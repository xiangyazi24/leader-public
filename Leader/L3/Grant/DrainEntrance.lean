import Leader.L3.Grant.DrainShared
import Leader.L3.Grant.DrainMarks
import Leader.L3.RenewalGrantStage

/-!
The source-ledger entrance state for the first Appendix D stage.
The physical field is the ORIGINAL canonical grantDrainStep, with the
actual request/scratch functions supplied by the caller. Grant labels
are GrantDrainLedgerLabel, not the frozen BANK labels.

It formalizes the adapted
bad-LIVE identity carrier, proves the two absorbing stopping clauses,
and instantiates the finite-family nominated-hit tail.
It does not assert the still-missing physical opposite-direction
noncrossing inequality or a first-hit cost bound.
-/

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared
open L3.RenewalReferenceClock

set_option autoImplicit false
set_option Elab.async false

/-- n immutable grant identities and n immutable initial paper-exact
non-leftmost LIVE identities. The source ledger is not in the
physical protocol state. -/
structure GrantDrainEntranceState (n : Nat) (Scratch : Type) where
  physical : GrantDrainState n Scratch
  grantLabels : Fin n → GrantDrainLedgerLabel n
  bulletHosts : Fin n → Option (Fin n)

/-- An initial bullet identity exists exactly where the paper's
corrected (D.2) BAD(ii) observer holds, including a preceding DUMMY
on the sector leader. -/
noncomputable def grantDrainEntranceBulletInitial
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch)
    (i : Fin n) : Option (Fin n) := by
  classical
  exact if SharedPaperNonleftmostLiveExact ring s.native i
    then some i else none

/-- Physical coordinates and both independent, bounded ghost families
at the adapted entrance cut. -/
noncomputable def grantDrainEntranceInitial
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch) :
    GrantDrainEntranceState n Scratch :=
  { physical := s
    grantLabels := grantDrainLedgerInitial ring s
    bulletHosts := grantDrainEntranceBulletInitial ring s }

/-- Only the OLD empty-follower responder can receive a moving
bad-LIVE identity on the source edge. -/
def GrantDrainEntranceBulletMove
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n) : Prop :=
  (s.native (ring.rightNeighbor e)).l = false ∧
  (s.native (ring.rightNeighbor e)).b = (0 : Fin 3) ∧
  SharedPaperNonleftmostLiveExact ring
    (grantDrainStep ring fresh update s e).native
    (ring.rightNeighbor e)

/-- No new initial bullet identity is ever allocated. A current
identity at the source moves clockwise or retires; an off-source
identity remains only if still physically paper-bad. -/
noncomputable def grantDrainEntranceBulletAdvance
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (old : Option (Fin n)) : Option (Fin n) := by
  classical
  exact
    match old with
    | none => none
    | some b =>
        if b = e then
          if GrantDrainEntranceBulletMove ring fresh update s e
          then some (ring.rightNeighbor e) else none
        else if SharedPaperNonleftmostLiveExact ring
            (grantDrainStep ring fresh update s e).native b
          then some b else none

/-- The same physical source step as the canonical model, with
source-ledger mark promotion and the proof-only bullet transport. -/
noncomputable def grantDrainEntranceNext
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (x : GrantDrainEntranceState n Scratch) (e : Fin n) :
    GrantDrainEntranceState n Scratch :=
  { physical := grantDrainStep ring fresh update x.physical e
    grantLabels := fun i =>
      grantDrainLedgerStep ring fresh update x.physical e (x.grantLabels i)
    bulletHosts := fun i =>
      grantDrainEntranceBulletAdvance ring fresh update
        x.physical e (x.bulletHosts i) }

/-- The type-level source-model square: we have not introduced a
surrogate physical transition. -/
theorem grantDrainEntranceNextCanonical
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (x : GrantDrainEntranceState n Scratch) (e : Fin n) :
    (grantDrainEntranceNext ring fresh update x e).physical =
      (grantDrainCanonicalModel ring hn fresh update).step x.physical e := by
  rfl

/-- Exactly the intended disjunction at zeta: no initial bad-LIVE
identity is still tracked, OR every surviving source grant label
has been marked. Neither clause demands grant extinction. -/
def GrantDrainEntranceDone
    {n : Nat} {Scratch : Type}
    (x : GrantDrainEntranceState n Scratch) : Prop :=
  (∀ j : Fin n, x.bulletHosts j = none) ∨
  (∀ i : Fin n, (x.grantLabels i).host ≠ none →
    (x.grantLabels i).mark ≠ .unmarked)

theorem grantDrainEntranceBulletAdvanceNone
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n) :
    grantDrainEntranceBulletAdvance ring fresh update s e none = none := by
  rfl

theorem grantDrainEntranceBulletAdvanceMove
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hMove : GrantDrainEntranceBulletMove ring fresh update s e) :
    grantDrainEntranceBulletAdvance ring fresh update s e (some e) =
      some (ring.rightNeighbor e) := by
  classical
  simp [grantDrainEntranceBulletAdvance, hMove]

theorem grantDrainEntranceBulletAdvanceStay
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e b : Fin n)
    (hb : b ≠ e)
    (hNew : SharedPaperNonleftmostLiveExact ring
      (grantDrainStep ring fresh update s e).native b) :
    grantDrainEntranceBulletAdvance ring fresh update s e (some b) =
      some b := by
  classical
  simp [grantDrainEntranceBulletAdvance, hb, hNew]

/-- A retired initial bullet cannot return, even after native
leader deletion or a canonical F0/F1/F2 birth. -/
theorem grantDrainEntranceBulletRetiredNext
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (x : GrantDrainEntranceState n Scratch) (e j : Fin n)
    (h : x.bulletHosts j = none) :
    (grantDrainEntranceNext ring fresh update x e).bulletHosts j =
      none := by
  change grantDrainEntranceBulletAdvance ring fresh update
    x.physical e (x.bulletHosts j) = none
  rw [h]
  exact grantDrainEntranceBulletAdvanceNone ring fresh update x.physical e

/-- An initial bad-LIVE identity never stutters at its nominated
outgoing edge: on that edge it moves one site right or retires. -/
theorem grantDrainEntranceBulletOutgoing
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (x : GrantDrainEntranceState n Scratch) (e j : Fin n)
    (h : x.bulletHosts j = some e) :
    (grantDrainEntranceNext ring fresh update x e).bulletHosts j =
        none ∨
    (grantDrainEntranceNext ring fresh update x e).bulletHosts j =
        some (ring.rightNeighbor e) := by
  classical
  by_cases hm : GrantDrainEntranceBulletMove ring fresh update x.physical e
  · right
    change grantDrainEntranceBulletAdvance ring fresh update
      x.physical e (x.bulletHosts j) = some (ring.rightNeighbor e)
    rw [h]
    exact grantDrainEntranceBulletAdvanceMove ring fresh update
      x.physical e hm
  · left
    change grantDrainEntranceBulletAdvance ring fresh update
      x.physical e (x.bulletHosts j) = none
    rw [h]
    simp [grantDrainEntranceBulletAdvance, hm]

/-- Every old hosted, marked grant label either retires or retains
a non-unmarked mark. This uses SOURCE mark monotonicity, not BANK's
mark-frozen family step. -/
theorem grantDrainEntranceAllGrantsMarkedNext
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (x : GrantDrainEntranceState n Scratch) (e : Fin n)
    (hMarked : ∀ i : Fin n, (x.grantLabels i).host ≠ none →
      (x.grantLabels i).mark ≠ .unmarked) :
    ∀ i : Fin n,
      ((grantDrainEntranceNext ring fresh update x e).grantLabels i).host ≠
        none →
      ((grantDrainEntranceNext ring fresh update x e).grantLabels i).mark ≠
        .unmarked := by
  intro i hNewHost
  change (grantDrainLedgerStep ring fresh update x.physical e
    (x.grantLabels i)).host ≠ none at hNewHost
  have hOldHost : (x.grantLabels i).host ≠ none := by
    intro hNone
    exact hNewHost (grantDrainLedgerStep_retired_absorbing
      ring fresh update x.physical e (x.grantLabels i) hNone)
  have hOldRank : 0 < grantDrainMarkRank (x.grantLabels i).mark := by
    cases hm : (x.grantLabels i).mark with
    | unmarked => exact False.elim ((hMarked i hOldHost) hm)
    | weak => simp [hm, grantDrainMarkRank]
    | strong => simp [hm, grantDrainMarkRank]
    | terminal => simp [hm, grantDrainMarkRank]
  have hRankNext := grantDrainLedgerStep_mark_monotone ring fresh update
    x.physical e (x.grantLabels i)
  have hPositive :
      0 < grantDrainMarkRank
        (grantDrainLedgerStep ring fresh update x.physical e
          (x.grantLabels i)).mark :=
    Nat.lt_of_lt_of_le hOldRank hRankNext
  intro hUnmarked
  change (grantDrainLedgerStep ring fresh update x.physical e
    (x.grantLabels i)).mark = .unmarked at hUnmarked
  rw [hUnmarked] at hPositive
  simp [grantDrainMarkRank] at hPositive

/-- Both target clauses are absorbing, without an independence
assumption, a stopping-time theorem, or a grant-quota premise. -/
theorem grantDrainEntranceDoneNext
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (x : GrantDrainEntranceState n Scratch) (e : Fin n)
    (hDone : GrantDrainEntranceDone x) :
    GrantDrainEntranceDone
      (grantDrainEntranceNext ring fresh update x e) := by
  rcases hDone with hNoBullet | hAllMarked
  · left
    intro j
    exact grantDrainEntranceBulletRetiredNext
      ring fresh update x e j (hNoBullet j)
  · right
    exact grantDrainEntranceAllGrantsMarkedNext
      ring fresh update x e hAllMarked

/-- The exact corrected BAD(ii) origin theorem also proves that
the PHYSICAL absence of all bad-LIVE is forward closed on PB. -/
theorem grantDrainEntrancePhysicalNoBadNext
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hPB : PPlus ring s.native)
    (hNone : ∀ b : Fin n,
      ¬ SharedPaperNonleftmostLiveExact ring s.native b) :
    ∀ b : Fin n,
      ¬ SharedPaperNonleftmostLiveExact ring
        (grantDrainStep ring fresh update s e).native b := by
  intro b hNew
  have hOrigin :=
    (sharedPaperCanonicalBadLiveStepOrigin ring hn fresh update)
      s e b hPB hNew
  rcases hOrigin with hMoved | hStayed
  · exact hNone e hMoved.2.1
  · exact hNone b hStayed.2

/-- Soundness and reverse coverage of ACTUAL paper-bad physical
sites, using only the finite initial host family. -/
def GrantDrainEntranceBulletFaithful
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (x : GrantDrainEntranceState n Scratch) : Prop :=
  (∀ (j b : Fin n),
    x.bulletHosts j = some b →
      SharedPaperNonleftmostLiveExact ring x.physical.native b) ∧
  (∀ b : Fin n,
    SharedPaperNonleftmostLiveExact ring x.physical.native b →
      ∃ j : Fin n, x.bulletHosts j = some b)

theorem grantDrainEntranceInitialFaithful
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch) :
    GrantDrainEntranceBulletFaithful ring
      (grantDrainEntranceInitial ring s) := by
  classical
  constructor
  · intro j b hHost
    change grantDrainEntranceBulletInitial ring s j = some b at hHost
    by_cases hj : SharedPaperNonleftmostLiveExact ring s.native j
    · have he : (some j : Option (Fin n)) = some b := by
        simpa [grantDrainEntranceBulletInitial, hj] using hHost
      have hSame : j = b := Option.some.inj he
      rw [← hSame]
      exact hj
    · have he : (none : Option (Fin n)) = some b := by
        simpa [grantDrainEntranceBulletInitial, hj] using hHost
      cases he
  · intro b hBad
    refine ⟨b, ?_⟩
    change grantDrainEntranceBulletInitial ring s b = some b
    change SharedPaperNonleftmostLiveExact ring s.native b at hBad
    simp [grantDrainEntranceBulletInitial, hBad]

/-- Forward soundness is by construction; reverse coverage is the
part which actually consumes BAD(ii) source geometry. -/
theorem grantDrainEntranceBulletSoundNext
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (x : GrantDrainEntranceState n Scratch) (e : Fin n) :
    ∀ (j b : Fin n),
      (grantDrainEntranceNext ring fresh update x e).bulletHosts j =
        some b →
      SharedPaperNonleftmostLiveExact ring
        (grantDrainEntranceNext ring fresh update x e).physical.native b := by
  classical
  intro j b hNext
  change grantDrainEntranceBulletAdvance ring fresh update
    x.physical e (x.bulletHosts j) = some b at hNext
  change SharedPaperNonleftmostLiveExact ring
    (grantDrainStep ring fresh update x.physical e).native b
  cases hOld : x.bulletHosts j with
  | none =>
      have hImpossible : (none : Option (Fin n)) = some b := by
        simpa [grantDrainEntranceBulletAdvance, hOld] using hNext
      cases hImpossible
  | some c =>
      by_cases hc : c = e
      · by_cases hMove :
            GrantDrainEntranceBulletMove ring fresh update x.physical e
        · have hEq : (some (ring.rightNeighbor e) : Option (Fin n)) =
              some b := by
            simpa [grantDrainEntranceBulletAdvance, hOld, hc, hMove]
              using hNext
          have hb : ring.rightNeighbor e = b := Option.some.inj hEq
          rw [← hb]
          exact hMove.2.2
        · have hImpossible : (none : Option (Fin n)) = some b := by
            simpa [grantDrainEntranceBulletAdvance, hOld, hc, hMove]
              using hNext
          cases hImpossible
      · by_cases hStay : SharedPaperNonleftmostLiveExact ring
            (grantDrainStep ring fresh update x.physical e).native c
        · have hEq : (some c : Option (Fin n)) = some b := by
            simpa [grantDrainEntranceBulletAdvance, hOld, hc, hStay]
              using hNext
          have hb : c = b := Option.some.inj hEq
          rw [← hb]
          exact hStay
        · have hImpossible : (none : Option (Fin n)) = some b := by
            simpa [grantDrainEntranceBulletAdvance, hOld, hc, hStay]
              using hNext
          cases hImpossible

/-- Every NEW paper-bad LIVE has an OLD tracked identity. Source
E/selector semantics enter only through sharedPaperCanonical...;
the ghost cannot grow new IDs. -/
theorem grantDrainEntranceBulletCoverNext
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (x : GrantDrainEntranceState n Scratch) (e : Fin n)
    (hPB : PPlus ring x.physical.native)
    (hCover : ∀ b : Fin n,
      SharedPaperNonleftmostLiveExact ring x.physical.native b →
        ∃ j : Fin n, x.bulletHosts j = some b) :
    ∀ b : Fin n,
      SharedPaperNonleftmostLiveExact ring
        (grantDrainEntranceNext ring fresh update x e).physical.native b →
      ∃ j : Fin n,
        (grantDrainEntranceNext ring fresh update x e).bulletHosts j =
          some b := by
  intro b hNew
  change SharedPaperNonleftmostLiveExact ring
    (grantDrainStep ring fresh update x.physical e).native b at hNew
  have hOrigin :=
    (sharedPaperCanonicalBadLiveStepOrigin ring hn fresh update)
      x.physical e b hPB hNew
  rcases hOrigin with hMove | hStay
  · obtain ⟨hEq, hOldBad, hFollower, hEmpty⟩ := hMove
    obtain ⟨j, hHost⟩ := hCover e hOldBad
    subst b
    refine ⟨j, ?_⟩
    change grantDrainEntranceBulletAdvance ring fresh update
      x.physical e (x.bulletHosts j) = some (ring.rightNeighbor e)
    rw [hHost]
    exact grantDrainEntranceBulletAdvanceMove ring fresh update
      x.physical e ⟨hFollower, hEmpty, hNew⟩
  · obtain ⟨hNe, hOldBad⟩ := hStay
    obtain ⟨j, hHost⟩ := hCover b hOldBad
    refine ⟨j, ?_⟩
    change grantDrainEntranceBulletAdvance ring fresh update
      x.physical e (x.bulletHosts j) = some b
    rw [hHost]
    exact grantDrainEntranceBulletAdvanceStay ring fresh update
      x.physical e b hNe hNew

theorem grantDrainEntranceFaithfulNext
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (x : GrantDrainEntranceState n Scratch) (e : Fin n)
    (hPB : PPlus ring x.physical.native)
    (hFaithful : GrantDrainEntranceBulletFaithful ring x) :
    GrantDrainEntranceBulletFaithful ring
      (grantDrainEntranceNext ring fresh update x e) := by
  constructor
  · exact grantDrainEntranceBulletSoundNext ring fresh update x e
  · exact grantDrainEntranceBulletCoverNext
      ring hn fresh update x e hPB hFaithful.2

/-- On faithful ghost states the first zeta branch has precisely the
claimed PHYSICAL meaning. -/
theorem grantDrainEntranceNoBulletIffNoBad
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (x : GrantDrainEntranceState n Scratch)
    (hFaithful : GrantDrainEntranceBulletFaithful ring x) :
    (∀ j : Fin n, x.bulletHosts j = none) ↔
      (∀ b : Fin n,
        ¬ SharedPaperNonleftmostLiveExact ring x.physical.native b) := by
  constructor
  · intro hNone b hBad
    obtain ⟨j, hHost⟩ := hFaithful.2 b hBad
    rw [hNone j] at hHost
    cases hHost
  · intro hNone j
    cases hHost : x.bulletHosts j with
    | none => rfl
    | some b =>
        exact False.elim (hNone b (hFaithful.1 j b hHost))

/-- Finite scheduler words carry the SAME canonical physical state
with the promoted source grant ledger and paper-exact bullet ghosts. -/
noncomputable def grantDrainEntranceRun
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (x : GrantDrainEntranceState n Scratch)
    (word : List (Fin n)) : GrantDrainEntranceState n Scratch :=
  word.foldl (grantDrainEntranceNext ring fresh update) x

/-- The zeta target is absorbing at every later finite word. -/
theorem grantDrainEntranceDoneRun
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    ∀ (word : List (Fin n))
      (x : GrantDrainEntranceState n Scratch),
      GrantDrainEntranceDone x →
      GrantDrainEntranceDone
        (grantDrainEntranceRun ring fresh update x word) := by
  intro word
  induction word with
  | nil =>
      intro x hDone
      exact hDone
  | cons e es ih =>
      intro x hDone
      change GrantDrainEntranceDone
        (grantDrainEntranceRun ring fresh update
          (grantDrainEntranceNext ring fresh update x e) es)
      exact ih (grantDrainEntranceNext ring fresh update x e)
        (grantDrainEntranceDoneNext ring fresh update x e hDone)

/-- Reverse ancestry holds along every finite word, and every
surviving ghost still denotes a physically bad-LIVE bullet. -/
theorem grantDrainEntranceFaithfulRun
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    ∀ (word : List (Fin n))
      (x : GrantDrainEntranceState n Scratch),
      PPlus ring x.physical.native →
      GrantDrainEntranceBulletFaithful ring x →
      GrantDrainEntranceBulletFaithful ring
        (grantDrainEntranceRun ring fresh update x word) := by
  intro word
  induction word with
  | nil =>
      intro x _ hFaithful
      exact hFaithful
  | cons e es ih =>
      intro x hPB hFaithful
      change GrantDrainEntranceBulletFaithful ring
        (grantDrainEntranceRun ring fresh update
          (grantDrainEntranceNext ring fresh update x e) es)
      have hPBNext :
          PPlus ring
            (grantDrainEntranceNext ring fresh update x e).physical.native :=
        grantDrainStep_preserves_PPlus
          (by omega : 3 ≤ n) ring fresh update x.physical e hPB
      exact ih (grantDrainEntranceNext ring fresh update x e) hPBNext
        (grantDrainEntranceFaithfulNext
          ring hn fresh update x e hPB hFaithful)

/-- At the adapted initial cut the finite-word reverse ancestry
is unconditional once the physical PB hypothesis is given. -/
theorem grantDrainEntranceInitialFaithfulRun
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (word : List (Fin n))
    (hPB : PPlus ring s.native) :
    GrantDrainEntranceBulletFaithful ring
      (grantDrainEntranceRun ring fresh update
        (grantDrainEntranceInitial ring s) word) := by
  exact grantDrainEntranceFaithfulRun ring hn fresh update word
    (grantDrainEntranceInitial ring s) hPB
    (grantDrainEntranceInitialFaithful ring s)

/-- The previsible outgoing edge of a tracked initial bullet.
Retired identities nominate their fixed immutable index. -/
def grantDrainEntranceBulletChosen
    {n : Nat} {Scratch : Type}
    (x : GrantDrainEntranceState n Scratch)
    (j : Fin n) : Fin n :=
  match x.bulletHosts j with
  | none => j
  | some b => b

theorem grantDrainEntranceBulletChosenAtHost
    {n : Nat} {Scratch : Type}
    (x : GrantDrainEntranceState n Scratch) (j b : Fin n)
    (hHost : x.bulletHosts j = some b) :
    grantDrainEntranceBulletChosen x j = b := by
  simp [grantDrainEntranceBulletChosen, hHost]

/-- The EXACT nominated-hit recursion for each immutable identity,
including after retirement. No stochastic independence is assumed. -/
noncomputable def grantDrainEntranceBulletHits
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (j : Fin n) :
    GrantDrainEntranceState n Scratch → List (Fin n) → Nat
  | _, [] => 0
  | x, e :: es =>
      (if e = grantDrainEntranceBulletChosen x j then 1 else 0) +
        grantDrainEntranceBulletHits ring fresh update j
          (grantDrainEntranceNext ring fresh update x e) es

/-- Finite-family nominated-hit tail, instantiated with
exactly n initial identities and the source-ghost next function.
This alone is NOT the D.2 bound on survival until the physical
noncrossing/quota implication has been proved. -/
theorem grantDrainEntranceFamilyLowerTail
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (x : GrantDrainEntranceState n Scratch)
    (T : Nat) (hn : 0 < n)
    (hT : 2 * n * n + n ≤ T) :
    L3.Prob.scheduleSum n T
      (fun w =>
        if (List.ofFn (fun j : Fin n =>
          decide (grantDrainEntranceBulletHits ring fresh update
            j x w < n))).any (fun z => z)
        then 1 else 0) * 2 ≤ n * n ^ T := by
  classical
  exact nominatedHits_family_lower_tail_half
    (grantDrainEntranceNext ring fresh update)
    (fun j z => grantDrainEntranceBulletChosen z j)
    (fun j z w => grantDrainEntranceBulletHits ring fresh update j z w)
    (by intro j z; rfl)
    (by intro j z e es; rfl)
    x T n hn hT

end L3.GrantDrainEntrance


/-!
Bridge for the opposite-direction argument.
This section proves the physical no-shared-site clause on the reachable
paper-exact bullet/source-ledger carrier, two retiring collision cases,
and exact post-HOLD/post-lock mark promotion. It does not assert the
remaining Y-to-X protected-prefix step or the global separation quota.

No supplementary axiom is introduced.
-/

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared
open L3.RenewalReferenceClock

set_option autoImplicit false
set_option Elab.async false

/-- The cyclic offset is below n. -/
theorem grantDrainEntranceArcOffsetLt
    {n : Nat} (ring : DirectedRing n) (p g : Fin n) :
    PPL.cyclicOffset ring p g < n := by
  unfold PPL.cyclicOffset
  exact Nat.mod_lt _ ring.hn

/-- A first-hit scan has no successes before its selected offset.
This is generic core recursion, not a grant-drain hypothesis. -/
theorem grantDrainEntranceScanSomeInfo
    {n : Nat} (site : Nat → Fin n) (hit : Fin n → Bool) :
    ∀ fuel start d,
      PPL.scanDistance site hit fuel start = some d →
      start ≤ d ∧ d < start + fuel ∧ hit (site d) = true ∧
      (∀ k : Nat, start ≤ k → k < d → hit (site k) = false) := by
  intro fuel
  induction fuel with
  | zero =>
      intro start d h
      simp [PPL.scanDistance] at h
  | succ fuel ih =>
      intro start d h
      cases hh : hit (site start) with
      | true =>
          have he : some start = some d := by
            simpa [PPL.scanDistance, hh] using h
          have hd : start = d := Option.some.inj he
          subst d
          refine ⟨Nat.le_refl _, by omega, hh, ?_⟩
          intro k hk hlt
          omega
      | false =>
          have ht :
              PPL.scanDistance site hit fuel (start + 1) = some d := by
            simpa [PPL.scanDistance, hh] using h
          rcases ih (start + 1) d ht with
            ⟨hlo, hhi, hval, hbefore⟩
          refine ⟨by omega, by omega, hval, ?_⟩
          intro k hk hkd
          by_cases heq : k = start
          · rw [heq]
            exact hh
          · exact hbefore k (by omega) hkd

/-- A failed exhaustive first-hit scan missed every inspected site. -/
private theorem grantDrainEntranceScanNoneInfo
    {n : Nat} (site : Nat → Fin n) (hit : Fin n → Bool) :
    ∀ fuel start,
      PPL.scanDistance site hit fuel start = none →
      ∀ k : Nat, start ≤ k → k < start + fuel →
        hit (site k) = false := by
  intro fuel
  induction fuel with
  | zero =>
      intro start h k hk hlt
      omega
  | succ fuel ih =>
      intro start h k hk hlt
      cases hh : hit (site start) with
      | true =>
          have hc : some start = (none : Option Nat) := by
            simpa [PPL.scanDistance, hh] using h
          cases hc
      | false =>
          have ht :
              PPL.scanDistance site hit fuel (start + 1) = none := by
            simpa [PPL.scanDistance, hh] using h
          by_cases heq : k = start
          · rw [heq]
            exact hh
          · exact ih (start + 1) ht k (by omega) (by omega)

/-- Recover the actual leader p from the clockwise offset from p
to a follower b. This is the only circular coordinate translation
needed in the failed-scan branch. -/
theorem grantDrainEntranceLeftOffset
    {n : Nat} (ring : DirectedRing n) (p b : Fin n) :
    PPL.shiftLeft ring b (PPL.cyclicOffset ring p b) = p := by
  have hshift := grantDrainMarksArcShiftLeftRight ring p
    (PPL.cyclicOffset ring p b) (PPL.cyclicOffset ring p b)
    (Nat.le_refl _) (grantDrainEntranceArcOffsetLt ring p b)
  rw [grantDrainMarksArcShiftRightOffset ring p b] at hshift
  have hzero : PPL.shiftRight ring p 0 = p := by
    apply Fin.ext
    change (p.val + 0) % n = p.val
    simp [Nat.mod_eq_of_lt p.isLt]
  simpa only [Nat.sub_self, hzero] using hshift

/-- A PB live follower has the exact Boolean shielded zero trail
tested by the source ledger at its own site. The first-hit scan
starts at zero, whereas grantDrainLeftLeaderDistance starts at one;
the follower hypothesis removes this discrepancy. -/
theorem grantDrainEntranceLiveStrongLock
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch)
    (b : Fin n)
    (hPB : PPlus ring s.native)
    (hLive : LiveBullet s.native b)
    (hFollower : (s.native b).l = false) :
    grantDrainLedgerStrongLock ring s b = true := by
  have hPeace : PPL.PeacefulCore ring
      (fun i : Fin n => (s.native i).l)
      (fun i : Fin n => (s.native i).sh)
      (fun i : Fin n => (s.native i).sg) b :=
    hPB.2 b hLive
  unfold PPL.PeacefulCore at hPeace
  cases hd : PPL.dLLBy ring (fun i : Fin n => (s.native i).l) b with
  | none =>
      have hMiss : ∀ k : Nat, 0 ≤ k → k < n →
          (s.native (PPL.shiftLeft ring b k)).l = false := by
        change PPL.scanDistance
          (fun k : Nat => PPL.shiftLeft ring b k)
          (fun i : Fin n => (s.native i).l) n 0 = none at hd
        exact fun k h0 hk => grantDrainEntranceScanNoneInfo
          (fun k : Nat => PPL.shiftLeft ring b k)
          (fun i : Fin n => (s.native i).l) n 0 hd k h0 (by omega)
      obtain ⟨p, hp⟩ := hPB.1
      have hAt := hMiss (PPL.cyclicOffset ring p b)
        (Nat.zero_le _) (grantDrainEntranceArcOffsetLt ring p b)
      rw [grantDrainEntranceLeftOffset ring p b, hp] at hAt
      cases hAt
  | some d =>
      rw [hd] at hPeace
      have hScan :
          PPL.scanDistance
            (fun k : Nat => PPL.shiftLeft ring b k)
            (fun i : Fin n => (s.native i).l) n 0 = some d := by
        exact hd
      rcases grantDrainEntranceScanSomeInfo
        (fun k : Nat => PPL.shiftLeft ring b k)
        (fun i : Fin n => (s.native i).l) n 0 d hScan with
        ⟨hStart, hBound, hSource, hBefore⟩
      have hPositive : 1 ≤ d := by
        by_cases hz : d = 0
        · have hAtB : (s.native b).l = true := by
            rw [hz] at hSource
            simpa [PPL.shiftLeft, Nat.mod_eq_of_lt b.isLt]
              using hSource
          rw [hFollower] at hAtB
          cases hAtB
        · omega
      have hDistance :
          grantDrainLeftLeaderDistance ring s.native b = d :=
        grantDrainMarksScanFirstSource ring s.native b d
          hPositive (by omega) hSource
          (fun k hk hkd => hBefore k (by omega) hkd)
      have hZeroAll :
          (List.range d).all (fun k =>
            !(s.native (PPL.shiftLeft ring b (k + 1))).sg) = true := by
        apply List.all_eq_true.mpr
        intro k hk
        have hklt : k < d := List.mem_range.mp hk
        have hzero :
            (s.native (PPL.shiftLeft ring b (k + 1))).sg =
              false := hPeace.2 ⟨k + 1, by omega⟩
        simp [hzero]
      simp [grantDrainLedgerStrongLock, grantDrainLedgerCorridor,
        hDistance, hSource, hZeroAll, hPeace.1]

/-- Right-hand marks are retained by the ordered maximum. -/
private theorem grantDrainEntranceMarkJoinRight
    (a b : GrantDrainMark) :
    grantDrainMarkRank b ≤
      grantDrainMarkRank (grantDrainMarkJoin a b) := by
  unfold grantDrainMarkJoin
  split <;> omega

/-- All three persistent joins preserve a freshly observed mark. -/
private theorem grantDrainEntranceMarkJoinsRight
    (a b c d : GrantDrainMark) :
    grantDrainMarkRank d ≤
      grantDrainMarkRank
        (grantDrainMarkJoin a
          (grantDrainMarkJoin b (grantDrainMarkJoin c d))) := by
  calc
    grantDrainMarkRank d ≤
        grantDrainMarkRank (grantDrainMarkJoin c d) :=
      grantDrainEntranceMarkJoinRight c d
    _ ≤ grantDrainMarkRank
          (grantDrainMarkJoin b (grantDrainMarkJoin c d)) :=
      grantDrainEntranceMarkJoinRight b _
    _ ≤ grantDrainMarkRank
          (grantDrainMarkJoin a
            (grantDrainMarkJoin b (grantDrainMarkJoin c d))) :=
      grantDrainEntranceMarkJoinRight a _

private theorem grantDrainEntranceMarkedRankPositive
    (m : GrantDrainMark) (hm : m ≠ .unmarked) :
    0 < grantDrainMarkRank m := by
  cases m <;> simp [grantDrainMarkRank] at *

/-- The dynamic source mark observes the CURRENT physical host,
even after FIRE/coalescence/HOLD. A frozen BANK ledger does not
enjoy this theorem. -/
theorem grantDrainEntranceMarkNextPostRank
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
  exact grantDrainEntranceMarkJoinsRight _ _ _ _

/-- Unlike a purely frozen source-agnostic ghost, the new label
always records a non-unmarked observation at its NEW host. -/
theorem grantDrainEntrancePostObservedMarked
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (x : GrantDrainEntranceState n Scratch)
    (e i g : Fin n)
    (hHost :
      ((grantDrainEntranceNext ring fresh update x e).grantLabels i).host =
        some g)
    (hObserved :
      grantDrainLedgerObservedMark ring
        (grantDrainEntranceNext ring fresh update x e).physical
        (some g) ≠ .unmarked) :
    ((grantDrainEntranceNext ring fresh update x e).grantLabels i).mark ≠
      .unmarked := by
  have hHostRaw :
      grantDrainLedgerHost ring fresh x.physical e
        (x.grantLabels i).host = some g := hHost
  have hRank := grantDrainEntranceMarkNextPostRank
    ring fresh update x.physical e (x.grantLabels i)
  rw [hHostRaw] at hRank
  have hPositive :
      0 < grantDrainMarkRank
        (grantDrainLedgerObservedMark ring
          (grantDrainStep ring fresh update x.physical e) (some g)) :=
    grantDrainEntranceMarkedRankPositive _
      (by exact hObserved)
  have hNewPositive := Nat.lt_of_lt_of_le hPositive hRank
  intro hUnmarked
  change (grantDrainLedgerStep ring fresh update x.physical e
    (x.grantLabels i)).mark = .unmarked at hUnmarked
  rw [hUnmarked] at hNewPositive
  simp [grantDrainMarkRank] at hNewPositive

/-- The actual source-ledger post-HOLD transition makes a surviving
held label terminal (including the incoming Y responder case). -/
theorem grantDrainEntrancePostHeldTerminal
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (x : GrantDrainEntranceState n Scratch)
    (e i g : Fin n)
    (hHost :
      ((grantDrainEntranceNext ring fresh update x e).grantLabels i).host =
        some g)
    (hRequest :
      (grantDrainEntranceNext ring fresh update x e).physical.request g =
        true)
    (hGrant :
      (grantDrainEntranceNext ring fresh update x e).physical.grant g =
        true) :
    ((grantDrainEntranceNext ring fresh update x e).grantLabels i).mark =
      .terminal := by
  have hHostRaw :
      grantDrainLedgerHost ring fresh x.physical e
        (x.grantLabels i).host = some g := hHost
  change grantDrainLedgerMarkNext ring fresh update
    x.physical e (x.grantLabels i) = .terminal
  exact grantDrainLedgerMarkNext_of_post_held
    ring fresh update x.physical e g (x.grantLabels i)
    hHostRaw hRequest hGrant

/-- The source ledger reflects strong corridor geometry after the
edge even if the old label was unmarked. -/
theorem grantDrainEntrancePostStrongMarked
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (x : GrantDrainEntranceState n Scratch)
    (e i g : Fin n)
    (hHost :
      ((grantDrainEntranceNext ring fresh update x e).grantLabels i).host =
        some g)
    (hFollower :
      ((grantDrainEntranceNext ring fresh update x e).physical.native g).l =
        false)
    (hLock :
      grantDrainLedgerStrongLock ring
        (grantDrainEntranceNext ring fresh update x e).physical g = true) :
    ((grantDrainEntranceNext ring fresh update x e).grantLabels i).mark ≠
      .unmarked := by
  apply grantDrainEntrancePostObservedMarked
    ring fresh update x e i g hHost
  by_cases hHeld :
      ((grantDrainEntranceNext ring fresh update x e).physical.request g &&
        (grantDrainEntranceNext ring fresh update x e).physical.grant g) =
        true
  · simp [grantDrainLedgerObservedMark, hHeld]
  · simp [grantDrainLedgerObservedMark, hHeld, hFollower, hLock]

/-- A source state has coherent CURRENT grant marks when any mark
read at a live label's actual host has already been recorded. -/
def GrantDrainEntranceMarkSound
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (x : GrantDrainEntranceState n Scratch) : Prop :=
  ∀ i g : Fin n,
    (x.grantLabels i).host = some g →
    grantDrainLedgerObservedMark ring x.physical (some g) ≠ .unmarked →
    (x.grantLabels i).mark ≠ .unmarked

theorem grantDrainEntranceInitialMarkSound
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch) :
    GrantDrainEntranceMarkSound ring
      (grantDrainEntranceInitial ring s) := by
  intro i g hHost hObserved
  change (grantDrainLedgerInitial ring s i).host = some g at hHost
  change (grantDrainLedgerInitial ring s i).mark ≠ .unmarked
  cases hg : s.grant i with
  | false =>
      simp [grantDrainLedgerInitial, hg] at hHost
  | true =>
      have he : (some i : Option (Fin n)) = some g := by
        simpa [grantDrainLedgerInitial, hg] using hHost
      have hi : i = g := Option.some.inj he
      subst g
      change ¬ grantDrainLedgerObservedMark ring s (some i) =
        GrantDrainMark.unmarked at hObserved
      simpa [grantDrainLedgerInitial, hg] using hObserved

/-- Because post-step observation is joined directly into the
source mark, CURRENT mark soundness is all-edge closed. -/
theorem grantDrainEntranceMarkSoundNext
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (x : GrantDrainEntranceState n Scratch) (e : Fin n) :
    GrantDrainEntranceMarkSound ring
      (grantDrainEntranceNext ring fresh update x e) := by
  intro i g hHost hObserved
  exact grantDrainEntrancePostObservedMarked
    ring fresh update x e i g hHost hObserved

theorem grantDrainEntranceMarkSoundRun
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    ∀ (word : List (Fin n)) (x : GrantDrainEntranceState n Scratch),
      GrantDrainEntranceMarkSound ring x →
      GrantDrainEntranceMarkSound ring
        (grantDrainEntranceRun ring fresh update x word) := by
  intro word
  induction word with
  | nil =>
      intro x hSound
      exact hSound
  | cons e es ih =>
      intro x hSound
      change GrantDrainEntranceMarkSound ring
        (grantDrainEntranceRun ring fresh update
          (grantDrainEntranceNext ring fresh update x e) es)
      exact ih (grantDrainEntranceNext ring fresh update x e)
        (grantDrainEntranceMarkSoundNext ring fresh update x e)

/-- The one-step physical PB closure, iterated on the actual source
state for later no-shared-site uses. -/
theorem grantDrainEntrancePBRun
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    ∀ (word : List (Fin n)) (x : GrantDrainEntranceState n Scratch),
      PPlus ring x.physical.native →
      PPlus ring
        (grantDrainEntranceRun ring fresh update x word).physical.native := by
  intro word
  induction word with
  | nil =>
      intro x hPB
      exact hPB
  | cons e es ih =>
      intro x hPB
      change PPlus ring
        (grantDrainEntranceRun ring fresh update
          (grantDrainEntranceNext ring fresh update x e) es).physical.native
      exact ih (grantDrainEntranceNext ring fresh update x e)
        (grantDrainStep_preserves_PPlus (by omega : 3 ≤ n)
          ring fresh update x.physical e hPB)

/-- Paper (a), a formal no-shared-site fact: while PB holds,
a physically faithful non-leftmost initial LIVE cannot occupy the
same site as a still-unmarked source-grant label. -/
theorem grantDrainEntranceNoSharedSite
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (x : GrantDrainEntranceState n Scratch)
    (hPB : PPlus ring x.physical.native)
    (hBullet : GrantDrainEntranceBulletFaithful ring x)
    (hMark : GrantDrainEntranceMarkSound ring x)
    (j i b : Fin n)
    (hBulletHost : x.bulletHosts j = some b)
    (hGrantHost : (x.grantLabels i).host = some b)
    (hUnmarked : (x.grantLabels i).mark = .unmarked) : False := by
  have hBad : SharedPaperNonleftmostLiveExact ring
      x.physical.native b := hBullet.1 j b hBulletHost
  have hLock :
      grantDrainLedgerStrongLock ring x.physical b = true :=
    grantDrainEntranceLiveStrongLock ring x.physical b
      hPB hBad.1 hBad.2.1
  have hObserved :
      grantDrainLedgerObservedMark ring x.physical (some b) ≠
        .unmarked := by
    by_cases hHeld :
        (x.physical.request b && x.physical.grant b) = true
    · simp [grantDrainLedgerObservedMark, hHeld]
    · simp [grantDrainLedgerObservedMark, hHeld, hBad.2.1, hLock]
  exact (hMark i b hGrantHost hObserved) hUnmarked

/-- Hence the two surviving identities have strictly positive and
strictly sub-cyclic clockwise separation, on any faithful PB state. -/
theorem grantDrainEntranceSeparationRange
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (x : GrantDrainEntranceState n Scratch)
    (hPB : PPlus ring x.physical.native)
    (hBullet : GrantDrainEntranceBulletFaithful ring x)
    (hMark : GrantDrainEntranceMarkSound ring x)
    (j i b g : Fin n)
    (hBulletHost : x.bulletHosts j = some b)
    (hGrantHost : (x.grantLabels i).host = some g)
    (hUnmarked : (x.grantLabels i).mark = .unmarked) :
    0 < PPL.cyclicOffset ring b g ∧
      PPL.cyclicOffset ring b g < n := by
  have hDifferent : b ≠ g := by
    intro he
    subst g
    exact grantDrainEntranceNoSharedSite ring x
      hPB hBullet hMark j i b hBulletHost hGrantHost hUnmarked
  have hPositive : 0 < PPL.cyclicOffset ring b g := by
    by_cases hz : PPL.cyclicOffset ring b g = 0
    · have hs : g = b :=
        grantDrainMarksSourceAtOffsetZero ring b g hz
      exact False.elim (hDifferent hs.symm)
    · omega
  exact ⟨hPositive, grantDrainEntranceArcOffsetLt ring b g⟩

/-- Paper (a) follows along every actual reachable source word from
any adapted PB cut, with no ghost assumptions added at the entrance. -/
theorem grantDrainEntranceInitialNoSharedRun
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (word : List (Fin n))
    (hPB : PPlus ring s.native)
    (j i b : Fin n)
    (hBulletHost :
      (grantDrainEntranceRun ring fresh update
        (grantDrainEntranceInitial ring s) word).bulletHosts j = some b)
    (hGrantHost :
      ((grantDrainEntranceRun ring fresh update
        (grantDrainEntranceInitial ring s) word).grantLabels i).host =
          some b)
    (hUnmarked :
      ((grantDrainEntranceRun ring fresh update
        (grantDrainEntranceInitial ring s) word).grantLabels i).mark =
          .unmarked) : False := by
  apply grantDrainEntranceNoSharedSite ring
    (grantDrainEntranceRun ring fresh update
      (grantDrainEntranceInitial ring s) word)
  · exact grantDrainEntrancePBRun ring hn fresh update word
      (grantDrainEntranceInitial ring s) hPB
  · exact grantDrainEntranceInitialFaithfulRun
      ring hn fresh update s word hPB
  · exact grantDrainEntranceMarkSoundRun ring fresh update word
      (grantDrainEntranceInitial ring s)
      (grantDrainEntranceInitialMarkSound ring s)
  · exact hBulletHost
  · exact hGrantHost
  · exact hUnmarked

/-- Paper (b), branch y leader: the guarded source ghost cannot
move a LIVE into a leader responder. It therefore retires. -/
theorem grantDrainEntranceSwapLeaderRetires
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (x : GrantDrainEntranceState n Scratch) (e j : Fin n)
    (hBullet : x.bulletHosts j = some e)
    (hLeader :
      (x.physical.native (ring.rightNeighbor e)).l = true) :
    (grantDrainEntranceNext ring fresh update x e).bulletHosts j =
      none := by
  have hMoveFalse :
      ¬ GrantDrainEntranceBulletMove ring fresh update x.physical e := by
    intro hMove
    have h1 := hMove.1
    rw [hLeader] at h1
    cases h1
  change grantDrainEntranceBulletAdvance ring fresh update
    x.physical e (x.bulletHosts j) = none
  rw [hBullet]
  simp [grantDrainEntranceBulletAdvance, hMoveFalse]

/-- Paper (b), branch y has any resident bullet (dummy or LIVE):
the moving initial LIVE cannot be inherited by that resident. -/
theorem grantDrainEntranceSwapResidentRetires
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (x : GrantDrainEntranceState n Scratch) (e j : Fin n)
    (hBullet : x.bulletHosts j = some e)
    (hResident :
      (x.physical.native (ring.rightNeighbor e)).b ≠ (0 : Fin 3)) :
    (grantDrainEntranceNext ring fresh update x e).bulletHosts j =
      none := by
  have hMoveFalse :
      ¬ GrantDrainEntranceBulletMove ring fresh update x.physical e := by
    intro hMove
    exact hResident hMove.2.1
  change grantDrainEntranceBulletAdvance ring fresh update
    x.physical e (x.bulletHosts j) = none
  rw [hBullet]
  simp [grantDrainEntranceBulletAdvance, hMoveFalse]

/-- Partial swap conclusion: if the moving identity survives and
its partner grant remains at the responder, no *unmarked* shared
successor is possible. The separate Y-to-X case still requires the
shielded-prefix preservation argument. -/
theorem grantDrainEntranceSwapResponderMarkedOrRetired
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (x : GrantDrainEntranceState n Scratch) (e j i : Fin n)
    (hPB : PPlus ring x.physical.native)
    (hFaithful : GrantDrainEntranceBulletFaithful ring x)
    (hBullet : x.bulletHosts j = some e)
    (hGrant : (x.grantLabels i).host = some (ring.rightNeighbor e))
    (hNewGrant :
      ((grantDrainEntranceNext ring fresh update x e).grantLabels i).host =
        some (ring.rightNeighbor e))
    (hNewBullet :
      (grantDrainEntranceNext ring fresh update x e).bulletHosts j =
        some (ring.rightNeighbor e)) :
    ((grantDrainEntranceNext ring fresh update x e).grantLabels i).mark ≠
      .unmarked := by
  intro hUnmarked
  exact grantDrainEntranceNoSharedSite ring
    (grantDrainEntranceNext ring fresh update x e)
    (grantDrainStep_preserves_PPlus (by omega : 3 ≤ n)
      ring fresh update x.physical e hPB)
    (grantDrainEntranceFaithfulNext
      ring hn fresh update x e hPB hFaithful)
    (grantDrainEntranceMarkSoundNext ring fresh update x e)
    j i (ring.rightNeighbor e) hNewBullet hNewGrant hUnmarked

end L3.GrantDrainEntrance



/-!
The exact selected-edge Y-to-X contact, without modifying
the source-ledger prefix. The decisive proof can be factored
through the NEW peaceful live responder: its shielded zero trail
strictly contains the follower initiator's strong-lock corridor.
When a Y grant can actually move to X, the literal token-owner
source sink excludes a final native leader at X.
-/

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared
open L3.RenewalReferenceClock

set_option autoImplicit false
set_option Elab.async false

/-- At a peaceful live responder y=x+1, a follower x has the same
nearest protected source and a strictly shorter zero-signal arc.
Thus a grant newly arriving at x is strongly locked, even when
its OWN old label was completely unmarked. -/
theorem grantDrainEntranceAdjacentLiveLocksPredecessor
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hPB : PPlus ring s.native)
    (hLive : LiveBullet s.native (ring.rightNeighbor e))
    (hYFollower : (s.native (ring.rightNeighbor e)).l = false)
    (hXFollower : (s.native e).l = false) :
    grantDrainLedgerStrongLock ring s e = true := by
  have hYLock :=
    grantDrainEntranceLiveStrongLock ring s
      (ring.rightNeighbor e) hPB hLive hYFollower
  obtain ⟨p, hNearest, hZero, hShield⟩ :=
    grantDrainMarksStrongLockToOffsetArc_proved
      ring s (ring.rightNeighbor e) hPB hYFollower hYLock
  have hPositive : 0 < PPL.cyclicOffset ring p e := by
    by_cases hz : PPL.cyclicOffset ring p e = 0
    · have he : e = p := grantDrainMarksSourceAtOffsetZero ring p e hz
      have hFalse := hXFollower
      rw [he, hNearest.2.1] at hFalse
      cases hFalse
    · omega
  have hNextBound : PPL.cyclicOffset ring p e + 1 < n := by
    have hBound := grantDrainEntranceArcOffsetLt ring p e
    by_cases hz : PPL.cyclicOffset ring p e + 1 = n
    · have hWrap : ring.rightNeighbor e = p := by
        calc
          ring.rightNeighbor e =
              PPL.shiftRight ring p
                (PPL.cyclicOffset ring p e + 1) :=
            grantDrainMarksNeighborOfOffset ring p e
          _ = PPL.shiftRight ring p n := by rw [hz]
          _ = p := grantDrainMarksFullRotation ring p
      have hFalse := hYFollower
      rw [hWrap, hNearest.2.1] at hFalse
      cases hFalse
    · omega
  have hOffset :
      PPL.cyclicOffset ring p (ring.rightNeighbor e) =
        PPL.cyclicOffset ring p e + 1 :=
    grantDrainMarksNeighborOffsetAdvance ring p e hNextBound
  have hNearestX : GrantDrainMarksNearestArc ring s.native p e := by
    refine ⟨hPositive, hNearest.2.1, ?_⟩
    intro k hkPos hkBound
    exact hNearest.2.2 k hkPos (by omega)
  have hZeroX : GrantDrainMarksZeroOffsetArc ring s.native p e := by
    intro k hk
    exact hZero k (by rw [hOffset]; omega)
  exact grantDrainMarksOffsetArcStrongLock
    ring s p e hNearestX hZeroX hShield

/-- This is a literal source-identity transport fact: an OLD
responder host can move to the initiator only via
grantDrainLedgerYSource = some false, hence the actual token row
has a NEW grant at its source. -/
theorem grantDrainEntranceResponderMovedRow
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hOld : label.host = some (ring.rightNeighbor e))
    (hNew :
      (grantDrainLedgerStep ring fresh update s e label).host = some e) :
    (grantDrainLedgerRow ring fresh s e).1.grant = true := by
  have hDistinct : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring hn e
  have hTransport :
      grantDrainLedgerHost ring fresh s e
        (some (ring.rightNeighbor e)) = some e := by
    change grantDrainLedgerHost ring fresh s e label.host = some e at hNew
    rw [hOld] at hNew
    exact hNew
  cases hY : grantDrainLedgerYSource
      (s.request (ring.rightNeighbor e))
      (s.grant (ring.rightNeighbor e))
      (grantDrainNativeNext ring s e e).l
      (grantDrainNativeNext ring s e (ring.rightNeighbor e)).l
      (grantDrainSelect ring s e)
      (grantDrainLedgerRow ring fresh s e) with
  | none =>
      have hImpossible : (none : Option (Fin n)) = some e := by
        simpa [grantDrainLedgerHost, hDistinct, hY] using hTransport
      cases hImpossible
  | some stays =>
      cases stays with
      | true =>
          have hImpossible :
              (some (ring.rightNeighbor e) : Option (Fin n)) =
                some e := by
            simpa [grantDrainLedgerHost, hDistinct, hY] using hTransport
          exact False.elim
            (hDistinct (Option.some.inj hImpossible))
      | false =>
          exact (grantDrainLedgerYSource_move_sound
            (s.request (ring.rightNeighbor e))
            (s.grant (ring.rightNeighbor e))
            (grantDrainNativeNext ring s e e).l
            (grantDrainNativeNext ring s e (ring.rightNeighbor e)).l
            (grantDrainSelect ring s e)
            (grantDrainLedgerRow ring fresh s e) hY).1

/-- If the OLD Y label actually moves to X, the final X cannot be
a leader: the concrete T1/source-sink token row would force its
grant bit to false. This excludes every FIRE selector producing a
leader at X, without hypothesizing no-FIRE prematurely. -/
theorem grantDrainEntranceResponderMoveSourceFollower
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hOld : label.host = some (ring.rightNeighbor e))
    (hNew :
      (grantDrainLedgerStep ring fresh update s e label).host = some e) :
    ((grantDrainStep ring fresh update s e).native e).l = false := by
  have hGrantX := grantDrainEntranceResponderMovedRow
    ring hn fresh update s e label hOld hNew
  change (grantDrainNativeNext ring s e e).l = false
  cases hFinal : (grantDrainNativeNext ring s e e).l with
  | false => rfl
  | true =>
      have hSink := bankGrantTokenRow_sourceLeaderSink
        (s.request e) (s.grant e)
        (s.request (ring.rightNeighbor e))
        (s.grant (ring.rightNeighbor e))
        (grantDrainNativeNext ring s e (ring.rightNeighbor e)).l
        (fresh s e) (grantDrainSelect ring s e)
      have hGrantFalse :
          (grantDrainLedgerRow ring fresh s e).1.grant = false := by
        unfold grantDrainLedgerRow
        rw [hFinal]
        exact hSink
      rw [hGrantFalse] at hGrantX
      cases hGrantX

/-- A source-ledger GRANT identity initially at Y can only retire,
stay at Y (HOLD), or move one counterclockwise edge to X. -/
theorem grantDrainEntranceResponderHostCases
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hOld : label.host = some (ring.rightNeighbor e)) :
    (grantDrainLedgerStep ring fresh update s e label).host = none ∨
    (grantDrainLedgerStep ring fresh update s e label).host =
      some (ring.rightNeighbor e) ∨
    (grantDrainLedgerStep ring fresh update s e label).host =
      some e := by
  have hDistinct : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring hn e
  cases hY : grantDrainLedgerYSource
      (s.request (ring.rightNeighbor e))
      (s.grant (ring.rightNeighbor e))
      (grantDrainNativeNext ring s e e).l
      (grantDrainNativeNext ring s e (ring.rightNeighbor e)).l
      (grantDrainSelect ring s e)
      (grantDrainLedgerRow ring fresh s e) with
  | none =>
      left
      simpa [grantDrainLedgerStep, grantDrainLedgerHost,
        hOld, hDistinct, hY]
  | some stays =>
      cases stays with
      | true =>
          right
          left
          simpa [grantDrainLedgerStep, grantDrainLedgerHost,
            hOld, hDistinct, hY]
      | false =>
          right
          right
          simpa [grantDrainLedgerStep, grantDrainLedgerHost,
            hOld, hDistinct, hY]

/-- The previously missing Y-to-X half of the paper's contact case.
If a tracked non-leftmost LIVE really arrives at Y while the OLD
responder label survives at X, post-PB provides the NEW live bullet's
protected trail, and the token row proves X is a follower. The
predecessor-arc lemma now gives an ACTUAL physical strong lock at X,
which is immediately recorded by the source ledger. -/
theorem grantDrainEntranceSwapMovedGrantMarked
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (x : GrantDrainEntranceState n Scratch)
    (e j i : Fin n)
    (hPB : PPlus ring x.physical.native)
    (hOldGrant :
      (x.grantLabels i).host = some (ring.rightNeighbor e))
    (hNewBullet :
      (grantDrainEntranceNext ring fresh update x e).bulletHosts j =
        some (ring.rightNeighbor e))
    (hNewGrant :
      ((grantDrainEntranceNext ring fresh update x e).grantLabels i).host =
        some e) :
    ((grantDrainEntranceNext ring fresh update x e).grantLabels i).mark ≠
      .unmarked := by
  have hNewBad := grantDrainEntranceBulletSoundNext
    ring fresh update x e j (ring.rightNeighbor e) hNewBullet
  have hNewPB : PPlus ring
      (grantDrainEntranceNext ring fresh update x e).physical.native :=
    grantDrainStep_preserves_PPlus (by omega : 3 ≤ n)
      ring fresh update x.physical e hPB
  have hNewXFollower :
      ((grantDrainEntranceNext ring fresh update x e).physical.native e).l =
        false :=
    grantDrainEntranceResponderMoveSourceFollower
      ring (by omega : 2 ≤ n) fresh update
      x.physical e (x.grantLabels i) hOldGrant hNewGrant
  have hXLock : grantDrainLedgerStrongLock ring
      (grantDrainEntranceNext ring fresh update x e).physical e = true :=
    grantDrainEntranceAdjacentLiveLocksPredecessor
      ring (grantDrainEntranceNext ring fresh update x e).physical e
      hNewPB hNewBad.1 hNewBad.2.1 hNewXFollower
  exact grantDrainEntrancePostStrongMarked ring fresh update x
    e i e hNewGrant hNewXFollower hXLock

/-- The HOLD / resident-Y branch is also marked: since Y is a
NEW peaceful LIVE follower, its own current shielded zero trail
produces a source strong lock (and a held request would additionally
make the mark terminal). -/
theorem grantDrainEntranceSwapHeldGrantMarked
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (x : GrantDrainEntranceState n Scratch)
    (e j i : Fin n)
    (hPB : PPlus ring x.physical.native)
    (hNewBullet :
      (grantDrainEntranceNext ring fresh update x e).bulletHosts j =
        some (ring.rightNeighbor e))
    (hNewGrant :
      ((grantDrainEntranceNext ring fresh update x e).grantLabels i).host =
        some (ring.rightNeighbor e)) :
    ((grantDrainEntranceNext ring fresh update x e).grantLabels i).mark ≠
      .unmarked := by
  have hNewBad := grantDrainEntranceBulletSoundNext
    ring fresh update x e j (ring.rightNeighbor e) hNewBullet
  have hNewPB : PPlus ring
      (grantDrainEntranceNext ring fresh update x e).physical.native :=
    grantDrainStep_preserves_PPlus (by omega : 3 ≤ n)
      ring fresh update x.physical e hPB
  have hYLock : grantDrainLedgerStrongLock ring
      (grantDrainEntranceNext ring fresh update x e).physical
      (ring.rightNeighbor e) = true :=
    grantDrainEntranceLiveStrongLock
      ring (grantDrainEntranceNext ring fresh update x e).physical
      (ring.rightNeighbor e) hNewPB hNewBad.1 hNewBad.2.1
  exact grantDrainEntrancePostStrongMarked ring fresh update x e i
    (ring.rightNeighbor e) hNewGrant hNewBad.2.1 hYLock

/-- Full one-edge contact trichotomy, for the exact paper pattern:
OLD tracked bullet at outgoing initiator X and OLD labelled grant
at responding Y. Regardless of the hostile fresh request, FIRE,
leader sink, resident bullet, coalescence or HOLD, either the
bullet retires, or the grant retires, or its source mark is promoted.
This is the no-passing condition at the only possible exchange edge. -/
theorem grantDrainEntranceSwap
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (x : GrantDrainEntranceState n Scratch)
    (e j i : Fin n)
    (hPB : PPlus ring x.physical.native)
    (hOldBullet : x.bulletHosts j = some e)
    (hOldGrant :
      (x.grantLabels i).host = some (ring.rightNeighbor e)) :
    (grantDrainEntranceNext ring fresh update x e).bulletHosts j = none ∨
    ((grantDrainEntranceNext ring fresh update x e).grantLabels i).host =
        none ∨
    ((grantDrainEntranceNext ring fresh update x e).grantLabels i).mark ≠
        .unmarked := by
  rcases grantDrainEntranceBulletOutgoing
      ring fresh update x e j hOldBullet with hRetired | hMoved
  · exact Or.inl hRetired
  · rcases grantDrainEntranceResponderHostCases ring
        (by omega : 2 ≤ n) fresh update x.physical e
        (x.grantLabels i) hOldGrant with hGone | hY | hX
    · exact Or.inr (Or.inl hGone)
    · exact Or.inr (Or.inr
        (grantDrainEntranceSwapHeldGrantMarked ring hn fresh update
          x e j i hPB hMoved hY))
    · exact Or.inr (Or.inr
        (grantDrainEntranceSwapMovedGrantMarked ring hn fresh update
          x e j i hPB hOldGrant hMoved hX))

end L3.GrantDrainEntrance


/-!
Separation. The source bullet either stays or moves one
clockwise edge; the source grant either stays or moves one
counterclockwise edge. The just-proved contact trichotomy excludes
the one wraparound swap with two surviving unmarked identities.
-/

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared
open L3.RenewalReferenceClock

set_option autoImplicit false
set_option Elab.async false

/-- A surviving initial non-leftmost LIVE identity can only stay
at its old site or advance on its actual outgoing service. -/
theorem grantDrainEntranceBulletSurvivorShape
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (x : GrantDrainEntranceState n Scratch) (e j b b' : Fin n)
    (hOld : x.bulletHosts j = some b)
    (hNew :
      (grantDrainEntranceNext ring fresh update x e).bulletHosts j =
        some b') :
    b' = b ∨ (b = e ∧ b' = ring.rightNeighbor e) := by
  classical
  by_cases hAtSource : b = e
  · have hSource : x.bulletHosts j = some e := by
      rw [hAtSource] at hOld
      exact hOld
    rcases grantDrainEntranceBulletOutgoing
      ring fresh update x e j hSource with hRet | hMove
    · rw [hNew] at hRet
      cases hRet
    · right
      refine ⟨hAtSource, ?_⟩
      exact (Option.some.inj (hMove.symm.trans hNew)).symm
  · have hRaw :
        grantDrainEntranceBulletAdvance ring fresh update
          x.physical e (some b) = some b' := by
      change grantDrainEntranceBulletAdvance ring fresh update
        x.physical e (x.bulletHosts j) = some b' at hNew
      rw [hOld] at hNew
      exact hNew
    by_cases hStay : SharedPaperNonleftmostLiveExact ring
        (grantDrainStep ring fresh update x.physical e).native b
    · have he : (some b : Option (Fin n)) = some b' := by
        simpa [grantDrainEntranceBulletAdvance, hAtSource, hStay]
          using hRaw
      exact Or.inl (Option.some.inj he).symm
    · have he : (none : Option (Fin n)) = some b' := by
        simpa [grantDrainEntranceBulletAdvance, hAtSource, hStay]
          using hRaw
      cases he

/-- If a bullet survives its nominated outgoing edge, it takes
exactly one clockwise step; it never stays at its old source. -/
theorem grantDrainEntranceBulletSurvivorOutgoingSite
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (x : GrantDrainEntranceState n Scratch) (e j b' : Fin n)
    (hOld : x.bulletHosts j = some e)
    (hNew :
      (grantDrainEntranceNext ring fresh update x e).bulletHosts j =
        some b') :
    b' = ring.rightNeighbor e := by
  rcases grantDrainEntranceBulletOutgoing
    ring fresh update x e j hOld with hRet | hMove
  · rw [hNew] at hRet
    cases hRet
  · exact (Option.some.inj (hMove.symm.trans hNew)).symm

/-- Any surviving old GRANT identity stays at its host, or moves
Y -> X on exactly the selected incoming edge. Other source values
are framed, and source grants cannot move right. -/
theorem grantDrainEntranceGrantSurvivorShape
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (x : GrantDrainEntranceState n Scratch) (e i g g' : Fin n)
    (hOld : (x.grantLabels i).host = some g)
    (hNew :
      ((grantDrainEntranceNext ring fresh update x e).grantLabels i).host =
        some g') :
    g' = g ∨ (g = ring.rightNeighbor e ∧ g' = e) := by
  have hRaw :
      grantDrainLedgerHost ring fresh x.physical e (some g) = some g' := by
    change grantDrainLedgerHost ring fresh x.physical e
      (x.grantLabels i).host = some g' at hNew
    rw [hOld] at hNew
    exact hNew
  by_cases hX : g = e
  · have hx :
        grantDrainLedgerHost ring fresh x.physical e (some e) =
          some g' := by
      simpa only [hX] using hRaw
    cases hStock :
        (x.physical.grant e &&
          (grantDrainLedgerRow ring fresh x.physical e).1.grant) with
    | false =>
        have he : (none : Option (Fin n)) = some g' := by
          simpa [grantDrainLedgerHost, hStock] using hx
        cases he
    | true =>
        have he : (some e : Option (Fin n)) = some g' := by
          simpa [grantDrainLedgerHost, hStock] using hx
        exact Or.inl ((Option.some.inj he).symm.trans hX.symm)
  · by_cases hY : g = ring.rightNeighbor e
    · have hy :
          grantDrainLedgerHost ring fresh x.physical e
            (some (ring.rightNeighbor e)) = some g' := by
        simpa only [hY] using hRaw
      have hDistinct : ring.rightNeighbor e ≠ e :=
        EWord.rightNeighborDifferent ring hn e
      cases hSource : grantDrainLedgerYSource
          (x.physical.request (ring.rightNeighbor e))
          (x.physical.grant (ring.rightNeighbor e))
          (grantDrainNativeNext ring x.physical e e).l
          (grantDrainNativeNext ring x.physical e
            (ring.rightNeighbor e)).l
          (grantDrainSelect ring x.physical e)
          (grantDrainLedgerRow ring fresh x.physical e) with
      | none =>
          have he : (none : Option (Fin n)) = some g' := by
            simpa [grantDrainLedgerHost, hDistinct, hSource] using hy
          cases he
      | some stays =>
          cases stays with
          | true =>
              have he :
                  (some (ring.rightNeighbor e) : Option (Fin n)) =
                    some g' := by
                simpa [grantDrainLedgerHost, hDistinct, hSource] using hy
              exact Or.inl ((Option.some.inj he).symm.trans hY.symm)
          | false =>
              have he : (some e : Option (Fin n)) = some g' := by
                simpa [grantDrainLedgerHost, hDistinct, hSource] using hy
              exact Or.inr ⟨hY, (Option.some.inj he).symm⟩
    · have he : (some g : Option (Fin n)) = some g' := by
        simpa [grantDrainLedgerHost, hX, hY] using hRaw
      exact Or.inl (Option.some.inj he).symm

/-- Moving an unmarked grant one edge counterclockwise reduces
the clockwise distance from ANY other site b by one, provided b
was not the old grant host itself. The forbidden modular wrap
would mean that the old grant host equals b. -/
theorem grantDrainEntranceGrantLeftDistance
    {n : Nat} (ring : DirectedRing n)
    (b e : Fin n)
    (hDifferent : b ≠ ring.rightNeighbor e) :
    PPL.cyclicOffset ring b e + 1 =
      PPL.cyclicOffset ring b (ring.rightNeighbor e) := by
  have hBound := grantDrainEntranceArcOffsetLt ring b e
  have hAdvance : PPL.cyclicOffset ring b e + 1 < n := by
    by_cases he : PPL.cyclicOffset ring b e + 1 = n
    · have hWrap : ring.rightNeighbor e = b := by
        calc
          ring.rightNeighbor e =
              PPL.shiftRight ring b (PPL.cyclicOffset ring b e + 1) :=
            grantDrainMarksNeighborOfOffset ring b e
          _ = PPL.shiftRight ring b n := by rw [he]
          _ = b := grantDrainMarksFullRotation ring b
      exact False.elim (hDifferent hWrap.symm)
    · omega
  exact (grantDrainMarksNeighborOffsetAdvance ring b e hAdvance).symm

/-- One-edge energy inequality under the *actual* PB/faithful-mark
carrier: a surviving unmarked pair cannot increase its clockwise
separation, and one bullet outgoing nominated hit costs one unit.
The only two-move case is the contact swap excluded by
grantDrainEntranceSwap. -/
theorem grantDrainEntranceSeparationStep
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (x : GrantDrainEntranceState n Scratch)
    (e j i b g b' g' : Fin n)
    (hPB : PPlus ring x.physical.native)
    (hFaithful : GrantDrainEntranceBulletFaithful ring x)
    (hMarkSound : GrantDrainEntranceMarkSound ring x)
    (hBullet : x.bulletHosts j = some b)
    (hGrant : (x.grantLabels i).host = some g)
    (hUnmarked : (x.grantLabels i).mark = .unmarked)
    (hNewBullet :
      (grantDrainEntranceNext ring fresh update x e).bulletHosts j =
        some b')
    (hNewGrant :
      ((grantDrainEntranceNext ring fresh update x e).grantLabels i).host =
        some g')
    (hNewUnmarked :
      ((grantDrainEntranceNext ring fresh update x e).grantLabels i).mark =
        .unmarked) :
    PPL.cyclicOffset ring b' g' + (if e = b then 1 else 0) ≤
      PPL.cyclicOffset ring b g := by
  have hRange := grantDrainEntranceSeparationRange
    ring x hPB hFaithful hMarkSound j i b g
    hBullet hGrant hUnmarked
  have hDifferent : b ≠ g := by
    intro he
    subst g
    exact grantDrainEntranceNoSharedSite ring x
      hPB hFaithful hMarkSound j i b
      hBullet hGrant hUnmarked
  have hBShape := grantDrainEntranceBulletSurvivorShape
    ring fresh update x e j b b' hBullet hNewBullet
  have hGShape := grantDrainEntranceGrantSurvivorShape
    ring (by omega : 2 ≤ n) fresh update
    x e i g g' hGrant hNewGrant
  rcases hBShape with hBStay | ⟨hBAtE, hBMove⟩
  · rcases hGShape with hGStay | ⟨hGAtY, hGMove⟩
    · have hNoHit : e ≠ b := by
        intro he
        have hAtE : x.bulletHosts j = some e := by
          rw [he]
          exact hBullet
        have hActual := grantDrainEntranceBulletSurvivorOutgoingSite
          ring fresh update x e j b' hAtE hNewBullet
        have hSelf : ring.rightNeighbor e = e := by
          calc
            ring.rightNeighbor e = b' := hActual.symm
            _ = b := hBStay
            _ = e := he.symm
        exact (EWord.rightNeighborDifferent ring
          (by omega : 2 ≤ n) e) hSelf
      rw [hBStay, hGStay]
      simp [hNoHit]
    · have hNotY : b ≠ ring.rightNeighbor e := by
        rw [← hGAtY]
        exact hDifferent
      have hShort :=
        grantDrainEntranceGrantLeftDistance ring b e hNotY
      calc
        PPL.cyclicOffset ring b' g' +
            (if e = b then 1 else 0) =
          PPL.cyclicOffset ring b e +
            (if e = b then 1 else 0) := by
              rw [hBStay, hGMove]
        _ ≤ PPL.cyclicOffset ring b e + 1 := by
          have hb : (if e = b then 1 else 0) ≤ 1 := by
            split <;> omega
          exact Nat.add_le_add_left hb _
        _ = PPL.cyclicOffset ring b (ring.rightNeighbor e) := hShort
        _ = PPL.cyclicOffset ring b g := by rw [hGAtY]
  · rcases hGShape with hGStay | ⟨hGAtY, hGMove⟩
    · have hShift : PPL.shiftRight ring b 1 =
          ring.rightNeighbor b := by
        apply Fin.ext
        rfl
      have hShort :
          PPL.cyclicOffset ring (ring.rightNeighbor b) g =
            PPL.cyclicOffset ring b g - 1 := by
        rw [← hShift]
        exact grantDrainMarksArcOffsetSubtract ring b g 1
          (by omega)
      have hNewB : b' = ring.rightNeighbor b := by
        rw [hBAtE]
        exact hBMove
      calc
        PPL.cyclicOffset ring b' g' +
            (if e = b then 1 else 0) =
          (PPL.cyclicOffset ring b g - 1) + 1 := by
            rw [hNewB, hGStay, hShort]
            simp [hBAtE]
        _ ≤ PPL.cyclicOffset ring b g := by omega
    · have hAtSource : x.bulletHosts j = some e := by
        rw [hBAtE] at hBullet
        exact hBullet
      have hAtResponder :
          (x.grantLabels i).host = some (ring.rightNeighbor e) := by
        rw [hGAtY] at hGrant
        exact hGrant
      rcases grantDrainEntranceSwap ring hn fresh update
          x e j i hPB hAtSource hAtResponder with
        hGoneBullet | hGoneGrant | hMarked
      · rw [hNewBullet] at hGoneBullet
        cases hGoneBullet
      · rw [hNewGrant] at hGoneGrant
        cases hGoneGrant
      · exact False.elim (hMarked hNewUnmarked)

end L3.GrantDrainEntrance


/-!
Word induction. Retired identities remain retired, marks
never demote, and the one-step separation inequality pays one unit
for every surviving nominated outgoing bullet hit.
-/

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared
open L3.RenewalReferenceClock

set_option autoImplicit false
set_option Elab.async false

theorem grantDrainEntranceBulletRetiredRun
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    ∀ (word : List (Fin n)) (x : GrantDrainEntranceState n Scratch)
      (j : Fin n),
      x.bulletHosts j = none →
      (grantDrainEntranceRun ring fresh update x word).bulletHosts j =
        none := by
  intro word
  induction word with
  | nil =>
      intro x j h
      exact h
  | cons e es ih =>
      intro x j h
      change (grantDrainEntranceRun ring fresh update
        (grantDrainEntranceNext ring fresh update x e) es).bulletHosts j =
          none
      exact ih (grantDrainEntranceNext ring fresh update x e) j
        (grantDrainEntranceBulletRetiredNext ring fresh update x e j h)

theorem grantDrainEntranceGrantRetiredRun
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    ∀ (word : List (Fin n)) (x : GrantDrainEntranceState n Scratch)
      (i : Fin n),
      (x.grantLabels i).host = none →
      ((grantDrainEntranceRun ring fresh update x word).grantLabels i).host =
        none := by
  intro word
  induction word with
  | nil =>
      intro x i h
      exact h
  | cons e es ih =>
      intro x i h
      change ((grantDrainEntranceRun ring fresh update
        (grantDrainEntranceNext ring fresh update x e) es).grantLabels i).host =
          none
      exact ih (grantDrainEntranceNext ring fresh update x e) i
        (grantDrainLedgerStep_retired_absorbing ring fresh update
          x.physical e (x.grantLabels i) h)

/-- The source mark never decreases on a scheduler word. -/
theorem grantDrainEntranceMarkRankRun
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    ∀ (word : List (Fin n)) (x : GrantDrainEntranceState n Scratch)
      (i : Fin n),
      grantDrainMarkRank (x.grantLabels i).mark ≤
        grantDrainMarkRank
          ((grantDrainEntranceRun ring fresh update x word).grantLabels i).mark := by
  intro word
  induction word with
  | nil =>
      intro x i
      exact Nat.le_refl _
  | cons e es ih =>
      intro x i
      change grantDrainMarkRank (x.grantLabels i).mark ≤
        grantDrainMarkRank
          ((grantDrainEntranceRun ring fresh update
            (grantDrainEntranceNext ring fresh update x e) es).grantLabels i).mark
      exact Nat.le_trans
        (grantDrainLedgerStep_mark_monotone
          ring fresh update x.physical e (x.grantLabels i))
        (ih (grantDrainEntranceNext ring fresh update x e) i)

/-- Wordwise conservation: hits plus final clockwise separation
cannot exceed the initial clockwise separation for a pair that
survives the entire word while the grant remains unmarked. -/
theorem grantDrainEntranceSeparationWord
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (j i : Fin n) :
    ∀ (word : List (Fin n)) (x : GrantDrainEntranceState n Scratch)
      (b g b' g' : Fin n),
      PPlus ring x.physical.native →
      GrantDrainEntranceBulletFaithful ring x →
      GrantDrainEntranceMarkSound ring x →
      x.bulletHosts j = some b →
      (x.grantLabels i).host = some g →
      (x.grantLabels i).mark = .unmarked →
      (grantDrainEntranceRun ring fresh update x word).bulletHosts j =
        some b' →
      ((grantDrainEntranceRun ring fresh update x word).grantLabels i).host =
        some g' →
      ((grantDrainEntranceRun ring fresh update x word).grantLabels i).mark =
        .unmarked →
      grantDrainEntranceBulletHits ring fresh update j x word +
        PPL.cyclicOffset ring b' g' ≤
          PPL.cyclicOffset ring b g := by
  intro word
  induction word with
  | nil =>
      intro x b g b' g' hPB hFaithful hMark hOldBullet hOldGrant
        hOldUnmarked hFinalBullet hFinalGrant hFinalUnmarked
      change x.bulletHosts j = some b' at hFinalBullet
      change (x.grantLabels i).host = some g' at hFinalGrant
      have hb : b = b' :=
        Option.some.inj (hOldBullet.symm.trans hFinalBullet)
      have hg : g = g' :=
        Option.some.inj (hOldGrant.symm.trans hFinalGrant)
      change (0 : Nat) + PPL.cyclicOffset ring b' g' ≤
        PPL.cyclicOffset ring b g
      simp only [Nat.zero_add]
      rw [← hb, ← hg]
      exact Nat.le_refl _
  | cons e es ih =>
      intro x b g b' g' hPB hFaithful hMark hOldBullet hOldGrant
        hOldUnmarked hFinalBullet hFinalGrant hFinalUnmarked
      change
        (grantDrainEntranceRun ring fresh update
          (grantDrainEntranceNext ring fresh update x e) es).bulletHosts j =
            some b' at hFinalBullet
      change
        ((grantDrainEntranceRun ring fresh update
          (grantDrainEntranceNext ring fresh update x e) es).grantLabels i).host =
            some g' at hFinalGrant
      change
        ((grantDrainEntranceRun ring fresh update
          (grantDrainEntranceNext ring fresh update x e) es).grantLabels i).mark =
            .unmarked at hFinalUnmarked
      cases hNextB :
          (grantDrainEntranceNext ring fresh update x e).bulletHosts j with
      | none =>
          have hNever := grantDrainEntranceBulletRetiredRun
            ring fresh update es
            (grantDrainEntranceNext ring fresh update x e) j hNextB
          rw [hNever] at hFinalBullet
          cases hFinalBullet
      | some bNext =>
          cases hNextG :
              ((grantDrainEntranceNext ring fresh update x e).grantLabels i).host with
          | none =>
              have hNever := grantDrainEntranceGrantRetiredRun
                ring fresh update es
                (grantDrainEntranceNext ring fresh update x e) i hNextG
              rw [hNever] at hFinalGrant
              cases hFinalGrant
          | some gNext =>
              have hNextUnmarked :
                  ((grantDrainEntranceNext ring fresh update x e).grantLabels i).mark =
                    .unmarked := by
                have hMono := grantDrainEntranceMarkRankRun
                  ring fresh update es
                  (grantDrainEntranceNext ring fresh update x e) i
                rw [hFinalUnmarked] at hMono
                cases hm :
                    ((grantDrainEntranceNext ring fresh update x e).grantLabels i).mark with
                | unmarked => rfl
                | weak =>
                    simp [grantDrainMarkRank, hm] at hMono
                | strong =>
                    simp [grantDrainMarkRank, hm] at hMono
                | terminal =>
                    simp [grantDrainMarkRank, hm] at hMono
              have hStepPB : PPlus ring
                  (grantDrainEntranceNext ring fresh update x e).physical.native :=
                grantDrainStep_preserves_PPlus
                  (by omega : 3 ≤ n) ring fresh update x.physical e hPB
              have hStepFaithful :=
                grantDrainEntranceFaithfulNext
                  ring hn fresh update x e hPB hFaithful
              have hStepMark :=
                grantDrainEntranceMarkSoundNext ring fresh update x e
              have hStepEnergy :=
                grantDrainEntranceSeparationStep
                  ring hn fresh update x e j i b g bNext gNext
                  hPB hFaithful hMark hOldBullet hOldGrant
                  hOldUnmarked hNextB hNextG hNextUnmarked
              have hTail :=
                ih (grantDrainEntranceNext ring fresh update x e)
                  bNext gNext b' g' hStepPB hStepFaithful hStepMark
                  hNextB hNextG hNextUnmarked
                  hFinalBullet hFinalGrant hFinalUnmarked
              change
                (if e = grantDrainEntranceBulletChosen x j then 1 else 0) +
                  grantDrainEntranceBulletHits ring fresh update j
                    (grantDrainEntranceNext ring fresh update x e) es +
                  PPL.cyclicOffset ring b' g' ≤
                    PPL.cyclicOffset ring b g
              rw [grantDrainEntranceBulletChosenAtHost x j b hOldBullet]
              omega

/-- The pathwise quota of paper lines 440-447, on the actual
canonical source and promoted source ledger: as long as both
original identities survive and the GRANT remains unmarked,
there have been fewer than n outgoing bullet hits since entrance. -/
theorem grantDrainEntranceNominatedQuota
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (word : List (Fin n)) (j i b' g' : Fin n)
    (hPB : PPlus ring s.native)
    (hBulletFinal :
      (grantDrainEntranceRun ring fresh update
        (grantDrainEntranceInitial ring s) word).bulletHosts j = some b')
    (hGrantFinal :
      ((grantDrainEntranceRun ring fresh update
        (grantDrainEntranceInitial ring s) word).grantLabels i).host =
          some g')
    (hMarkFinal :
      ((grantDrainEntranceRun ring fresh update
        (grantDrainEntranceInitial ring s) word).grantLabels i).mark =
          .unmarked) :
    grantDrainEntranceBulletHits ring fresh update j
      (grantDrainEntranceInitial ring s) word < n := by
  cases hInitialBullet :
      (grantDrainEntranceInitial ring s).bulletHosts j with
  | none =>
      have hRetired := grantDrainEntranceBulletRetiredRun
        ring fresh update word (grantDrainEntranceInitial ring s)
        j hInitialBullet
      rw [hRetired] at hBulletFinal
      cases hBulletFinal
  | some b =>
      cases hInitialGrant :
          ((grantDrainEntranceInitial ring s).grantLabels i).host with
      | none =>
          have hRetired := grantDrainEntranceGrantRetiredRun
            ring fresh update word (grantDrainEntranceInitial ring s)
            i hInitialGrant
          rw [hRetired] at hGrantFinal
          cases hGrantFinal
      | some g =>
          have hInitialUnmarked :
              ((grantDrainEntranceInitial ring s).grantLabels i).mark =
                .unmarked := by
            have hMono := grantDrainEntranceMarkRankRun
              ring fresh update word (grantDrainEntranceInitial ring s) i
            rw [hMarkFinal] at hMono
            cases hm :
                ((grantDrainEntranceInitial ring s).grantLabels i).mark with
            | unmarked => rfl
            | weak =>
                simp [grantDrainMarkRank, hm] at hMono
            | strong =>
                simp [grantDrainMarkRank, hm] at hMono
            | terminal =>
                simp [grantDrainMarkRank, hm] at hMono
          have hEnergy :=
            grantDrainEntranceSeparationWord
              ring hn fresh update j i word
              (grantDrainEntranceInitial ring s)
              b g b' g' hPB
              (grantDrainEntranceInitialFaithful ring s)
              (grantDrainEntranceInitialMarkSound ring s)
              hInitialBullet hInitialGrant hInitialUnmarked
              hBulletFinal hGrantFinal hMarkFinal
          have hBound := grantDrainEntranceArcOffsetLt ring b g
          omega

end L3.GrantDrainEntrance


/-!
Exact local native-E audit for the contact edge:
old X has LIVE, old Y is an empty follower. This records the actual
source/receiver signal row, independent of any grant token update.
-/

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared
open L3.RenewalReferenceClock

set_option autoImplicit false
set_option Elab.async false

/-- A peaceful OLD live bullet has signal zero at its own source.
This supplies the X signal premise of the exact E row. -/
theorem grantDrainEntranceContactOldSignalZero
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hPB : PPlus ring s.native)
    (hLive : LiveBullet s.native e) :
    (s.native e).sg = false := by
  have hPeace : PPL.PeacefulCore ring
      (fun i : Fin n => (s.native i).l)
      (fun i : Fin n => (s.native i).sh)
      (fun i : Fin n => (s.native i).sg) e :=
    hPB.2 e hLive
  unfold PPL.PeacefulCore at hPeace
  cases hd : PPL.dLLBy ring
      (fun i : Fin n => (s.native i).l) e with
  | none =>
      rw [hd] at hPeace
      exact hPeace e
  | some d =>
      rw [hd] at hPeace
      have hHere : (s.native (PPL.shiftLeft ring e 0)).sg = false :=
        hPeace.2 (0 : Fin (d + 1))
      have hShift : PPL.shiftLeft ring e 0 = e := by
        apply Fin.ext
        simp [PPL.shiftLeft, Nat.mod_eq_of_lt e.isLt]
      rw [hShift] at hHere
      exact hHere

/-- Literal certLiteralEPair row: the OLD X LIVE enters empty
follower Y, setting B_Y=2 and S_Y=0. With peaceful S_X=0,
the NEW source signal S_X also remains zero. The old Y signal
and both shields are unrestricted, and no fresh request is read. -/
theorem grantDrainEntranceContactNativeSignalRow
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hLive : LiveBullet s.native e)
    (hXFollower : (s.native e).l = false)
    (hYFollower : (s.native (ring.rightNeighbor e)).l = false)
    (hYEmpty : (s.native (ring.rightNeighbor e)).b = (0 : Fin 3))
    (hOldXSignal : (s.native e).sg = false) :
    (nativeE ring s.native e e).sg = false ∧
    (nativeE ring s.native e (ring.rightNeighbor e)).sg = false ∧
    (nativeE ring s.native e (ring.rightNeighbor e)).b =
      (2 : Fin 3) := by
  have hDistinct : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring hn e
  have hSource :
      nativeE ring s.native e e =
        (certLiteralEPair (s.native e)
          (s.native (ring.rightNeighbor e))).1 := by
    simp [nativeE]
  have hResponder :
      nativeE ring s.native e (ring.rightNeighbor e) =
        (certLiteralEPair (s.native e)
          (s.native (ring.rightNeighbor e))).2 := by
    simp [nativeE, hDistinct]
  have hLiteral :
      (certLiteralEPair (s.native e)
        (s.native (ring.rightNeighbor e))).1.sg = false ∧
      (certLiteralEPair (s.native e)
        (s.native (ring.rightNeighbor e))).2.sg = false ∧
      (certLiteralEPair (s.native e)
        (s.native (ring.rightNeighbor e))).2.b = (2 : Fin 3) := by
    change (s.native e).b = (2 : Fin 3) at hLive
    simp [certLiteralEPair, certFinThree, hLive,
      hXFollower, hYFollower, hYEmpty, hOldXSignal]
  rw [hSource, hResponder]
  exact hLiteral

/-- The actual Y post-E site is not FIRE-eligible: it now holds
the incoming LIVE. Thus the F1/rightLocal selector cannot fire at
Y in this contact row. Possible source births are separately ruled
out when an OLD Y grant actually survives at X, by the source sink
lemma in grantDrainEntranceResponderMoveSourceFollower. -/
theorem grantDrainEntranceContactResponderNotEligible
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hLive : LiveBullet s.native e)
    (hXFollower : (s.native e).l = false)
    (hYFollower : (s.native (ring.rightNeighbor e)).l = false)
    (hYEmpty : (s.native (ring.rightNeighbor e)).b = (0 : Fin 3))
    (hOldXSignal : (s.native e).sg = false) :
    grantDrainEligible (nativeE ring s.native e)
      (ring.rightNeighbor e) = false := by
  have hRow := grantDrainEntranceContactNativeSignalRow
    ring hn s e hLive hXFollower hYFollower hYEmpty hOldXSignal
  simp [grantDrainEligible, hRow.2.2]

end L3.GrantDrainEntrance



/-!
R8d source first-branch tail. The source GrantDrainEntranceDone, its closure and
grantDrainEntranceNominatedQuota are the inputs.
The weighted finite-word argument is reproduced from the core-only
nominated-hit proof, with local names; no later bank-repair module
is imported.
-/

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared
open L3.RenewalReferenceClock
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- Every still-active zeta word has at least one original bullet
identity below its n-hit quota. This is the literal D.2 implication,
using the already pathwise noncrossing theorem. -/
theorem grantDrainEntranceNotDoneShortHits
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (word : List (Fin n))
    (hPB : PPlus ring s.native)
    (hNotDone : ¬ GrantDrainEntranceDone
      (grantDrainEntranceRun ring fresh update
        (grantDrainEntranceInitial ring s) word)) :
    ∃ j : Fin n,
      grantDrainEntranceBulletHits ring fresh update j
        (grantDrainEntranceInitial ring s) word < n := by
  classical
  have hBulletNotAll : ¬ (∀ j : Fin n,
      (grantDrainEntranceRun ring fresh update
        (grantDrainEntranceInitial ring s) word).bulletHosts j = none) := by
    intro hAll
    exact hNotDone (Or.inl hAll)
  obtain ⟨j, hj⟩ := Classical.not_forall.mp hBulletNotAll
  cases hBulletHost :
      (grantDrainEntranceRun ring fresh update
        (grantDrainEntranceInitial ring s) word).bulletHosts j with
  | none =>
      exact False.elim (hj hBulletHost)
  | some b =>
      have hGrantNotAll : ¬ (∀ i : Fin n,
          ((grantDrainEntranceRun ring fresh update
            (grantDrainEntranceInitial ring s) word).grantLabels i).host ≠ none →
          ((grantDrainEntranceRun ring fresh update
            (grantDrainEntranceInitial ring s) word).grantLabels i).mark ≠
            .unmarked) := by
        intro hAll
        exact hNotDone (Or.inr hAll)
      obtain ⟨i, hi⟩ := Classical.not_forall.mp hGrantNotAll
      have hGrantLive :
          ((grantDrainEntranceRun ring fresh update
            (grantDrainEntranceInitial ring s) word).grantLabels i).host ≠
            none := by
        intro hNone
        exact hi (fun hAlive => False.elim (hAlive hNone))
      have hUnmarked :
          ((grantDrainEntranceRun ring fresh update
            (grantDrainEntranceInitial ring s) word).grantLabels i).mark =
            .unmarked := by
        by_cases hm :
            ((grantDrainEntranceRun ring fresh update
              (grantDrainEntranceInitial ring s) word).grantLabels i).mark =
              .unmarked
        · exact hm
        · exact False.elim (hi (fun _ => hm))
      cases hGrantHost :
          ((grantDrainEntranceRun ring fresh update
            (grantDrainEntranceInitial ring s) word).grantLabels i).host with
      | none =>
          exact False.elim (hGrantLive hGrantHost)
      | some g =>
          exact ⟨j, grantDrainEntranceNominatedQuota
            ring hn fresh update s word j i b g hPB
            hBulletHost hGrantHost hUnmarked⟩

/-- Uniform first-hit survival is a 0-or-1 indicator on every
scheduler word, without requiring terminal closure. -/
private theorem grantDrainEntranceSurvivalBit
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

/-- First-hit survival forces zeta NOT done at the final state
of the same physical/ghost scheduler word. -/
private theorem grantDrainEntranceSurvivalEndNot
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    ∀ (x : GrantDrainEntranceState n Scratch) (w : List (Fin n)),
      UniformFirstHit.survivalWord
        (grantDrainEntranceNext ring fresh update)
        GrantDrainEntranceDone x w = 1 →
      ¬ GrantDrainEntranceDone
        (grantDrainEntranceRun ring fresh update x w) := by
  classical
  intro x w
  induction w generalizing x with
  | nil =>
      intro hs hp
      simp [UniformFirstHit.survivalWord] at hs
      exact hs hp
  | cons e es ih =>
      intro hs
      by_cases hp : GrantDrainEntranceDone x
      · simp [UniformFirstHit.survivalWord, hp] at hs
      · have ht :
            UniformFirstHit.survivalWord
              (grantDrainEntranceNext ring fresh update)
              GrantDrainEntranceDone
              (grantDrainEntranceNext ring fresh update x e) es = 1 := by
          simpa only [UniformFirstHit.survivalWord, if_neg hp] using hs
        change ¬ GrantDrainEntranceDone
          (grantDrainEntranceRun ring fresh update
            (grantDrainEntranceNext ring fresh update x e) es)
        exact ih (grantDrainEntranceNext ring fresh update x e) ht

/-- Core List Nat sum has at least one unit when a literal one
occurs in the list. No Mathlib List.le_sum_of_mem is used. -/
private theorem grantDrainEntranceOneLeSum
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

/-! The exact 1-versus-2 predictable-edge exponential moment,
copied from RenewalGrantStage with local names to stay in the
import closure. Every nomination is state-predictable. -/
private def grantDrainEntranceTailMissWeight {S : Type} {n : Nat}
    (next : S → Fin n → S) (chosen : S → Fin n) :
    S → List (Fin n) → Nat
  | _, [] => 1
  | x, e :: es =>
      (if e = chosen x then 1 else 2) *
        grantDrainEntranceTailMissWeight next chosen (next x e) es

private theorem grantDrainEntranceTailEdgeWeight {n : Nat} (a : Fin n) :
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

private theorem grantDrainEntranceTailScheduleMul {n : Nat} (T c : Nat)
    (f : List (Fin n) → Nat) :
    L3.Prob.scheduleSum n T (fun w => c * f w) =
      c * L3.Prob.scheduleSum n T f := by
  change FixedSpanRenewalPayload.wordSum n T (fun w => c * f w) =
    c * FixedSpanRenewalPayload.wordSum n T f
  rw [← FixedSpanRenewalPayload.rawWord_sum n T (fun w => c * f w),
    ← FixedSpanRenewalPayload.rawWord_sum n T f,
    ofFn_sum_mul_left]

private theorem grantDrainEntranceTailMass {S : Type} {n : Nat}
    (next : S → Fin n → S) (chosen : S → Fin n)
    (x : S) (T : Nat) (hn : 0 < n) :
    L3.Prob.scheduleSum n T
      (fun w => grantDrainEntranceTailMissWeight next chosen x w) =
        (2 * n - 1) ^ T := by
  induction T generalizing x with
  | zero =>
      simp [L3.Prob.scheduleSum, FixedSpanRenewalPayload.wordSum,
        allSchedules, grantDrainEntranceTailMissWeight]
  | succ T ih =>
      have hrow (e : Fin n) :
          L3.Prob.scheduleSum n T
            (fun w => grantDrainEntranceTailMissWeight next chosen x (e :: w)) =
          (if e = chosen x then 1 else 2) * (2 * n - 1) ^ T := by
        calc
          _ = L3.Prob.scheduleSum n T
                (fun w => (if e = chosen x then 1 else 2) *
                  grantDrainEntranceTailMissWeight next chosen (next x e) w) := rfl
          _ = (if e = chosen x then 1 else 2) *
                L3.Prob.scheduleSum n T
                  (fun w => grantDrainEntranceTailMissWeight next chosen (next x e) w) :=
                grantDrainEntranceTailScheduleMul T _ _
          _ = (if e = chosen x then 1 else 2) *
                (2 * n - 1) ^ T := by
                rw [ih (next x e)]
      calc
        L3.Prob.scheduleSum n (T + 1)
            (fun w => grantDrainEntranceTailMissWeight next chosen x w) =
          (List.ofFn (fun e : Fin n =>
            L3.Prob.scheduleSum n T
              (fun w => grantDrainEntranceTailMissWeight next chosen x (e :: w)))).sum :=
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
            rw [grantDrainEntranceTailEdgeWeight]
        _ = (2 * n - 1) ^ (T + 1) := by
            rw [Nat.pow_succ]

private theorem grantDrainEntranceTailHitsProduct {S : Type} {n : Nat}
    (next : S → Fin n → S) (chosen : S → Fin n)
    (hits : S → List (Fin n) → Nat)
    (hzero : ∀ y : S, hits y [] = 0)
    (hcons : ∀ (y : S) (e : Fin n) (es : List (Fin n)),
      hits y (e :: es) =
        (if e = chosen y then 1 else 0) + hits (next y e) es)
    (x : S) (w : List (Fin n)) :
    2 ^ (hits x w) * grantDrainEntranceTailMissWeight next chosen x w =
      2 ^ w.length := by
  induction w generalizing x with
  | nil =>
      simp [hzero, grantDrainEntranceTailMissWeight]
  | cons e es ih =>
      rw [hcons x e es]
      by_cases he : e = chosen x
      · simp only [if_pos he, grantDrainEntranceTailMissWeight,
          List.length_cons, Nat.one_mul]
        have hadd :
            1 + hits (next x e) es = hits (next x e) es + 1 := by
          omega
        rw [hadd, Nat.pow_succ, Nat.pow_succ]
        calc
          (2 ^ hits (next x e) es * 2) *
              grantDrainEntranceTailMissWeight next chosen (next x e) es =
            (2 ^ hits (next x e) es *
              grantDrainEntranceTailMissWeight next chosen (next x e) es) * 2 := by
                ac_rfl
          _ = 2 ^ es.length * 2 := by
                rw [ih (next x e)]
      · simp only [if_neg he, grantDrainEntranceTailMissWeight,
          List.length_cons, Nat.zero_add]
        rw [Nat.pow_succ]
        calc
          2 ^ hits (next x e) es *
              (2 * grantDrainEntranceTailMissWeight next chosen (next x e) es) =
            (2 ^ hits (next x e) es *
              grantDrainEntranceTailMissWeight next chosen (next x e) es) * 2 := by
                ac_rfl
          _ = 2 ^ es.length * 2 := by
                rw [ih (next x e)]

private theorem grantDrainEntranceTailScheduleLengthMul {n : Nat}
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

private theorem grantDrainEntranceTailWeighted {S : Type} {n : Nat}
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
      2 ^ Q * grantDrainEntranceTailMissWeight next chosen x w := by
    by_cases h : hits x w < Q
    · have hpow : 2 * 2 ^ (hits x w) ≤ 2 ^ Q := by
        have hmono : 2 ^ (hits x w + 1) ≤ 2 ^ Q :=
          Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) (by omega)
        simpa only [Nat.pow_succ, Nat.mul_comm] using hmono
      simp only [if_pos h, Nat.mul_one]
      calc
        2 ^ (w.length + 1) =
          (2 * 2 ^ (hits x w)) *
            grantDrainEntranceTailMissWeight next chosen x w := by
              rw [Nat.pow_succ,
                ← grantDrainEntranceTailHitsProduct next chosen hits hzero hcons x w]
              ac_rfl
        _ ≤ 2 ^ Q * grantDrainEntranceTailMissWeight next chosen x w :=
          Nat.mul_le_mul_right _ hpow
    · simp [h]
  calc
    2 ^ (T + 1) *
        L3.Prob.scheduleSum n T
          (fun w => if hits x w < Q then 1 else 0) =
      L3.Prob.scheduleSum n T
        (fun w => 2 ^ (w.length + 1) *
          (if hits x w < Q then 1 else 0)) :=
        (grantDrainEntranceTailScheduleLengthMul T 2 _).symm
    _ ≤ L3.Prob.scheduleSum n T
          (fun w => 2 ^ Q * grantDrainEntranceTailMissWeight next chosen x w) :=
        L3.Density.schedule_sum_mono T _ _ hpoint
    _ = 2 ^ Q * (2 * n - 1) ^ T := by
        rw [grantDrainEntranceTailScheduleMul, grantDrainEntranceTailMass next chosen x T hn]



/-- D.3 in exact Nat form, after unioning over at most n initial
bullet identities on the SAME scheduler word. This keeps the
stronger weighted exponent rather than the weak half-tail bound. -/
theorem grantDrainEntranceWeightedFamilySurvival
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (hPB : PPlus ring s.native) (T : Nat) :
    2 ^ (T + 1) *
      UniformFirstHit.survivalNumerator
        (grantDrainEntranceNext ring fresh update)
        GrantDrainEntranceDone (grantDrainEntranceInitial ring s) T ≤
      n * (2 ^ n * (2 * n - 1) ^ T) := by
  classical
  have hpoint (w : List (Fin n)) :
      UniformFirstHit.survivalWord
        (grantDrainEntranceNext ring fresh update)
        GrantDrainEntranceDone (grantDrainEntranceInitial ring s) w ≤
      (List.ofFn (fun j : Fin n =>
        if grantDrainEntranceBulletHits ring fresh update j
          (grantDrainEntranceInitial ring s) w < n then 1 else 0)).sum := by
    by_cases hs : UniformFirstHit.survivalWord
        (grantDrainEntranceNext ring fresh update)
        GrantDrainEntranceDone (grantDrainEntranceInitial ring s) w = 1
    · have hNotDone := grantDrainEntranceSurvivalEndNot
        ring fresh update (grantDrainEntranceInitial ring s) w hs
      obtain ⟨j, hj⟩ := grantDrainEntranceNotDoneShortHits
        ring hn fresh update s w hPB hNotDone
      have hMember : (1 : Nat) ∈
          List.ofFn (fun j : Fin n =>
            if grantDrainEntranceBulletHits ring fresh update j
              (grantDrainEntranceInitial ring s) w < n then 1 else 0) :=
        List.mem_ofFn.mpr ⟨j, by simp [hj]⟩
      rw [hs]
      exact grantDrainEntranceOneLeSum _ hMember
    · have hZero :
          UniformFirstHit.survivalWord
            (grantDrainEntranceNext ring fresh update)
            GrantDrainEntranceDone (grantDrainEntranceInitial ring s) w = 0 := by
        have hb := grantDrainEntranceSurvivalBit
          (grantDrainEntranceNext ring fresh update)
          GrantDrainEntranceDone (grantDrainEntranceInitial ring s) w
        omega
      rw [hZero]
      exact Nat.zero_le _
  have hmass :
      UniformFirstHit.survivalNumerator
        (grantDrainEntranceNext ring fresh update)
        GrantDrainEntranceDone (grantDrainEntranceInitial ring s) T ≤
      L3.Prob.scheduleSum n T
        (fun w => (List.ofFn (fun j : Fin n =>
          if grantDrainEntranceBulletHits ring fresh update j
            (grantDrainEntranceInitial ring s) w < n then 1 else 0)).sum) := by
    change L3.Prob.scheduleSum n T
      (UniformFirstHit.survivalWord
        (grantDrainEntranceNext ring fresh update)
        GrantDrainEntranceDone (grantDrainEntranceInitial ring s)) ≤ _
    exact L3.Density.schedule_sum_mono T _ _ hpoint
  have hrow (j : Fin n) :
      2 ^ (T + 1) *
        L3.Prob.scheduleSum n T
          (fun w => if grantDrainEntranceBulletHits ring fresh update
            j (grantDrainEntranceInitial ring s) w < n then 1 else 0) ≤
      2 ^ n * (2 * n - 1) ^ T :=
    grantDrainEntranceTailWeighted
      (grantDrainEntranceNext ring fresh update)
      (fun x => grantDrainEntranceBulletChosen x j)
      (grantDrainEntranceBulletHits ring fresh update j)
      (by intro y; rfl)
      (by intro y e es; rfl)
      (grantDrainEntranceInitial ring s) T n (by omega : 0 < n)
  calc
    2 ^ (T + 1) *
        UniformFirstHit.survivalNumerator
          (grantDrainEntranceNext ring fresh update)
          GrantDrainEntranceDone (grantDrainEntranceInitial ring s) T ≤
      2 ^ (T + 1) *
        L3.Prob.scheduleSum n T
          (fun w => (List.ofFn (fun j : Fin n =>
            if grantDrainEntranceBulletHits ring fresh update j
              (grantDrainEntranceInitial ring s) w < n then 1 else 0)).sum) :=
        Nat.mul_le_mul_left _ hmass
    _ = (List.ofFn (fun j : Fin n =>
          2 ^ (T + 1) *
            L3.Prob.scheduleSum n T
              (fun w => if grantDrainEntranceBulletHits ring fresh update j
                (grantDrainEntranceInitial ring s) w < n then 1 else 0))).sum := by
        rw [L3.Density.schedule_sum_fin, ← ofFn_sum_mul_left]
    _ ≤ (List.ofFn (fun _ : Fin n =>
          2 ^ n * (2 * n - 1) ^ T)).sum :=
      ofFn_sum_le _ _ hrow
    _ = n * (2 ^ n * (2 * n - 1) ^ T) := by
      rw [ofFn_sum_const]

end L3.GrantDrainEntrance


/-! Elementary Nat exponential cutoff and geometric cost, specialized
to the actual first zeta stage. At T=3n² the weighted n-label union
has at least n+1 doubling blocks of length 2n. -/

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared
open L3.RenewalReferenceClock
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

private theorem grantDrainEntranceTailLinearPower (a k : Nat) :
    a ^ k * (a + 1 + k) ≤ (a + 1) ^ (k + 1) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hp : a ^ (k + 1) ≤ (a + 1) ^ (k + 1) :=
        Nat.pow_le_pow_left (Nat.le_succ a) (k + 1)
      calc
        a ^ (k + 1) * (a + 1 + (k + 1)) =
          (a ^ k * (a + 1 + k)) * a + a ^ (k + 1) := by
            have hc : a + 1 + (k + 1) = a + 1 + k + 1 := by
              omega
            rw [hc]
            simp only [Nat.pow_succ, Nat.mul_add, Nat.add_mul, Nat.mul_one,
              Nat.one_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        _ ≤ (a + 1) ^ (k + 1) * a +
              (a + 1) ^ (k + 1) :=
          Nat.add_le_add (Nat.mul_le_mul_right a ih) hp
        _ = (a + 1) ^ ((k + 1) + 1) := by
          rw [Nat.pow_succ (a + 1) (k + 1), Nat.mul_add, Nat.mul_one]

private theorem grantDrainEntranceTailHalfBlock (n : Nat) (hn : 0 < n) :
    2 * (2 * n - 1) ^ (2 * n) ≤ (2 * n) ^ (2 * n) := by
  have he : (2 * n - 1) + 1 = 2 * n := by
    omega
  have hpow :
      (2 * n - 1) ^ (2 * n) =
        (2 * n - 1) ^ (2 * n - 1) * (2 * n - 1) := by
    calc
      (2 * n - 1) ^ (2 * n) =
          (2 * n - 1) ^ ((2 * n - 1) + 1) := by
            rw [he]
      _ = (2 * n - 1) ^ (2 * n - 1) * (2 * n - 1) :=
        Nat.pow_succ _ _
  calc
    2 * (2 * n - 1) ^ (2 * n) =
        (2 * n - 1) ^ (2 * n - 1) * (2 * (2 * n - 1)) := by
          rw [hpow]
          ac_rfl
    _ ≤ (2 * n - 1) ^ (2 * n - 1) *
        ((2 * n - 1) + 1 + (2 * n - 1)) :=
          Nat.mul_le_mul_left _ (by omega)
    _ ≤ ((2 * n - 1) + 1) ^ ((2 * n - 1) + 1) :=
          grantDrainEntranceTailLinearPower _ _
    _ = (2 * n) ^ (2 * n) := by
          rw [he]

private theorem grantDrainEntranceTailDecay (n T Q : Nat) (hn : 0 < n)
    (hT : 2 * n * Q ≤ T) :
    2 ^ Q * (2 * n - 1) ^ T ≤ (2 * n) ^ T := by
  have hblock := grantDrainEntranceTailHalfBlock n hn
  have hpower :
      (2 * (2 * n - 1) ^ (2 * n)) ^ Q ≤
        ((2 * n) ^ (2 * n)) ^ Q :=
    Nat.pow_le_pow_left hblock Q
  have hblocks :
      2 ^ Q * (2 * n - 1) ^ (2 * n * Q) ≤
        (2 * n) ^ (2 * n * Q) := by
    simpa only [Nat.mul_pow, ← Nat.pow_mul] using hpower
  have hsplit : 2 * n * Q + (T - 2 * n * Q) = T := by
    omega
  calc
    2 ^ Q * (2 * n - 1) ^ T =
        (2 ^ Q * (2 * n - 1) ^ (2 * n * Q)) *
          (2 * n - 1) ^ (T - 2 * n * Q) := by
            rw [Nat.mul_assoc, ← Nat.pow_add, hsplit]
    _ ≤ (2 * n) ^ (2 * n * Q) *
          (2 * n) ^ (T - 2 * n * Q) :=
        Nat.mul_le_mul hblocks
          (Nat.pow_le_pow_left
            (by omega : 2 * n - 1 ≤ 2 * n) (T - 2 * n * Q))
    _ = (2 * n) ^ T := by
        rw [← Nat.pow_add, hsplit]


/-- Exact integer replacement for the paper's exponential cutoff.
For n≥5, 2n(n+1) ≤ 3n²; each 2n-block loses a factor two. -/
theorem grantDrainEntranceThreeSquareCutoff
    (n : Nat) (hn : 5 ≤ n) :
    2 ^ (n + 1) * (2 * n - 1) ^ (3 * n ^ 2) ≤
      (2 * n) ^ (3 * n ^ 2) := by
  have hN : 2 * n ≤ n * n :=
    Nat.mul_le_mul_right n (by omega : 2 ≤ n)
  have hT : 2 * n * (n + 1) ≤ 3 * n ^ 2 := by
    calc
      2 * n * (n + 1) = (2 * n) * n + 2 * n := by
        rw [Nat.mul_add, Nat.mul_one]
      _ = 2 * (n * n) + 2 * n := by ac_rfl
      _ ≤ 2 * (n * n) + n * n :=
        Nat.add_le_add_left hN _
      _ = 3 * n ^ 2 := by
        rw [Nat.pow_two]
        omega
  exact grantDrainEntranceTailDecay
    n (3 * n ^ 2) (n + 1) (by omega : 0 < n) hT

/-- In the tail T=3n²+u the scaled live-word mass is controlled
by a single exact geometric factor r^u, with r=2n-1. -/
theorem grantDrainEntranceSurvivalAfterCutoff
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (hPB : PPlus ring s.native) (u : Nat) :
    4 * 2 ^ (3 * n ^ 2 + u) *
      UniformFirstHit.survivalNumerator
        (grantDrainEntranceNext ring fresh update)
        GrantDrainEntranceDone (grantDrainEntranceInitial ring s)
        (3 * n ^ 2 + u) ≤
      n * (2 * n) ^ (3 * n ^ 2) * (2 * n - 1) ^ u := by
  have hFamily := grantDrainEntranceWeightedFamilySurvival
    ring hn fresh update s hPB (3 * n ^ 2 + u)
  have hCut := grantDrainEntranceThreeSquareCutoff n hn
  calc
    4 * 2 ^ (3 * n ^ 2 + u) *
        UniformFirstHit.survivalNumerator
          (grantDrainEntranceNext ring fresh update)
          GrantDrainEntranceDone (grantDrainEntranceInitial ring s)
          (3 * n ^ 2 + u) ≤
      2 * (n * (2 ^ n * (2 * n - 1) ^ (3 * n ^ 2 + u))) := by
        have hEq :
            4 * 2 ^ (3 * n ^ 2 + u) *
              UniformFirstHit.survivalNumerator
                (grantDrainEntranceNext ring fresh update)
                GrantDrainEntranceDone (grantDrainEntranceInitial ring s)
                (3 * n ^ 2 + u) =
            2 * (2 ^ ((3 * n ^ 2 + u) + 1) *
              UniformFirstHit.survivalNumerator
                (grantDrainEntranceNext ring fresh update)
                GrantDrainEntranceDone (grantDrainEntranceInitial ring s)
                (3 * n ^ 2 + u)) := by
          have hFour : (2 : Nat) * 2 = 4 := by decide
          have hPower :
              2 ^ ((3 * n ^ 2 + u) + 1) =
                2 ^ (3 * n ^ 2 + u) * 2 :=
            Nat.pow_succ 2 (3 * n ^ 2 + u)
          rw [hPower, ← hFour]
          ac_rfl
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
        ac_rfl
    _ ≤ n * (2 * n) ^ (3 * n ^ 2) * (2 * n - 1) ^ u :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left n hCut)

/-- The number of surviving words at t never exceeds n^t,
with no terminal-closure hypothesis. -/
private theorem grantDrainEntranceSurvivalCountCap
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
          ac_rfl

/-- The first T terms of the cost are at most T before scaling.
This pays for the entire first 3n² steps without a stochastic
estimate. -/
private theorem grantDrainEntranceCostTrivial
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
      have hs := grantDrainEntranceSurvivalCountCap next P x T
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

/-- Numerator of the exact geometric tail; b-r=1. This avoids
any Rat division or infinite series. -/
def grantDrainEntranceGeometricTail (b : Nat) : Nat → Nat
  | 0 => 0
  | u + 1 =>
      b * grantDrainEntranceGeometricTail b u +
        b * (b - 1) ^ u

/-- Finite telescope: the geometric tail has total scaled mass
strictly bounded by one more b-power. -/
theorem grantDrainEntranceGeometricTailIdentity
    (b : Nat) (hb : 1 ≤ b) :
    ∀ u : Nat,
      grantDrainEntranceGeometricTail b u +
        b * (b - 1) ^ u = b ^ (u + 1) := by
  intro u
  induction u with
  | zero =>
      simp [grantDrainEntranceGeometricTail, Nat.pow_succ]
  | succ u ih =>
      have hbase : 1 + (b - 1) = b := by omega
      have hstep :
          grantDrainEntranceGeometricTail b (u + 1) +
            b * (b - 1) ^ (u + 1) =
          b * (grantDrainEntranceGeometricTail b u +
            b * (b - 1) ^ u) := by
        change b * grantDrainEntranceGeometricTail b u +
            b * (b - 1) ^ u +
            b * ((b - 1) ^ u * (b - 1)) =
          b * (grantDrainEntranceGeometricTail b u +
            b * (b - 1) ^ u)
        calc
          b * grantDrainEntranceGeometricTail b u +
              b * (b - 1) ^ u +
              b * ((b - 1) ^ u * (b - 1)) =
            b * grantDrainEntranceGeometricTail b u +
              b * (b - 1) ^ u * (1 + (b - 1)) := by
                rw [Nat.mul_add, Nat.mul_one]
                ac_rfl
          _ = b * grantDrainEntranceGeometricTail b u +
                b * (b - 1) ^ u * b := by rw [hbase]
          _ = b * (grantDrainEntranceGeometricTail b u +
                b * (b - 1) ^ u) := by
                rw [Nat.mul_add]
                ac_rfl
      calc
        grantDrainEntranceGeometricTail b (u + 1) +
            b * (b - 1) ^ (u + 1) =
          b * (grantDrainEntranceGeometricTail b u +
            b * (b - 1) ^ u) := hstep
        _ = b * b ^ (u + 1) := by rw [ih]
        _ = b ^ ((u + 1) + 1) := by
          simp only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm,
            Nat.mul_left_comm]

/-- Cost through 3n²+u steps is first-phase trivial cost plus the
finite geometric tail, in entirely Nat-scaled form. -/
private theorem grantDrainEntranceCostAfterCutoff
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (hPB : PPlus ring s.native) :
    ∀ u : Nat,
      4 * 2 ^ (3 * n ^ 2 + u) *
        K2ArbitraryElimination.FiniteAccounting.costNumerator
          (grantDrainEntranceNext ring fresh update)
          GrantDrainEntranceDone (grantDrainEntranceInitial ring s)
          (3 * n ^ 2 + u) ≤
      4 * (3 * n ^ 2) * (2 * n) ^ (3 * n ^ 2 + u) +
        n * (2 * n) ^ (3 * n ^ 2) *
          grantDrainEntranceGeometricTail (2 * n) u := by
  intro u
  induction u with
  | zero =>
      have ht := grantDrainEntranceCostTrivial
        (grantDrainEntranceNext ring fresh update)
        GrantDrainEntranceDone (grantDrainEntranceInitial ring s)
        (3 * n ^ 2)
      have hscaled :
          4 * 2 ^ (3 * n ^ 2) *
            K2ArbitraryElimination.FiniteAccounting.costNumerator
              (grantDrainEntranceNext ring fresh update)
              GrantDrainEntranceDone (grantDrainEntranceInitial ring s)
              (3 * n ^ 2) ≤
          4 * (3 * n ^ 2) * (2 * n) ^ (3 * n ^ 2) := by
        calc
          _ ≤ 4 * 2 ^ (3 * n ^ 2) *
                ((3 * n ^ 2) * n ^ (3 * n ^ 2)) :=
            Nat.mul_le_mul_left _ ht
          _ = 4 * (3 * n ^ 2) * (2 * n) ^ (3 * n ^ 2) := by
            rw [Nat.mul_pow]
            ac_rfl
      simpa only [Nat.add_zero, grantDrainEntranceGeometricTail,
        Nat.mul_zero] using hscaled
  | succ u ih =>
      have hSurv := grantDrainEntranceSurvivalAfterCutoff
        ring hn fresh update s hPB u
      have hstep : 3 * n ^ 2 + (u + 1) =
          (3 * n ^ 2 + u) + 1 := by omega
      calc
        4 * 2 ^ (3 * n ^ 2 + (u + 1)) *
            K2ArbitraryElimination.FiniteAccounting.costNumerator
              (grantDrainEntranceNext ring fresh update)
              GrantDrainEntranceDone (grantDrainEntranceInitial ring s)
              (3 * n ^ 2 + (u + 1)) =
          (2 * n) *
            (4 * 2 ^ (3 * n ^ 2 + u) *
              K2ArbitraryElimination.FiniteAccounting.costNumerator
                (grantDrainEntranceNext ring fresh update)
                GrantDrainEntranceDone (grantDrainEntranceInitial ring s)
                (3 * n ^ 2 + u) +
             4 * 2 ^ (3 * n ^ 2 + u) *
              UniformFirstHit.survivalNumerator
                (grantDrainEntranceNext ring fresh update)
                GrantDrainEntranceDone (grantDrainEntranceInitial ring s)
                (3 * n ^ 2 + u)) := by
          rw [hstep, UniformFirstHit.costNumerator_succ_eq,
            show 2 ^ (3 * n ^ 2 + u + 1) = 2 ^ (3 * n ^ 2 + u) * 2 from
              Nat.pow_succ 2 (3 * n ^ 2 + u)]
          generalize 2 ^ (3 * n ^ 2 + u) = P
          generalize K2ArbitraryElimination.FiniteAccounting.costNumerator
              (grantDrainEntranceNext ring fresh update)
              GrantDrainEntranceDone (grantDrainEntranceInitial ring s)
              (3 * n ^ 2 + u) = C
          generalize UniformFirstHit.survivalNumerator
              (grantDrainEntranceNext ring fresh update)
              GrantDrainEntranceDone (grantDrainEntranceInitial ring s)
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
          ac_rfl

/-- R8d first-stage clock. The pure integer proof pays 3n² for
the early phase and at most n²/2 for the later geometric tail.
The resulting 3.5n² envelope is below the accepted 4n² ceiling. -/
theorem grantDrainEntranceFirstStageCost
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (hPB : PPlus ring s.native)
    (T : Nat) :
    K2ArbitraryElimination.FiniteAccounting.costNumerator
      (grantDrainEntranceNext ring fresh update)
      GrantDrainEntranceDone (grantDrainEntranceInitial ring s) T ≤
        n ^ T * (4 * n ^ 2) := by
  by_cases hEarly : T ≤ 3 * n ^ 2
  · have hTriv := grantDrainEntranceCostTrivial
      (grantDrainEntranceNext ring fresh update)
      GrantDrainEntranceDone (grantDrainEntranceInitial ring s) T
    calc
      _ ≤ T * n ^ T := hTriv
      _ ≤ (4 * n ^ 2) * n ^ T :=
        Nat.mul_le_mul_right _ (by omega)
      _ = n ^ T * (4 * n ^ 2) := by ac_rfl
  · have hLong : 3 * n ^ 2 ≤ T := by omega
    obtain ⟨u, hu⟩ : ∃ u : Nat, T = 3 * n ^ 2 + u :=
      ⟨T - 3 * n ^ 2, by omega⟩
    subst T
    have hTail := grantDrainEntranceCostAfterCutoff
      ring hn fresh update s hPB u
    have hGeomId := grantDrainEntranceGeometricTailIdentity
      (2 * n) (by omega : 1 ≤ 2 * n) u
    have hGeom :
        grantDrainEntranceGeometricTail (2 * n) u ≤
          (2 * n) ^ (u + 1) := by omega
    have hPart : n * (2 * n) = 2 * n ^ 2 := by
      rw [Nat.pow_two]
      ac_rfl
    have hCoeff :
        4 * (3 * n ^ 2) + n * (2 * n) ≤ 16 * n ^ 2 := by
      rw [hPart]
      omega
    have hScaled :
        4 * 2 ^ (3 * n ^ 2 + u) *
          K2ArbitraryElimination.FiniteAccounting.costNumerator
            (grantDrainEntranceNext ring fresh update)
            GrantDrainEntranceDone (grantDrainEntranceInitial ring s)
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
      ac_rfl
    rw [hPowerEq] at hScaled
    have hPositive : 0 < 4 * 2 ^ (3 * n ^ 2 + u) := by
      have hp : 0 < 2 ^ (3 * n ^ 2 + u) :=
        Nat.pow_pos (by decide : 0 < (2 : Nat))
      omega
    have hCancel := Nat.le_of_mul_le_mul_left hScaled hPositive
    calc
      K2ArbitraryElimination.FiniteAccounting.costNumerator
          (grantDrainEntranceNext ring fresh update)
          GrantDrainEntranceDone (grantDrainEntranceInitial ring s)
          (3 * n ^ 2 + u) ≤
        4 * n ^ 2 * n ^ (3 * n ^ 2 + u) := hCancel
      _ = n ^ (3 * n ^ 2 + u) * (4 * n ^ 2) := by ac_rfl

end L3.GrantDrainEntrance




/-!
R8e second branch: native clean-sector entrance.

This section uses the exact source grantDrainStep and C_native.
It proves all-word preservation of the corrected paper BAD(ii)
absence, defines the remaining initial nonclean-DUMMY cohort,
and formalizes the scalar "zero after one in the follower suffix,
plus a ready-source mismatch" observer from tokens.tex:560-608.

A sound and complete DUMMY transport with its < n nominated-hit
quota, scalar drift on every native E/FIRE branch, and the final
4*n^2 first-hit bound are NOT proved here. No missing geometric
transition fact is replaced by an axiom or a named assumption.
-/

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared
open L3.RenewalReferenceClock
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- The paper's second-branch condition is about the ACTUAL native
configuration, not a frozen BANK ghost or a terminal observer. -/
def GrantDrainEntranceNoBadLive
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch) : Prop :=
  ∀ b : Fin n,
    ¬ SharedPaperNonleftmostLiveExact ring s.native b

/-- A clean-sector configuration is exactly the existing L3
C_native predicate: PPlus, at most one (LIVE or DUMMY) bullet
in each sector, complete zero trail, and 0*1* signal suffix.
The ready/no-bullet boundary condition is also included. -/
def GrantDrainEntranceClean
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch) : Prop :=
  C_native ring s.native

/-- The intermediate class reached after all nonclean dummy labels
have retired or become clean: one bullet per sector with its
full leader-to-bullet zero trail. The signal suffix may be dirty. -/
def GrantDrainEntranceZeroTrailFamily
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch) : Prop :=
  I ring s.native

theorem grantDrainEntranceCleanHasZeroTrail
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch)
    (h : GrantDrainEntranceClean ring s) :
    GrantDrainEntranceZeroTrailFamily ring s :=
  h.1

theorem grantDrainEntranceCleanHasPB
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch)
    (h : GrantDrainEntranceClean ring s) :
    PPlus ring s.native :=
  h.1.1

/-- An ordinary finite scheduler word on the ACTUAL grant-drain
source. The hostile update and fresh-request functions are unchanged. -/
def grantDrainEntrancePhysicalWord
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (word : List (Fin n)) : GrantDrainState n Scratch :=
  word.foldl (grantDrainStep ring fresh update) s

/-- The ghost-extended word projects to precisely the above
canonical physical word, without any alternate protocol dynamics. -/
theorem grantDrainEntrancePhysicalWordProjection
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    ∀ (word : List (Fin n)) (x : GrantDrainEntranceState n Scratch),
      (grantDrainEntranceRun ring fresh update x word).physical =
        grantDrainEntrancePhysicalWord ring fresh update
          x.physical word := by
  intro word
  induction word with
  | nil =>
      intro x
      rfl
  | cons e es ih =>
      intro x
      change
        (grantDrainEntranceRun ring fresh update
          (grantDrainEntranceNext ring fresh update x e) es).physical =
        grantDrainEntrancePhysicalWord ring fresh update
          (grantDrainStep ring fresh update x.physical e) es
      exact ih (grantDrainEntranceNext ring fresh update x e)

/-- The no-new-BAD(ii) theorem at the single-edge level now
gives permanence for *every* physical future word, including
FIRE and arbitrary hostile fresh requests. -/
theorem grantDrainEntranceNoBadLiveWord
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    ∀ (word : List (Fin n)) (s : GrantDrainState n Scratch),
      PPlus ring s.native →
      GrantDrainEntranceNoBadLive ring s →
      GrantDrainEntranceNoBadLive ring
        (grantDrainEntrancePhysicalWord ring fresh update s word) := by
  intro word
  induction word with
  | nil =>
      intro s hPB hNoBad
      exact hNoBad
  | cons e es ih =>
      intro s hPB hNoBad
      change GrantDrainEntranceNoBadLive ring
        (grantDrainEntrancePhysicalWord ring fresh update
          (grantDrainStep ring fresh update s e) es)
      have hPBNext : PPlus ring
          (grantDrainStep ring fresh update s e).native :=
        grantDrainStep_preserves_PPlus
          (by omega : 3 ≤ n) ring fresh update s e hPB
      have hNoBadNext :
          GrantDrainEntranceNoBadLive ring
            (grantDrainStep ring fresh update s e) :=
        grantDrainEntrancePhysicalNoBadNext
          ring hn fresh update s e hPB hNoBad
      exact ih (grantDrainStep ring fresh update s e)
        hPBNext hNoBadNext

/-- The same permanence theorem for the existing entrance ghost,
which lets R8e start from the R8d stopping cut. -/
theorem grantDrainEntranceNoBadLiveGhostWord
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (x : GrantDrainEntranceState n Scratch)
    (word : List (Fin n))
    (hPB : PPlus ring x.physical.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring x.physical) :
    GrantDrainEntranceNoBadLive ring
      (grantDrainEntranceRun ring fresh update x word).physical := by
  have hWord := grantDrainEntranceNoBadLiveWord
    ring hn fresh update word x.physical hPB hNoBad
  rw [grantDrainEntrancePhysicalWordProjection
    ring fresh update word x]
  exact hWord

/-- A bullet is clean when it is the earliest occupied site in its
nearest-leader sector and carries the zero-signal trail. This
observer does not assume singleton-sector uniqueness globally. -/
def GrantDrainEntranceBulletCleanAt
    {n : Nat}
    (ring : DirectedRing n)
    (N : Fin n → CertNative) (b : Fin n) : Prop :=
  HasBullet N b ∧
  ∃ p : Fin n,
    leaderSector ring N p b ∧
    (∀ a : Fin n, leaderSector ring N p a →
      HasBullet N a →
      PPL.cyclicOffset ring p b ≤ PPL.cyclicOffset ring p a) ∧
    signalTrail ring N p b

/-- The initial unclean cohort must be made of DUMMY bullets.
This is a real observer, not a claim that all its identities already
obey the paper's unproved transport and nominated-hit quota. -/
def GrantDrainEntranceUncleanDummyAt
    {n : Nat}
    (ring : DirectedRing n)
    (N : Fin n → CertNative) (b : Fin n) : Prop :=
  (N b).b = (1 : Fin 3) ∧
    ¬ GrantDrainEntranceBulletCleanAt ring N b

/-- One permanent initial site is the identity of each label.
An absent host is an unused label, not a newly created dummy. -/
structure GrantDrainEntranceDummyLabel (n : Nat) where
  identity : Fin n
  host : Option (Fin n)

/-- Exactly one label is seeded at each initially nonclean DUMMY.
No later identity can be allocated from this initial family. -/
noncomputable def grantDrainEntranceDummyInitial
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch)
    (i : Fin n) : GrantDrainEntranceDummyLabel n := by
  classical
  exact
    { identity := i
      host :=
        if GrantDrainEntranceUncleanDummyAt ring s.native i then
          some i else none }

theorem grantDrainEntranceDummyInitialHostIff
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch)
    (i : Fin n) :
    (grantDrainEntranceDummyInitial ring s i).host = some i ↔
      GrantDrainEntranceUncleanDummyAt ring s.native i := by
  classical
  unfold grantDrainEntranceDummyInitial
  by_cases h : GrantDrainEntranceUncleanDummyAt ring s.native i
  · simp [h]
  · simp [h]

/-- Every initially hosted label is for a genuine DUMMY, rather than
a LIVE or a newly born dummy. -/
theorem grantDrainEntranceDummyInitiallyDummy
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch)
    (i : Fin n)
    (h : (grantDrainEntranceDummyInitial ring s i).host = some i) :
    (s.native i).b = (1 : Fin 3) :=
  (grantDrainEntranceDummyInitialHostIff ring s i).mp h |>.1

/-- There are at most n initially hosted dummy labels; all later
accounting must use these immutable identities, not new bullets. -/
theorem grantDrainEntranceDummyInitialCountCap
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch) :
    (List.ofFn (fun i : Fin n =>
      if (grantDrainEntranceDummyInitial ring s i).host = some i
      then 1 else 0)).sum ≤ n := by
  classical
  calc
    (List.ofFn (fun i : Fin n =>
        if (grantDrainEntranceDummyInitial ring s i).host = some i
        then 1 else 0)).sum ≤
      (List.ofFn (fun _ : Fin n => 1)).sum :=
        ofFn_sum_le _ _ (fun i => by
          split <;> omega)
    _ = n := by simp [ofFn_sum_const]

/-- A follower in the suffix of a sector lies strictly beyond
EVERY bullet host in that same sector. In the intermediate class I
there is at most one bullet, so this is exactly the suffix to the
right of that unique bullet; in a bullet-free sector, it is the
whole follower interval. -/
def GrantDrainEntranceSignalSuffixSite
    {n : Nat}
    (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (p : Fin n) (d : Fin (n + 1)) (k : Fin n) : Prop :=
  sectorLength ring N p d ∧
  1 ≤ k.val ∧ k.val < d.val ∧
  (∀ h : Fin n, h.val < d.val →
    HasBullet N (PPL.shiftRight ring p h.val) → h.val < k.val)

/-- A counted zero: at this follower the signal is zero although
a strictly earlier follower in the SAME bullet-free suffix
already has signal one. Counting each site once matches the
paper's "zero to the right of the first one" statistic. -/
def GrantDrainEntranceCountedZero
    {n : Nat}
    (ring : DirectedRing n)
    (N : Fin n → CertNative) (v : Fin n) : Prop :=
  ∃ (p : Fin n) (d : Fin (n + 1)) (r k : Fin n),
    GrantDrainEntranceSignalSuffixSite ring N p d r ∧
    v = PPL.shiftRight ring p k.val ∧
    r.val < k.val ∧ k.val < d.val ∧
    (N (PPL.shiftRight ring p k.val)).sg = false ∧
    (N (PPL.shiftRight ring p r.val)).sg = true

/-- Ready-source anomaly: a bullet-free sector has a ready leader
but the first follower's signal is zero. The first follower is
counted only for this case, so the two defect types are disjoint
at that site. -/
def GrantDrainEntranceReadyMismatch
    {n : Nat}
    (ring : DirectedRing n)
    (N : Fin n → CertNative) (v : Fin n) : Prop :=
  ∃ (p : Fin n) (d : Fin (n + 1)),
    sectorLength ring N p d ∧
    1 < d.val ∧
    v = ring.rightNeighbor p ∧
    (∀ h : Fin n, h.val < d.val →
      ¬ HasBullet N (PPL.shiftRight ring p h.val)) ∧
    (N p).sg = true ∧ (N v).sg = false

def GrantDrainEntranceSignalDefect
    {n : Nat}
    (ring : DirectedRing n)
    (N : Fin n → CertNative) (v : Fin n) : Prop :=
  GrantDrainEntranceCountedZero ring N v ∨
    GrantDrainEntranceReadyMismatch ring N v

/-- The actual scalar signal-cleanup observer counts physical
follower sites with a zero-after-one suffix violation or the
ready-source first-follower anomaly. All quantities are Nat. -/
noncomputable def grantDrainEntranceSignalCleanupPotential
    {n : Nat}
    (ring : DirectedRing n)
    (N : Fin n → CertNative) : Nat := by
  classical
  exact (List.ofFn (fun v : Fin n =>
    if GrantDrainEntranceSignalDefect ring N v then 1 else 0)).sum

/-- Trivial but unconditional cardinality cap: one unit per
physical site. Sharpening this to n-2 in the intermediate class
is still part of the R8e signal-drift proof. -/
theorem grantDrainEntranceSignalCleanupPotentialLe
    {n : Nat}
    (ring : DirectedRing n)
    (N : Fin n → CertNative) :
    grantDrainEntranceSignalCleanupPotential ring N ≤ n := by
  classical
  unfold grantDrainEntranceSignalCleanupPotential
  calc
    (List.ofFn (fun v : Fin n =>
        if GrantDrainEntranceSignalDefect ring N v then 1 else 0)).sum ≤
      (List.ofFn (fun _ : Fin n => 1)).sum :=
      ofFn_sum_le _ _ (fun v => by
        split <;> omega)
    _ = n := by simp [ofFn_sum_const]

/-- A 0*1* suffix cannot contain an earlier one followed by a
later zero. This elementary statement is used for both sorts
of paper clean sectors (with or without a bullet). -/
private theorem grantDrainEntranceSuffixNoInversion
    {n : Nat}
    (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (p : Fin n) (lo hi : Nat)
    (hPattern : signalZeroStarOneStar ring N p lo hi)
    (r k : Fin n)
    (hLo : lo ≤ r.val) (hOrder : r.val < k.val)
    (hHi : k.val < hi)
    (hOne : (N (PPL.shiftRight ring p r.val)).sg = true)
    (hZero : (N (PPL.shiftRight ring p k.val)).sg = false) :
    False := by
  rcases hPattern with ⟨cut, hLower, hUpper, hZeros, hOnes⟩
  by_cases hBefore : r.val < cut.val
  · have hAt := hZeros r hLo hBefore
    rw [hOne] at hAt
    cases hAt
  · have hAt := hOnes k (by omega : cut.val ≤ k.val) hHi
    rw [hZero] at hAt
    cases hAt

theorem grantDrainEntranceCleanNoCountedZero
    {n : Nat}
    (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (hClean : C_native ring N)
    (v : Fin n) :
    ¬ GrantDrainEntranceCountedZero ring N v := by
  intro hDefect
  rcases hDefect with
    ⟨p, d, r, k, hSuffixSite, hSite, hOrder, hKlt, hZero, hOne⟩
  obtain ⟨hSector, hRpos, hRlt, hAfterBullet⟩ := hSuffixSite
  have hCase := hClean.2 p d hSector
  rcases hCase with hBullet | hNoBullet
  · obtain ⟨h, hHlt, hOccupied, hTrail, hPattern⟩ := hBullet
    have hBefore : h.val < r.val :=
      hAfterBullet h hHlt hOccupied
    exact grantDrainEntranceSuffixNoInversion ring N p
      (h.val + 1) d.val hPattern r k
      (by omega) hOrder hKlt hOne hZero
  · obtain ⟨hEmpty, hPattern, hReady⟩ := hNoBullet
    exact grantDrainEntranceSuffixNoInversion ring N p
      1 d.val hPattern r k hRpos hOrder hKlt hOne hZero

theorem grantDrainEntranceCleanNoReadyMismatch
    {n : Nat}
    (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (hClean : C_native ring N)
    (v : Fin n) :
    ¬ GrantDrainEntranceReadyMismatch ring N v := by
  intro hMismatch
  rcases hMismatch with
    ⟨p, d, hSector, hGap, hSite, hEmpty, hReady, hZero⟩
  have hCase := hClean.2 p d hSector
  rcases hCase with hBullet | hNoBullet
  · obtain ⟨h, hLt, hOccupied, hTrail, hPattern⟩ := hBullet
    exact (hEmpty h hLt) hOccupied
  · obtain ⟨hNoBullet, hPattern, hReadyCondition⟩ := hNoBullet
    have hN : 1 < n := by
      have hd := d.isLt
      omega
    have hOne :
        (N (PPL.shiftRight ring p 1)).sg = true := by
      have hAt := hReadyCondition hReady
        (⟨1, by omega⟩ : Fin n) (Nat.le_refl 1) hGap
      simpa only [] using hAt
    have hNeighbor :
        ring.rightNeighbor p = PPL.shiftRight ring p 1 := by
      apply Fin.ext
      rfl
    have hNew : (N v).sg = true := by
      rw [hSite, hNeighbor]
      exact hOne
    rw [hZero] at hNew
    cases hNew

theorem grantDrainEntranceCleanNoSignalDefect
    {n : Nat}
    (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (hClean : C_native ring N)
    (v : Fin n) :
    ¬ GrantDrainEntranceSignalDefect ring N v := by
  intro h
  rcases h with hz | hr
  · exact grantDrainEntranceCleanNoCountedZero ring N hClean v hz
  · exact grantDrainEntranceCleanNoReadyMismatch ring N hClean v hr

/-- One verified direction of the proposed scalar zero criterion:
all clean-sector configurations have zero cleanup potential. The
converse under I, monotonicity under native E/FIRE, and the
positive-edge drop still require actual source-row geometry. -/
theorem grantDrainEntranceCleanSignalPotentialZero
    {n : Nat}
    (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (hClean : C_native ring N) :
    grantDrainEntranceSignalCleanupPotential ring N = 0 := by
  classical
  unfold grantDrainEntranceSignalCleanupPotential
  have hpoint (v : Fin n) :
      (if GrantDrainEntranceSignalDefect ring N v then 1 else 0) =
        (0 : Nat) := by
    simp [grantDrainEntranceCleanNoSignalDefect ring N hClean v]
  have hsum := ofFn_sum_eq
    (fun v : Fin n =>
      if GrantDrainEntranceSignalDefect ring N v then 1 else 0)
    (fun _ : Fin n => 0)
    hpoint
  rw [hsum, ofFn_sum_const, Nat.mul_zero]

/-- A generic cost theorem already in RenewalGrantStage
reduces the remaining scalar stage to physical all-edge drift.
This theorem does not assert that those source-level hypotheses
have been discharged. No artificial independent exponential
clocks are introduced. -/
theorem grantDrainEntranceSignalCostOfCertifiedDrift
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (Inv : GrantDrainState n Scratch → Prop)
    (chosen : GrantDrainState n Scratch → Fin n)
    (hclosed :
      ∀ s, Inv s → ¬ GrantDrainEntranceClean ring s →
        ∀ e, Inv (grantDrainStep ring fresh update s e))
    (hdrop :
      ∀ s, Inv s → ¬ GrantDrainEntranceClean ring s →
        grantDrainEntranceSignalCleanupPotential ring
            (grantDrainStep ring fresh update s (chosen s)).native + 1 ≤
          grantDrainEntranceSignalCleanupPotential ring s.native)
    (hnoninc :
      ∀ s, Inv s → ¬ GrantDrainEntranceClean ring s →
        ∀ e,
        grantDrainEntranceSignalCleanupPotential ring
            (grantDrainStep ring fresh update s e).native ≤
          grantDrainEntranceSignalCleanupPotential ring s.native)
    (s : GrantDrainState n Scratch) (hInv : Inv s) (T : Nat) :
    K2ArbitraryElimination.FiniteAccounting.costNumerator
      (grantDrainStep ring fresh update)
      (GrantDrainEntranceClean ring) s T ≤
      n ^ T * (n * n) := by
  have hCost := L3.Prob.costNumerator_le_of_nominated_edge_on
    (grantDrainStep ring fresh update)
    (GrantDrainEntranceClean ring) Inv
    (fun s => grantDrainEntranceSignalCleanupPotential ring s.native)
    chosen hclosed hdrop hnoninc s hInv T
  have hCap := grantDrainEntranceSignalCleanupPotentialLe
    ring s.native
  calc
    K2ArbitraryElimination.FiniteAccounting.costNumerator
        (grantDrainStep ring fresh update)
        (GrantDrainEntranceClean ring) s T ≤
      n ^ T * (n *
        grantDrainEntranceSignalCleanupPotential ring s.native) := hCost
    _ ≤ n ^ T * (n * n) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hCap)

end L3.GrantDrainEntrance


/-!
R8f. Source-level pieces of the Appendix D.5
zero-trail signal-potential proof.

This section intentionally does NOT assert the five global
potential obligations without a proof. The native transition is
the actual grantDrainStep, with all hostile fresh-request and
scratch choices left unrestricted. The two easy forward-closure
factors and exact E/FIRE branch partition are discharged below.
-/

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared
open L3.RenewalReferenceClock
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- The requested post-bad-LIVE intermediate class. No new
physical state or transition is added; the second conjunct
is exactly I, including PPlus, one bullet per sector and
its leader-to-bullet zero trail. -/
def GrantDrainEntranceIntermediateZ
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch) : Prop :=
  GrantDrainEntranceNoBadLive ring s ∧
    GrantDrainEntranceZeroTrailFamily ring s

theorem grantDrainEntranceIntermediateZHasPPlus
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch)
    (hz : GrantDrainEntranceIntermediateZ ring s) :
    PPlus ring s.native := by
  exact hz.2.1

/-- The non-bad-LIVE half of forward closure is proved on every
real scheduler edge, even if FIRE and new requests intervene. -/
theorem grantDrainEntranceIntermediateZNoBadNext
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hz : GrantDrainEntranceIntermediateZ ring s) :
    GrantDrainEntranceNoBadLive ring
      (grantDrainStep ring fresh update s e) := by
  exact grantDrainEntrancePhysicalNoBadNext ring hn
    fresh update s e hz.2.1 hz.1

/-- The protected PPlus half of I is already forward closed.
The remaining one-bullet/zero-trail clauses of I are NOT
derived from PPlus alone. -/
theorem grantDrainEntranceIntermediateZPPlusNext
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hz : GrantDrainEntranceIntermediateZ ring s) :
    PPlus ring (grantDrainStep ring fresh update s e).native := by
  exact grantDrainStep_preserves_PPlus (by omega : 3 ≤ n)
    ring fresh update s e hz.2.1

theorem grantDrainEntranceIntermediateZForwardEnvelope
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hz : GrantDrainEntranceIntermediateZ ring s) :
    GrantDrainEntranceNoBadLive ring
      (grantDrainStep ring fresh update s e) ∧
    PPlus ring (grantDrainStep ring fresh update s e).native := by
  exact ⟨grantDrainEntranceIntermediateZNoBadNext
    ring hn fresh update s e hz,
    grantDrainEntranceIntermediateZPPlusNext
      ring hn fresh update s e hz⟩

/-- The physical native projection depends only on the OLD
native E and selected FIRE, not on scratch or newly chosen
requests. This is a definitional projection of the actual
reference step. -/
theorem grantDrainEntranceNativeOwnerExact
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n) :
    (grantDrainStep ring fresh update s e).native =
      grantDrainNativeNext ring s e := by
  rfl

/-- E alone or E followed by a birth at one of the two actual
endpoints: this exhausts F0/F1/F2, with no invented FIRE row.
The cross case is an initiator birth. -/
theorem grantDrainEntranceNativeOwnerCases
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
  change grantDrainNativeNext ring s e =
      nativeE ring s.native e ∨
    grantDrainNativeNext ring s e =
      canonicalBirth (nativeE ring s.native e) e ∨
    grantDrainNativeNext ring s e =
      canonicalBirth (nativeE ring s.native e)
        (ring.rightNeighbor e)
  cases hf : grantDrainSelect ring s e with
  | none =>
      simp [grantDrainNativeNext, hf]
  | leftLocal =>
      simp [grantDrainNativeNext, hf]
  | rightLocal =>
      simp [grantDrainNativeNext, hf]
  | cross =>
      simp [grantDrainNativeNext, hf]

/-- The existing clean => zero implication gives the
strictly positive => nonclean direction without any
hypothesis about a sector decomposition. This is not the
requested converse zero => clean. -/
theorem grantDrainEntranceSignalPositiveNotClean
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (hp : 0 <
      grantDrainEntranceSignalCleanupPotential ring s.native) :
    ¬ GrantDrainEntranceClean ring s := by
  intro hc
  have hzero := grantDrainEntranceCleanSignalPotentialZero
    ring s.native hc
  rw [hzero] at hp
  exact Nat.not_lt_zero 0 hp

/-- A ready leader serving its first empty, zero-signal follower
has the literal native E row: the leader loses readiness and
sends a live bullet to that follower. The responder shield is
arbitrary. This is the nominated ready-source case in D.5. -/
theorem grantDrainEntranceReadySourceLiteralERow
    (x y : CertNative)
    (hxLeader : x.l = true)
    (hxReady : x.sg = true)
    (hyFollower : y.l = false)
    (hyEmpty : y.b = (0 : Fin 3))
    (hyZero : y.sg = false) :
    (certLiteralEPair x y).1.l = true ∧
    (certLiteralEPair x y).1.sg = false ∧
    (certLiteralEPair x y).2.b = (2 : Fin 3) ∧
    (certLiteralEPair x y).2.sg = false := by
  simp [certLiteralEPair, certFinThree, hxLeader,
    hxReady, hyFollower, hyEmpty, hyZero]

/-- In the ready-source case the post-E source remains a
leader and the post-E responder has a live bullet, so neither
endpoint is birth-eligible. Arbitrary OLD grant and request
bytes cannot select FIRE on this service. -/
theorem grantDrainEntranceReadySourceNoFire
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hxLeader : (s.native e).l = true)
    (hxReady : (s.native e).sg = true)
    (hyFollower : (s.native (ring.rightNeighbor e)).l = false)
    (hyEmpty : (s.native (ring.rightNeighbor e)).b =
      (0 : Fin 3))
    (hyZero : (s.native (ring.rightNeighbor e)).sg = false) :
    grantDrainSelect ring s e = .none := by
  have hpair := grantDrainEntranceReadySourceLiteralERow
    (s.native e) (s.native (ring.rightNeighbor e))
    hxLeader hxReady hyFollower hyEmpty hyZero
  have hsource :
      (nativeE ring s.native e e).l = true := by
    simpa [nativeE] using hpair.1
  have hdest :
      (nativeE ring s.native e (ring.rightNeighbor e)).b =
        (2 : Fin 3) := by
    simpa [nativeE, hne] using hpair.2.2.1
  have hsourceNotEligible :
      grantDrainEligible (nativeE ring s.native e) e = false := by
    simp [grantDrainEligible, hsource]
  have hdestNotEligible :
      grantDrainEligible (nativeE ring s.native e)
        (ring.rightNeighbor e) = false := by
    simp [grantDrainEligible, hdest]
  simp [grantDrainSelect, hsourceNotEligible, hdestNotEligible]

/-- The actual physical native transition on such a ready edge
is therefore exactly E, not an abstract no-birth surrogate. -/
theorem grantDrainEntranceReadySourceActualNativeE
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hxLeader : (s.native e).l = true)
    (hxReady : (s.native e).sg = true)
    (hyFollower : (s.native (ring.rightNeighbor e)).l = false)
    (hyEmpty : (s.native (ring.rightNeighbor e)).b =
      (0 : Fin 3))
    (hyZero : (s.native (ring.rightNeighbor e)).sg = false) :
    (grantDrainStep ring fresh update s e).native =
      nativeE ring s.native e := by
  have hf := grantDrainEntranceReadySourceNoFire
    ring s e hne hxLeader hxReady hyFollower hyEmpty hyZero
  change grantDrainNativeNext ring s e = nativeE ring s.native e
  simp [grantDrainNativeNext, hf]

end L3.GrantDrainEntrance

/-!
Additional local native-array facts for the I-factor.

The unrestricted all-edge closure of I is NOT established by
this section.  In particular, the sectorLength re-partitioning
arguments after a native leader death and after both canonical
birth locations have not yet been proved.  No assumption claiming
those properties is introduced as an axiom.
-/

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-- A genuine nonempty native bullet is either DUMMY or LIVE. -/
theorem grantDrainEntranceNonzeroBulletKind
    (b : Fin 3) (h : b ≠ (0 : Fin 3)) :
    b = (1 : Fin 3) ∨ b = (2 : Fin 3) := by
  rcases b with ⟨v, hv⟩
  rcases v with _ | _ | _ | v
  · exact False.elim (h rfl)
  · exact Or.inl rfl
  · exact Or.inr rfl
  · omega

/-- The distinct initiator and responder for the production n >= 5. -/
theorem grantDrainEntranceRightNeighborDistinct
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
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

/-- E on a moving, zero-signal follower bullet: the old source is
empty and zero, and the old empty follower acquires exactly that
bullet and becomes zero, regardless of its original signal/shield. -/
theorem grantDrainEntranceNonleaderBulletPairERow
    (x y : CertNative)
    (hxFollower : x.l = false)
    (hyFollower : y.l = false)
    (hxBullet : x.b ≠ (0 : Fin 3))
    (hyEmpty : y.b = (0 : Fin 3))
    (hxZero : x.sg = false) :
    (certLiteralEPair x y).1.b = (0 : Fin 3) ∧
    (certLiteralEPair x y).1.sg = false ∧
    (certLiteralEPair x y).2.b = x.b ∧
    (certLiteralEPair x y).2.sg = false := by
  rcases grantDrainEntranceNonzeroBulletKind x.b hxBullet with hb | hb
  · simp [certLiteralEPair, certFinThree,
      hxFollower, hyFollower, hb, hyEmpty, hxZero]
  · simp [certLiteralEPair, certFinThree,
      hxFollower, hyFollower, hb, hyEmpty, hxZero]

/-- The literal follower-bullet E row lifted to the native array. -/
theorem grantDrainEntranceNonleaderBulletNativeE
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hxFollower : (N e).l = false)
    (hyFollower : (N (ring.rightNeighbor e)).l = false)
    (hxBullet : (N e).b ≠ (0 : Fin 3))
    (hyEmpty : (N (ring.rightNeighbor e)).b = (0 : Fin 3))
    (hxZero : (N e).sg = false) :
    (nativeE ring N e e).b = (0 : Fin 3) ∧
    (nativeE ring N e e).sg = false ∧
    (nativeE ring N e (ring.rightNeighbor e)).b = (N e).b ∧
    (nativeE ring N e (ring.rightNeighbor e)).sg = false := by
  have hp := grantDrainEntranceNonleaderBulletPairERow
    (N e) (N (ring.rightNeighbor e))
    hxFollower hyFollower hxBullet hyEmpty hxZero
  have hne := grantDrainEntranceRightNeighborDistinct ring hn e
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [nativeE] using hp.1
  · simpa [nativeE] using hp.2.1
  · simpa [nativeE, hne] using hp.2.2.1
  · simpa [nativeE, hne] using hp.2.2.2

/-- A moving follower bullet cannot turn an OLD zero signal into
one at any site.  At the responder E may also clear an OLD one. -/
theorem grantDrainEntranceNonleaderBulletNativeEZeroPreserved
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hxFollower : (N e).l = false)
    (hyFollower : (N (ring.rightNeighbor e)).l = false)
    (hxBullet : (N e).b ≠ (0 : Fin 3))
    (hyEmpty : (N (ring.rightNeighbor e)).b = (0 : Fin 3))
    (hxZero : (N e).sg = false)
    (i : Fin n) (hOldZero : (N i).sg = false) :
    (nativeE ring N e i).sg = false := by
  have hm := grantDrainEntranceNonleaderBulletNativeE
    ring hn N e hxFollower hyFollower hxBullet hyEmpty hxZero
  by_cases he : i = e
  · subst i
    exact hm.2.1
  · by_cases hy : i = ring.rightNeighbor e
    · subst i
      exact hm.2.2.2
    · simpa [nativeE, he, hy] using hOldZero

/-- In a nonleader follower-bullet move, every pre-existing zero
arc remains zero, independently of its selected endpoints. -/
theorem grantDrainEntranceNonleaderBulletNativeEPreservesTrail
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hxFollower : (N e).l = false)
    (hyFollower : (N (ring.rightNeighbor e)).l = false)
    (hxBullet : (N e).b ≠ (0 : Fin 3))
    (hyEmpty : (N (ring.rightNeighbor e)).b = (0 : Fin 3))
    (hxZero : (N e).sg = false)
    (p b : Fin n) (hTrail : signalTrail ring N p b) :
    signalTrail ring (nativeE ring N e) p b := by
  intro k hk
  exact grantDrainEntranceNonleaderBulletNativeEZeroPreserved
    ring hn N e hxFollower hyFollower hxBullet hyEmpty hxZero
    (PPL.shiftRight ring p k.val) (hTrail k hk)

/-- If the post-E responder is ineligible, the OLD-selector
cannot execute a responder birth.  It may still birth at e. -/
theorem grantDrainEntranceResponderIneligibleNoRightFire
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch)
    (e : Fin n)
    (hIneligible : grantDrainEligible (nativeE ring s.native e)
      (ring.rightNeighbor e) = false) :
    grantDrainSelect ring s e ≠ .rightLocal := by
  simp [grantDrainSelect, hIneligible]
  split <;> (try split) <;> simp

/-- On the ACTUAL grantDrainStep a follower bullet enters the next
empty follower even if OLD grants cause an initiator birth.  A
responder birth is impossible because that endpoint contains the
transferred bullet after E.  Fresh request and scratch are arbitrary. -/
theorem grantDrainEntranceNonleaderBulletActualResponder
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hxFollower : (s.native e).l = false)
    (hyFollower : (s.native (ring.rightNeighbor e)).l = false)
    (hxBullet : (s.native e).b ≠ (0 : Fin 3))
    (hyEmpty : (s.native (ring.rightNeighbor e)).b = (0 : Fin 3))
    (hxZero : (s.native e).sg = false) :
    ((grantDrainStep ring fresh update s e).native
      (ring.rightNeighbor e)).b = (s.native e).b ∧
    ((grantDrainStep ring fresh update s e).native
      (ring.rightNeighbor e)).sg = false := by
  have hm := grantDrainEntranceNonleaderBulletNativeE
    ring hn s.native e hxFollower hyFollower hxBullet hyEmpty hxZero
  have hIneligible :
      grantDrainEligible (nativeE ring s.native e)
        (ring.rightNeighbor e) = false := by
    rcases grantDrainEntranceNonzeroBulletKind
      (s.native e).b hxBullet with hb | hb
    · simp [grantDrainEligible, hm.2.2.1, hb]
    · simp [grantDrainEligible, hm.2.2.1, hb]
  have hNoRight :=
    grantDrainEntranceResponderIneligibleNoRightFire
      ring s e hIneligible
  have hne := grantDrainEntranceRightNeighborDistinct ring hn e
  change
    (grantDrainNativeNext ring s e (ring.rightNeighbor e)).b =
        (s.native e).b ∧
    (grantDrainNativeNext ring s e (ring.rightNeighbor e)).sg = false
  cases hf : grantDrainSelect ring s e with
  | none =>
      simpa [grantDrainNativeNext, hf] using hm.2.2
  | leftLocal =>
      simpa [grantDrainNativeNext, hf, canonicalBirth, hne] using hm.2.2
  | rightLocal =>
      exact False.elim (hNoRight hf)
  | cross =>
      simpa [grantDrainNativeNext, hf, canonicalBirth, hne] using hm.2.2

/-- An unshielded leader receives a LIVE from a follower and loses
leadership in the E row.  Its new signal is zero even if it was
originally ready (which may also create its own DUMMY). -/
theorem grantDrainEntranceIncomingLivePairERow
    (x y : CertNative)
    (hxFollower : x.l = false)
    (hxLive : x.b = (2 : Fin 3))
    (hyLeader : y.l = true)
    (hyOpen : y.sh = false) :
    (certLiteralEPair x y).1.b = (0 : Fin 3) ∧
    (certLiteralEPair x y).2.l = false ∧
    (certLiteralEPair x y).2.sg = false := by
  cases hReady : y.sg <;>
    simp [certLiteralEPair, certFinThree,
      hxFollower, hxLive, hyLeader, hyOpen, hReady]

/-- The same incoming-LIVE leader-death row at native-array sites.
This is about E; a following responder birth could restore its
leader bit, so it is not mislabelled an unconditional physical death. -/
theorem grantDrainEntranceIncomingLiveNativeE
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hxFollower : (N e).l = false)
    (hxLive : (N e).b = (2 : Fin 3))
    (hyLeader : (N (ring.rightNeighbor e)).l = true)
    (hyOpen : (N (ring.rightNeighbor e)).sh = false) :
    (nativeE ring N e e).b = (0 : Fin 3) ∧
    (nativeE ring N e (ring.rightNeighbor e)).l = false ∧
    (nativeE ring N e (ring.rightNeighbor e)).sg = false := by
  have hp := grantDrainEntranceIncomingLivePairERow
    (N e) (N (ring.rightNeighbor e))
    hxFollower hxLive hyLeader hyOpen
  have hne := grantDrainEntranceRightNeighborDistinct ring hn e
  refine ⟨?_, ?_, ?_⟩
  · simpa [nativeE] using hp.1
  · simpa [nativeE, hne] using hp.2.1
  · simpa [nativeE, hne] using hp.2.2

/-- Outside the two selected physical sites, E has no native effect. -/
theorem grantDrainEntranceNativeEFrame
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (e i : Fin n)
    (he : i ≠ e) (hy : i ≠ ring.rightNeighbor e) :
    nativeE ring N e i = N i := by
  simp [nativeE, he, hy]

/-- FIRE overwrites precisely its chosen site, not another sector's
native entries. -/
theorem grantDrainEntranceCanonicalBirthFrame
    {n : Nat} (N : Fin n → CertNative) (z i : Fin n)
    (hi : i ≠ z) :
    canonicalBirth N z i = N i := by
  simp [canonicalBirth, hi]

/-- The literal born leader has no bullet and has signal zero. -/
theorem grantDrainEntranceCanonicalBirthAtSite
    {n : Nat} (N : Fin n → CertNative) (z : Fin n) :
    (canonicalBirth N z z).l = true ∧
    (canonicalBirth N z z).b = (0 : Fin 3) ∧
    (canonicalBirth N z z).sg = false := by
  simp [canonicalBirth, firedNative]

/-- A canonical birth only clears signals; it never changes an
old signal zero into one at any position. -/
theorem grantDrainEntranceCanonicalBirthPreservesZero
    {n : Nat} (N : Fin n → CertNative) (z i : Fin n)
    (hOldZero : (N i).sg = false) :
    (canonicalBirth N z i).sg = false := by
  by_cases he : i = z
  · subst i
    simp [canonicalBirth, firedNative]
  · simpa [canonicalBirth, he] using hOldZero

/-- Any old zero trail remains zero after either initiator or
responder birth.  The changed sector endpoints still need
a separate sectorLength proof. -/
theorem grantDrainEntranceCanonicalBirthPreservesTrail
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (z p b : Fin n)
    (hTrail : signalTrail ring N p b) :
    signalTrail ring (canonicalBirth N z) p b := by
  intro k hk
  exact grantDrainEntranceCanonicalBirthPreservesZero
    N z (PPL.shiftRight ring p k.val) (hTrail k hk)

/-- Canonical birth allocates a leader, never a physical bullet. -/
theorem grantDrainEntranceCanonicalBirthNoNewBullets
    {n : Nat} (N : Fin n → CertNative) (z i : Fin n)
    (hBullet : HasBullet (canonicalBirth N z) i) :
    HasBullet N i := by
  by_cases he : i = z
  · subst i
    have hZero : (canonicalBirth N z z).b = (0 : Fin 3) := by
      simp [canonicalBirth, firedNative]
    exact False.elim (hBullet hZero)
  · simpa [HasBullet, canonicalBirth, he] using hBullet

/-- Exact assembly of the already-proved no-BAD and PB factors
with the three still-required independent native I obligations.
This theorem is conditional, NOT the requested unconditional
I-factor closure. -/
theorem grantDrainEntranceIntermediateZNextFromNativeCases
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hz : GrantDrainEntranceIntermediateZ ring s)
    (hE : I ring (nativeE ring s.native e))
    (hSourceBirth :
      I ring (canonicalBirth (nativeE ring s.native e) e))
    (hResponderBirth :
      I ring (canonicalBirth (nativeE ring s.native e)
        (ring.rightNeighbor e))) :
    GrantDrainEntranceIntermediateZ ring
      (grantDrainStep ring fresh update s e) := by
  constructor
  · exact grantDrainEntranceIntermediateZNoBadNext
      ring hn fresh update s e hz
  · change I ring (grantDrainStep ring fresh update s e).native
    rcases grantDrainEntranceNativeOwnerCases
      ring fresh update s e with hNative | hLeft | hRight
    · rw [hNative]
      exact hE
    · rw [hLeft]
      exact hSourceBirth
    · rw [hRight]
      exact hResponderBirth

/-- A genuine closed subcase: with a unique leader, fully clean
native word and no selected FIRE, the existing singleton-E
theorem proves all of I after the actual grant-drain step. -/
theorem grantDrainEntranceIntermediateZSingletonCleanNoFire
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hSingle : OneNativeLeader s.native)
    (hClean : C_native ring s.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring s)
    (hNoFire : grantDrainSelect ring s e = .none) :
    GrantDrainEntranceIntermediateZ ring
      (grantDrainStep ring fresh update s e) := by
  constructor
  · exact grantDrainEntrancePhysicalNoBadNext
      ring hn fresh update s e hClean.1.1 hNoBad
  · change I ring (grantDrainStep ring fresh update s e).native
    have hNative :
        (grantDrainStep ring fresh update s e).native =
          nativeE ring s.native e := by
      change grantDrainNativeNext ring s e = nativeE ring s.native e
      simp [grantDrainNativeNext, hNoFire]
    rw [hNative]
    exact (nativeE_preserves_singleton_C_native
      hn ring s.native e ⟨hSingle, hClean⟩).2.1

/-- As a concrete corollary, complete grant extinction supplies
the no-FIRE premise automatically, without limiting requests. -/
theorem grantDrainEntranceIntermediateZSingletonCleanGrantFree
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hSingle : OneNativeLeader s.native)
    (hClean : C_native ring s.native)
    (hNoBad : GrantDrainEntranceNoBadLive ring s)
    (hFree : GrantFree s) :
    GrantDrainEntranceIntermediateZ ring
      (grantDrainStep ring fresh update s e) := by
  exact grantDrainEntranceIntermediateZSingletonCleanNoFire
    ring hn fresh update s e hSingle hClean hNoBad
    (grantDrainSelect_empty ring s e hFree)

end L3.GrantDrainEntrance

/-!
A bounded clockwise ahead scan and a one-way local
characterization of I, together with unconditional canonical-birth
closure for that local characterization.

This section does NOT claim
unrestricted native-E closure, nor I -> ILocal, which are the remaining
requirements for the requested all-edge I theorem.  No new axiom
or unproved theorem is inserted.
-/

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-- A structural rightward scan of exactly the available fuel.
At each site it includes its own bullet, and it may proceed to the
right only if the next site is a follower. The production scan uses
fuel n, which is enough to cover a sector on a rooted ring. -/
def grantDrainEntranceAheadFuel
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (v : Fin n) : Nat → Prop
  | 0 => False
  | fuel + 1 =>
      HasBullet N v ∨
        ((N (ring.rightNeighbor v)).l = false ∧
          grantDrainEntranceAheadFuel ring N
            (ring.rightNeighbor v) fuel)

/-- The requested local form: no next bullet in the current
follower run after an occupied site, and a zero signal at every
site from which a bullet is seen before the next leader. -/
def GrantDrainEntranceILocal
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) : Prop :=
  PPlus ring N ∧
    (∀ v : Fin n, HasBullet N v →
      (N (ring.rightNeighbor v)).l = false →
      ¬ grantDrainEntranceAheadFuel ring N
        (ring.rightNeighbor v) n) ∧
    (∀ v : Fin n,
      grantDrainEntranceAheadFuel ring N v n →
        (N v).sg = false)

/-- A bullet is visible with one unit of scan fuel. -/
theorem grantDrainEntranceAheadFuelBullet
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (v : Fin n)
    (fuel : Nat) (hb : HasBullet N v) :
    grantDrainEntranceAheadFuel ring N v (fuel + 1) := by
  exact Or.inl hb

/-- The step of the scan when the next site is a follower. -/
theorem grantDrainEntranceAheadFuelStep
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (v : Fin n)
    (fuel : Nat)
    (hFollower : (N (ring.rightNeighbor v)).l = false)
    (hAhead : grantDrainEntranceAheadFuel ring N
      (ring.rightNeighbor v) fuel) :
    grantDrainEntranceAheadFuel ring N v (fuel + 1) := by
  exact Or.inr ⟨hFollower, hAhead⟩

/-- A longer scan cannot lose a witness. -/
theorem grantDrainEntranceAheadFuelMonotone
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) :
    ∀ (fuel cap : Nat) (v : Fin n), fuel ≤ cap →
      grantDrainEntranceAheadFuel ring N v fuel →
      grantDrainEntranceAheadFuel ring N v cap := by
  intro fuel
  induction fuel with
  | zero =>
      intro cap v hCap hAhead
      change False at hAhead
      exact False.elim hAhead
  | succ fuel ih =>
      intro cap v hCap hAhead
      cases cap with
      | zero =>
          omega
      | succ cap =>
          change HasBullet N v ∨
            ((N (ring.rightNeighbor v)).l = false ∧
              grantDrainEntranceAheadFuel ring N
                (ring.rightNeighbor v) fuel) at hAhead
          rcases hAhead with hBullet | hTail
          · exact Or.inl hBullet
          · exact Or.inr
              ⟨hTail.1,
                ih cap (ring.rightNeighbor v) (by omega) hTail.2⟩

/-- Immediate leader barriers stop the scan if the current site
does not contain a bullet. -/
theorem grantDrainEntranceAheadFuelLeaderBarrier
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (v : Fin n) (fuel : Nat)
    (hEmpty : ¬ HasBullet N v)
    (hLeader : (N (ring.rightNeighbor v)).l = true) :
    ¬ grantDrainEntranceAheadFuel ring N v (fuel + 1) := by
  intro hAhead
  change HasBullet N v ∨
    ((N (ring.rightNeighbor v)).l = false ∧
      grantDrainEntranceAheadFuel ring N
        (ring.rightNeighbor v) fuel) at hAhead
  rcases hAhead with hBullet | hTail
  · exact hEmpty hBullet
  · have hFalse : true = false := hLeader.symm.trans hTail.1
    cases hFalse

/-- The actual clockwise successor equals a one-step shift.
This is cyclic, including the wraparound edge. -/
private theorem grantDrainEntranceArcShiftRightAdd
    {n : Nat} (ring : DirectedRing n)
    (p : Fin n) (a b : Nat) :
    PPL.shiftRight ring (PPL.shiftRight ring p a) b =
      PPL.shiftRight ring p (a + b) := by
  apply Fin.ext
  change (((p.val + a) % n + b) % n) =
    (p.val + (a + b)) % n
  rw [Nat.mod_add_mod, Nat.add_assoc]

theorem grantDrainEntranceAheadShiftSucc
    {n : Nat} (ring : DirectedRing n)
    (p : Fin n) (k : Nat) :
    ring.rightNeighbor (PPL.shiftRight ring p k) =
      PPL.shiftRight ring p (k + 1) := by
  calc
    ring.rightNeighbor (PPL.shiftRight ring p k) =
        PPL.shiftRight ring (PPL.shiftRight ring p k) 1 := by
          rfl
    _ = PPL.shiftRight ring p (k + 1) :=
      grantDrainEntranceArcShiftRightAdd ring p k 1

/-- A sector bullet at offset a is visible, with at most n scan
steps, at EVERY earlier offset k in its own sector, including
the sector leader at offset zero.  No global leader-search lemma
is needed in this direction. -/
theorem grantDrainEntranceAheadSectorEarlier
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (p : Fin n) (d : Fin (n + 1))
    (hSector : sectorLength ring N p d)
    (a k : Fin n)
    (ha : a.val < d.val) (hk : k.val ≤ a.val)
    (hBullet : HasBullet N (PPL.shiftRight ring p a.val)) :
    grantDrainEntranceAheadFuel ring N
      (PPL.shiftRight ring p k.val) n := by
  have hArc : ∀ t : Nat, t ≤ a.val →
      grantDrainEntranceAheadFuel ring N
        (PPL.shiftRight ring p (a.val - t)) (t + 1) := by
    intro t
    induction t with
    | zero =>
        intro ht
        change grantDrainEntranceAheadFuel ring N
          (PPL.shiftRight ring p a.val) 1
        exact Or.inl hBullet
    | succ t ih =>
        intro ht
        have htOld : t ≤ a.val := by omega
        have hPos : 0 < a.val - t := by omega
        have hLt : a.val - t < d.val := by omega
        have hNextFollower :
            (N (PPL.shiftRight ring p (a.val - t))).l =
              false := by
          exact hSector.2.2.2
            (⟨a.val - t, by omega⟩ : Fin n) hPos hLt
        have hNextSite :
            ring.rightNeighbor
              (PPL.shiftRight ring p (a.val - (t + 1))) =
              PPL.shiftRight ring p (a.val - t) := by
          calc
            _ = PPL.shiftRight ring p
                  ((a.val - (t + 1)) + 1) :=
              grantDrainEntranceAheadShiftSucc
                ring p (a.val - (t + 1))
            _ = PPL.shiftRight ring p (a.val - t) := by
              congr 1
              omega
        have hFollower :
            (N (ring.rightNeighbor
              (PPL.shiftRight ring p
                (a.val - (t + 1))))).l = false := by
          rw [hNextSite]
          exact hNextFollower
        have hAheadNext :
            grantDrainEntranceAheadFuel ring N
              (ring.rightNeighbor
                (PPL.shiftRight ring p
                  (a.val - (t + 1)))) (t + 1) := by
          rw [hNextSite]
          exact ih htOld
        exact grantDrainEntranceAheadFuelStep ring N
          (PPL.shiftRight ring p (a.val - (t + 1)))
          (t + 1) hFollower hAheadNext
  have hAt :
      grantDrainEntranceAheadFuel ring N
        (PPL.shiftRight ring p k.val)
        (a.val - k.val + 1) := by
    have hAux := hArc (a.val - k.val) (by omega)
    have hSame : a.val - (a.val - k.val) = k.val := by
      omega
    rw [hSame] at hAux
    exact hAux
  exact grantDrainEntranceAheadFuelMonotone ring N
    (a.val - k.val + 1) n
    (PPL.shiftRight ring p k.val) (by omega) hAt

/-- If a sector has two distinct bullets, the earlier occupied
site sees the later bullet strictly ahead with no leader barrier.
This contradicts the first clause of ILocal. -/
private theorem grantDrainEntranceILocalNoOrderedSectorBullets
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (hLocal : GrantDrainEntranceILocal ring N)
    (p : Fin n) (d : Fin (n + 1))
    (hSector : sectorLength ring N p d)
    (a b : Fin n)
    (hab : a.val < b.val) (hb : b.val < d.val)
    (hA : HasBullet N (PPL.shiftRight ring p a.val))
    (hB : HasBullet N (PPL.shiftRight ring p b.val)) :
    False := by
  have hFollower :
      (N (ring.rightNeighbor
        (PPL.shiftRight ring p a.val))).l = false := by
    rw [grantDrainEntranceAheadShiftSucc ring p a.val]
    exact hSector.2.2.2
      (⟨a.val + 1, by omega⟩ : Fin n)
      (Nat.succ_pos a.val) (Nat.lt_of_le_of_lt hab hb)
  have hAhead :
      grantDrainEntranceAheadFuel ring N
        (ring.rightNeighbor (PPL.shiftRight ring p a.val)) n := by
    rw [grantDrainEntranceAheadShiftSucc ring p a.val]
    exact grantDrainEntranceAheadSectorEarlier
      ring N p d hSector b
        (⟨a.val + 1, by omega⟩ : Fin n)
        hb hab hB
  exact (hLocal.2.1 (PPL.shiftRight ring p a.val)
    hA hFollower) hAhead

/-- The local forward-ahead predicate implies the COMPLETE
sectorLength-indexed I, not just its zero-trail half.
This is unconditional and works for every rooted ring size. -/
theorem grantDrainEntranceILocalImpliesI
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (hLocal : GrantDrainEntranceILocal ring N) :
    I ring N := by
  refine ⟨hLocal.1, ?_⟩
  intro p d hSector
  constructor
  · intro a b ha hb hA hB
    by_cases heq : a = b
    · exact heq
    · have hOrder : a.val < b.val ∨ b.val < a.val := by
        have hDiff : a.val ≠ b.val := by
          intro hEqVal
          exact heq (Fin.ext hEqVal)
        omega
      rcases hOrder with hab | hba
      · exact False.elim
          (grantDrainEntranceILocalNoOrderedSectorBullets
            ring N hLocal p d hSector a b hab hb hA hB)
      · exact False.elim
          (grantDrainEntranceILocalNoOrderedSectorBullets
            ring N hLocal p d hSector b a hba ha hB hA)
  · intro a ha hBullet k hk
    exact hLocal.2.2 (PPL.shiftRight ring p k.val)
      (grantDrainEntranceAheadSectorEarlier
        ring N p d hSector a k ha hk hBullet)

/-- Any present bullet is under a zero signal in the local domain.
This follows from the bounded scan, not from a postulated trail. -/
theorem grantDrainEntranceILocalBulletSignalZero
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (hLocal : GrantDrainEntranceILocal ring N)
    (v : Fin n) (hBullet : HasBullet N v) :
    (N v).sg = false := by
  have hOne : grantDrainEntranceAheadFuel ring N v 1 :=
    grantDrainEntranceAheadFuelBullet ring N v 0 hBullet
  have hAhead := grantDrainEntranceAheadFuelMonotone
    ring N 1 n v ring.hn hOne
  exact hLocal.2.2 v hAhead

/-- A ready site cannot see a bullet in its clockwise follower run. -/
theorem grantDrainEntranceILocalReadyNoAhead
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (hLocal : GrantDrainEntranceILocal ring N)
    (v : Fin n)
    (hReady : (N v).sg = true) :
    ¬ grantDrainEntranceAheadFuel ring N v n := by
  intro hAhead
  have hZero := hLocal.2.2 v hAhead
  have hImpossible : true = false := hReady.symm.trans hZero
  cases hImpossible

/-- Canonical birth only creates a leader; therefore a new
follower was already a follower in the old native array. -/
theorem grantDrainEntranceCanonicalBirthFollowerBackward
    {n : Nat} (N : Fin n → CertNative)
    (z i : Fin n)
    (hFollower : (canonicalBirth N z i).l = false) :
    (N i).l = false := by
  by_cases hi : i = z
  · subst i
    simp [canonicalBirth, firedNative] at hFollower
  · simpa [canonicalBirth, hi] using hFollower

/-- Every ahead witness after canonical birth was already present
before birth, at the same position and with the same fuel.
The induction tracks both absence of new bullets and absence of
new follower paths; no leader-search or sector bookkeeping is used. -/
theorem grantDrainEntranceAheadCanonicalBirthBackward
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (z : Fin n) :
    ∀ (fuel : Nat) (v : Fin n),
      grantDrainEntranceAheadFuel ring
        (canonicalBirth N z) v fuel →
      grantDrainEntranceAheadFuel ring N v fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro v hAhead
      change False at hAhead
      exact False.elim hAhead
  | succ fuel ih =>
      intro v hAhead
      change HasBullet (canonicalBirth N z) v ∨
        ((canonicalBirth N z (ring.rightNeighbor v)).l = false ∧
          grantDrainEntranceAheadFuel ring
            (canonicalBirth N z)
            (ring.rightNeighbor v) fuel) at hAhead
      rcases hAhead with hBullet | hTail
      · exact Or.inl
          (grantDrainEntranceCanonicalBirthNoNewBullets
            N z v hBullet)
      · exact Or.inr
          ⟨grantDrainEntranceCanonicalBirthFollowerBackward
              N z (ring.rightNeighbor v) hTail.1,
            ih (ring.rightNeighbor v) hTail.2⟩

/-- ILocal is genuinely all-site closed under canonical birth,
at an arbitrary site, even when its old signal and shield are
adversarial.  No-BAD-LIVE is not needed for this result. -/
theorem grantDrainEntranceILocalCanonicalBirth
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (z : Fin n)
    (hLocal : GrantDrainEntranceILocal ring N) :
    GrantDrainEntranceILocal ring (canonicalBirth N z) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨canonicalBirth_has_leader N z,
      canonicalBirth_preserves_P ring N z hLocal.1.2⟩
  · intro v hBullet hNextFollower hAhead
    have hOldBullet :=
      grantDrainEntranceCanonicalBirthNoNewBullets
        N z v hBullet
    have hOldFollower :=
      grantDrainEntranceCanonicalBirthFollowerBackward
        N z (ring.rightNeighbor v) hNextFollower
    have hOldAhead :=
      grantDrainEntranceAheadCanonicalBirthBackward
        ring N z n (ring.rightNeighbor v) hAhead
    exact (hLocal.2.1 v hOldBullet hOldFollower) hOldAhead
  · intro v hAhead
    have hOldAhead :=
      grantDrainEntranceAheadCanonicalBirthBackward
        ring N z n v hAhead
    exact grantDrainEntranceCanonicalBirthPreservesZero
      N z v (hLocal.2.2 v hOldAhead)

/-- F0/F1/F2 cannot break ILocal once the literal native E
has produced an ILocal array. This separates FIRE completely
from the still-open E preservation argument. -/
theorem grantDrainEntranceILocalPhysicalNextFromE
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hE : GrantDrainEntranceILocal ring
      (nativeE ring s.native e)) :
    GrantDrainEntranceILocal ring
      (grantDrainStep ring fresh update s e).native := by
  rcases grantDrainEntranceNativeOwnerCases
    ring fresh update s e with hNone | hSource | hResponder
  · rw [hNone]
    exact hE
  · rw [hSource]
    exact grantDrainEntranceILocalCanonicalBirth
      ring (nativeE ring s.native e) e hE
  · rw [hResponder]
    exact grantDrainEntranceILocalCanonicalBirth
      ring (nativeE ring s.native e)
        (ring.rightNeighbor e) hE

/-- The old no-BAD-LIVE theorem, the new local-to-global proof,
and the local-FIRE closure assemble to the exact required
IntermediateZ conclusion from ONE explicit, unproved E premise.
This is a conditional theorem, not the unconditional goal. -/
theorem grantDrainEntranceIntermediateZNextFromILocalE
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hz : GrantDrainEntranceIntermediateZ ring s)
    (hE : GrantDrainEntranceILocal ring
      (nativeE ring s.native e)) :
    GrantDrainEntranceIntermediateZ ring
      (grantDrainStep ring fresh update s e) := by
  constructor
  · exact grantDrainEntranceIntermediateZNoBadNext
      ring hn fresh update s e hz
  · change I ring (grantDrainStep ring fresh update s e).native
    exact grantDrainEntranceILocalImpliesI ring
      (grantDrainStep ring fresh update s e).native
      (grantDrainEntranceILocalPhysicalNextFromE
        ring fresh update s e hE)

end L3.GrantDrainEntrance

/-!
Bounded-ahead certificates, global sector coverage, the
reverse I-to-ILocal implication, and genuine local E cases.

The arbitrary nativeE preservation
of ILocal remains open here. In particular, the general
leader-deletion / merged-sector case is NOT proved. No declaration
asserting that goal, and no axiom, is inserted.
-/

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-- Shift from the right neighbor by k equals shift by k+1. -/
private theorem grantDrainEntranceAheadRightShift
    {n : Nat} (ring : DirectedRing n)
    (v : Fin n) (k : Nat) :
    PPL.shiftRight ring (ring.rightNeighbor v) k =
      PPL.shiftRight ring v (k + 1) := by
  change PPL.shiftRight ring (PPL.shiftRight ring v 1) k =
    PPL.shiftRight ring v (k + 1)
  rw [grantDrainEntranceArcShiftRightAdd]
  congr 1
  omega

/-- Extract an explicit witness from a bounded ahead scan. Every
strictly positive intermediate offset is a follower. In particular,
the witness never crosses a leader. -/
theorem grantDrainEntranceAheadFuelWitness
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) :
    ∀ (fuel : Nat) (v : Fin n),
      grantDrainEntranceAheadFuel ring N v fuel →
        ∃ t : Nat, t < fuel ∧
          HasBullet N (PPL.shiftRight ring v t) ∧
          (∀ j : Nat, 0 < j → j ≤ t →
            (N (PPL.shiftRight ring v j)).l = false) := by
  intro fuel
  induction fuel with
  | zero =>
      intro v hAhead
      change False at hAhead
      exact False.elim hAhead
  | succ fuel ih =>
      intro v hAhead
      change HasBullet N v ∨
        ((N (ring.rightNeighbor v)).l = false ∧
          grantDrainEntranceAheadFuel ring N
            (ring.rightNeighbor v) fuel) at hAhead
      rcases hAhead with hb | ht
      · refine ⟨0, Nat.zero_lt_succ fuel, ?_, ?_⟩
        · have hz : PPL.shiftRight ring v 0 = v := by
            apply Fin.ext
            simp [PPL.shiftRight, Nat.mod_eq_of_lt v.isLt]
          rw [hz]
          exact hb
        · intro j hj hjt
          omega
      · obtain ⟨t, hlt, hb, hpath⟩ :=
          ih (ring.rightNeighbor v) ht.2
        refine ⟨t + 1, by omega, ?_, ?_⟩
        · rw [grantDrainEntranceAheadRightShift ring v t] at hb
          exact hb
        · intro j hj hjt
          by_cases hjone : j = 1
          · have hsite :
                PPL.shiftRight ring v j = ring.rightNeighbor v := by
              rw [hjone]
              rfl
            rw [hsite]
            exact ht.1
          · have hpos : 0 < j - 1 := by omega
            have hle : j - 1 ≤ t := by omega
            have hprev := hpath (j - 1) hpos hle
            rw [grantDrainEntranceAheadRightShift ring v (j - 1)]
              at hprev
            have heq : (j - 1) + 1 = j := by omega
            rw [heq] at hprev
            exact hprev

/-- Coverage of every position by a genuine sector. The next
lemma derives this from a single leader rather than assuming it. -/
def GrantDrainEntranceSectorCover
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) : Prop :=
  ∀ v : Fin n,
    ∃ (p : Fin n) (d : Fin (n + 1)) (a : Fin n),
      sectorLength ring N p d ∧
      a.val < d.val ∧
      v = PPL.shiftRight ring p a.val

private theorem grantDrainEntranceAheadRightLeftInverse
    {n : Nat} (ring : DirectedRing n)
    (v : Fin n) (d : Nat) (hd : d < n) :
    PPL.shiftRight ring (PPL.shiftLeft ring v d) d = v := by
  apply Fin.ext
  change (((v.val + n - d % n) % n + d) % n) = v.val
  rw [Nat.mod_eq_of_lt hd, Nat.mod_add_mod]
  have hsum : v.val + n - d + d = v.val + n := by omega
  rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt v.isLt]

private theorem grantDrainEntranceAheadShiftFull
    {n : Nat} (ring : DirectedRing n) (p : Fin n) :
    PPL.shiftRight ring p n = p := by
  apply Fin.ext
  change (p.val + n) % n = p.val
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt p.isLt]

/-- Every site of a rooted finite ring belongs to a sectorLength
interval. Choose the nearest leader behind the site by a bounded
counterclockwise scan, then the first leader strictly clockwise of
that leader. The return at offset n makes the second scan nonempty.
The backward first-hit property proves the site precedes that
next leader. -/
theorem grantDrainEntranceSectorCoverOfRoot
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (hRoot : ∃ q : Fin n, (N q).l = true) :
    GrantDrainEntranceSectorCover ring N := by
  intro v
  obtain ⟨q, hq⟩ := hRoot
  have hqDistance : PPL.cyclicOffset ring q v < n :=
    grantDrainEntranceArcOffsetLt ring q v
  have hAtBack :
      (N (PPL.shiftLeft ring v
        (PPL.cyclicOffset ring q v))).l = true := by
    rw [grantDrainEntranceLeftOffset ring q v]
    exact hq
  have hBackExists :
      ∃ a : Nat,
        PPL.scanDistance
          (fun k : Nat => PPL.shiftLeft ring v k)
          (fun i : Fin n => (N i).l) n 0 = some a := by
    cases hs : PPL.scanDistance
        (fun k : Nat => PPL.shiftLeft ring v k)
        (fun i : Fin n => (N i).l) n 0 with
    | none =>
        have hmiss := grantDrainEntranceScanNoneInfo
          (fun k : Nat => PPL.shiftLeft ring v k)
          (fun i : Fin n => (N i).l) n 0 hs
          (PPL.cyclicOffset ring q v) (Nat.zero_le _)
          (by omega)
        rw [hAtBack] at hmiss
        cases hmiss
    | some a =>
        exact ⟨a, rfl⟩
  obtain ⟨a, haScan⟩ := hBackExists
  rcases grantDrainEntranceScanSomeInfo
    (fun k : Nat => PPL.shiftLeft ring v k)
    (fun i : Fin n => (N i).l) n 0 a haScan with
    ⟨haLower, haUpper, haLeader, haBefore⟩
  have haLt : a < n := by omega
  have hRightLeft :
      PPL.shiftRight ring (PPL.shiftLeft ring v a) a = v :=
    grantDrainEntranceAheadRightLeftInverse ring v a haLt
  have hFullLeader :
      (N (PPL.shiftRight ring
        (PPL.shiftLeft ring v a) n)).l = true := by
    rw [grantDrainEntranceAheadShiftFull]
    exact haLeader
  have hForwardExists :
      ∃ d : Nat,
        PPL.scanDistance
          (fun k : Nat =>
            PPL.shiftRight ring (PPL.shiftLeft ring v a) k)
          (fun i : Fin n => (N i).l) n 1 = some d := by
    cases hs : PPL.scanDistance
        (fun k : Nat =>
          PPL.shiftRight ring (PPL.shiftLeft ring v a) k)
        (fun i : Fin n => (N i).l) n 1 with
    | none =>
        have hmiss := grantDrainEntranceScanNoneInfo
          (fun k : Nat =>
            PPL.shiftRight ring (PPL.shiftLeft ring v a) k)
          (fun i : Fin n => (N i).l) n 1 hs
          n (by omega) (by omega)
        rw [hFullLeader] at hmiss
        cases hmiss
    | some d =>
        exact ⟨d, rfl⟩
  obtain ⟨d, hdScan⟩ := hForwardExists
  rcases grantDrainEntranceScanSomeInfo
    (fun k : Nat =>
      PPL.shiftRight ring (PPL.shiftLeft ring v a) k)
    (fun i : Fin n => (N i).l) n 1 d hdScan with
    ⟨hdLower, hdUpper, hdLeader, hdBefore⟩
  have hdLe : d ≤ n := by omega
  have hSector :
      sectorLength ring N
        (PPL.shiftLeft ring v a)
        (⟨d, by omega⟩ : Fin (n + 1)) := by
    refine ⟨hdLower, haLeader, hdLeader, ?_⟩
    intro k hk hkd
    exact hdBefore k.val (by omega) hkd
  have hInside : a < d := by
    by_cases hlt : a < d
    · exact hlt
    · have hda : d ≤ a := by omega
      have hBackIndex : a - d < a := by omega
      have hmiss := haBefore (a - d) (Nat.zero_le _) hBackIndex
      have hShift := grantDrainMarksArcShiftLeftRight ring
        (PPL.shiftLeft ring v a) a (a - d)
        (by omega) haLt
      rw [hRightLeft] at hShift
      have hsub : a - (a - d) = d := by omega
      rw [hsub] at hShift
      rw [hShift, hdLeader] at hmiss
      cases hmiss
  refine ⟨PPL.shiftLeft ring v a,
    ⟨d, by omega⟩, ⟨a, haLt⟩, hSector, hInside, ?_⟩
  exact hRightLeft.symm

/-- A bounded scan beginning at sector offset a cannot reach
beyond the sector's next leader: a crossing at d-a would violate
the follower-only condition in the witness. -/
private theorem grantDrainEntranceAheadSectorNoCross
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (p : Fin n) (d : Fin (n + 1))
    (hSector : sectorLength ring N p d)
    (a t : Nat) (ha : a < d.val)
    (hPath : ∀ j : Nat, 0 < j → j ≤ t →
      (N (PPL.shiftRight ring
        (PPL.shiftRight ring p a) j)).l = false) :
    a + t < d.val := by
  by_cases hInside : a + t < d.val
  · exact hInside
  · have hStep : 0 < d.val - a ∧ d.val - a ≤ t := by omega
    have hMiss := hPath (d.val - a) hStep.1 hStep.2
    have hCross :
        PPL.shiftRight ring
            (PPL.shiftRight ring p a) (d.val - a) =
          PPL.shiftRight ring p d.val := by
      rw [grantDrainEntranceArcShiftRightAdd]
      congr 1
      omega
    rw [hCross, hSector.2.2.1] at hMiss
    cases hMiss

/-- The reverse implication I -> ILocal, once rooted sector
coverage is explicitly available. The lemma above supplies
coverage on every PPlus configuration. -/
theorem grantDrainEntranceIImpliesILocalOfSectorCover
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (hI : I ring N)
    (hCover : GrantDrainEntranceSectorCover ring N) :
    GrantDrainEntranceILocal ring N := by
  refine ⟨hI.1, ?_, ?_⟩
  · intro v hBullet hNextFollower hAhead
    obtain ⟨p, d, a, hSector, ha, hv⟩ := hCover v
    have hRight :
        ring.rightNeighbor v =
          PPL.shiftRight ring p (a.val + 1) := by
      rw [hv]
      exact grantDrainEntranceAheadShiftSucc ring p a.val
    have hNextInside : a.val + 1 < d.val := by
      by_cases hlt : a.val + 1 < d.val
      · exact hlt
      · have heq : a.val + 1 = d.val := by omega
        rw [hRight, heq, hSector.2.2.1] at hNextFollower
        cases hNextFollower
    obtain ⟨t, ht, hLater, hPath⟩ :=
      grantDrainEntranceAheadFuelWitness ring N n
        (ring.rightNeighbor v) hAhead
    have hPathInSector : ∀ j : Nat, 0 < j → j ≤ t →
        (N (PPL.shiftRight ring
          (PPL.shiftRight ring p (a.val + 1)) j)).l =
            false := by
      intro j hj hjt
      have hAt := hPath j hj hjt
      rw [hRight] at hAt
      exact hAt
    have hWithin : a.val + 1 + t < d.val :=
      grantDrainEntranceAheadSectorNoCross ring N
        p d hSector (a.val + 1) t hNextInside hPathInSector
    have hFirst : HasBullet N
        (PPL.shiftRight ring p a.val) := by
      rw [← hv]
      exact hBullet
    have hSecond : HasBullet N
        (PPL.shiftRight ring p (a.val + 1 + t)) := by
      have hAt := hLater
      rw [hRight] at hAt
      rw [grantDrainEntranceArcShiftRightAdd] at hAt
      exact hAt
    have hEqual :
        a = (⟨a.val + 1 + t, by omega⟩ : Fin n) :=
      (hI.2 p d hSector).1
        a (⟨a.val + 1 + t, by omega⟩ : Fin n)
        ha hWithin hFirst hSecond
    have hValues := congrArg Fin.val hEqual
    change a.val = a.val + 1 + t at hValues
    omega
  · intro v hAhead
    obtain ⟨p, d, a, hSector, ha, hv⟩ := hCover v
    obtain ⟨t, ht, hBullet, hPath⟩ :=
      grantDrainEntranceAheadFuelWitness ring N n v hAhead
    have hPathInSector : ∀ j : Nat, 0 < j → j ≤ t →
        (N (PPL.shiftRight ring
          (PPL.shiftRight ring p a.val) j)).l = false := by
      intro j hj hjt
      have hAt := hPath j hj hjt
      rw [hv] at hAt
      exact hAt
    have hWithin : a.val + t < d.val :=
      grantDrainEntranceAheadSectorNoCross ring N
        p d hSector a.val t ha hPathInSector
    have hAtBullet : HasBullet N
        (PPL.shiftRight ring p (a.val + t)) := by
      have hAt := hBullet
      rw [hv] at hAt
      rw [grantDrainEntranceArcShiftRightAdd] at hAt
      exact hAt
    have hAtZero :
        (N (PPL.shiftRight ring p a.val)).sg = false :=
      (hI.2 p d hSector).2
        (⟨a.val + t, by omega⟩ : Fin n)
        hWithin hAtBullet a (Nat.le_add_right a.val t)
    rw [hv]
    exact hAtZero

/-- Full equivalence, using actual rooted sector coverage. -/
theorem grantDrainEntranceIffILocal
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) :
    I ring N ↔ GrantDrainEntranceILocal ring N := by
  constructor
  · intro hI
    exact grantDrainEntranceIImpliesILocalOfSectorCover
      ring N hI
      (grantDrainEntranceSectorCoverOfRoot ring N hI.1.1)
  · exact grantDrainEntranceILocalImpliesI ring N

/-- Two native arrays with identical leader and bullet fields
have precisely the same ahead scan at every fuel and every site. -/
theorem grantDrainEntranceAheadFuelUniformFrame
    {n : Nat} (ring : DirectedRing n)
    (M N : Fin n → CertNative)
    (hLeader : ∀ i : Fin n, (M i).l = (N i).l)
    (hBullet : ∀ i : Fin n, (M i).b = (N i).b) :
    ∀ (fuel : Nat) (v : Fin n),
      grantDrainEntranceAheadFuel ring M v fuel ↔
        grantDrainEntranceAheadFuel ring N v fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro v
      rfl
  | succ fuel ih =>
      intro v
      have hb : HasBullet M v ↔ HasBullet N v := by
        unfold HasBullet
        rw [hBullet v]
      have hl :
          (M (ring.rightNeighbor v)).l = false ↔
          (N (ring.rightNeighbor v)).l = false := by
        rw [hLeader (ring.rightNeighbor v)]
      have ht := ih (ring.rightNeighbor v)
      change
        (HasBullet M v ∨
          ((M (ring.rightNeighbor v)).l = false ∧
            grantDrainEntranceAheadFuel ring M
              (ring.rightNeighbor v) fuel)) ↔
        (HasBullet N v ∨
          ((N (ring.rightNeighbor v)).l = false ∧
            grantDrainEntranceAheadFuel ring N
              (ring.rightNeighbor v) fuel))
      constructor
      · intro h
        rcases h with hHere | hTail
        · exact Or.inl (hb.mp hHere)
        · exact Or.inr ⟨hl.mp hTail.1, ht.mp hTail.2⟩
      · intro h
        rcases h with hHere | hTail
        · exact Or.inl (hb.mpr hHere)
        · exact Or.inr ⟨hl.mpr hTail.1, ht.mpr hTail.2⟩

/-- Generic bounded prefix frame: equality of both native fields
at every inspected position (through the last follower guard)
is sufficient to preserve an ahead scan. -/
theorem grantDrainEntranceAheadFuelPrefixFrame
    {n : Nat} (ring : DirectedRing n)
    (M N : Fin n → CertNative) :
    ∀ (fuel : Nat) (v : Fin n),
      (∀ k : Nat, k ≤ fuel →
        (M (PPL.shiftRight ring v k)).b =
          (N (PPL.shiftRight ring v k)).b ∧
        (M (PPL.shiftRight ring v k)).l =
          (N (PPL.shiftRight ring v k)).l) →
      (grantDrainEntranceAheadFuel ring M v fuel ↔
        grantDrainEntranceAheadFuel ring N v fuel) := by
  intro fuel
  induction fuel with
  | zero =>
      intro v hFrame
      rfl
  | succ fuel ih =>
      intro v hFrame
      have hz : PPL.shiftRight ring v 0 = v := by
        apply Fin.ext
        simp [PPL.shiftRight, Nat.mod_eq_of_lt v.isLt]
      have hStart := hFrame 0 (Nat.zero_le _)
      rw [hz] at hStart
      have hNext := hFrame 1 (by omega)
      change
        (M (ring.rightNeighbor v)).b =
          (N (ring.rightNeighbor v)).b ∧
        (M (ring.rightNeighbor v)).l =
          (N (ring.rightNeighbor v)).l at hNext
      have hb : HasBullet M v ↔ HasBullet N v := by
        unfold HasBullet
        rw [hStart.1]
      have hl :
          (M (ring.rightNeighbor v)).l = false ↔
          (N (ring.rightNeighbor v)).l = false := by
        rw [hNext.2]
      have hSubFrame : ∀ k : Nat, k ≤ fuel →
          (M (PPL.shiftRight ring (ring.rightNeighbor v) k)).b =
            (N (PPL.shiftRight ring (ring.rightNeighbor v) k)).b ∧
          (M (PPL.shiftRight ring (ring.rightNeighbor v) k)).l =
            (N (PPL.shiftRight ring (ring.rightNeighbor v) k)).l := by
        intro k hk
        rw [grantDrainEntranceAheadRightShift ring v k]
        exact hFrame (k + 1) (by omega)
      have ht := ih (ring.rightNeighbor v) hSubFrame
      change
        (HasBullet M v ∨
          ((M (ring.rightNeighbor v)).l = false ∧
            grantDrainEntranceAheadFuel ring M
              (ring.rightNeighbor v) fuel)) ↔
        (HasBullet N v ∨
          ((N (ring.rightNeighbor v)).l = false ∧
            grantDrainEntranceAheadFuel ring N
              (ring.rightNeighbor v) fuel))
      constructor
      · intro h
        rcases h with hHere | hTail
        · exact Or.inl (hb.mp hHere)
        · exact Or.inr ⟨hl.mp hTail.1, ht.mp hTail.2⟩
      · intro h
        rcases h with hHere | hTail
        · exact Or.inl (hb.mpr hHere)
        · exact Or.inr ⟨hl.mpr hTail.1, ht.mpr hTail.2⟩

/-- Native E cannot alter a finite ahead scan whose inspected
clockwise prefix avoids both endpoints. This is a true frame
lemma; it does not pretend that a full n-scan avoids the edge. -/
theorem grantDrainEntranceAheadFuelNativeEFrame
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (e v : Fin n)
    (fuel : Nat)
    (hAvoid : ∀ k : Nat, k ≤ fuel →
      PPL.shiftRight ring v k ≠ e ∧
      PPL.shiftRight ring v k ≠ ring.rightNeighbor e) :
    grantDrainEntranceAheadFuel ring
        (nativeE ring N e) v fuel ↔
      grantDrainEntranceAheadFuel ring N v fuel := by
  apply grantDrainEntranceAheadFuelPrefixFrame
    ring (nativeE ring N e) N fuel v
  intro k hk
  have hSite := hAvoid k hk
  have hFrame := grantDrainEntranceNativeEFrame
    ring N e (PPL.shiftRight ring v k) hSite.1 hSite.2
  rw [hFrame]
  exact ⟨rfl, rfl⟩

/-- An ahead scan beginning at an empty site must use the
follower branch in its first step. -/
theorem grantDrainEntranceAheadFuelTailFromEmpty
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (v : Fin n) (fuel : Nat)
    (hEmpty : ¬ HasBullet N v)
    (hAhead : grantDrainEntranceAheadFuel ring N v (fuel + 1)) :
    (N (ring.rightNeighbor v)).l = false ∧
      grantDrainEntranceAheadFuel ring N
        (ring.rightNeighbor v) fuel := by
  change HasBullet N v ∨
    ((N (ring.rightNeighbor v)).l = false ∧
      grantDrainEntranceAheadFuel ring N
        (ring.rightNeighbor v) fuel) at hAhead
  rcases hAhead with hb | ht
  · exact False.elim (hEmpty hb)
  · exact ht

/-- Literal pure E row for two empty followers. Both leader and
bullet fields are fixed; only the initiator may copy the
responder signal. -/
theorem grantDrainEntranceFollowerEmptyPairERow
    (x y : CertNative)
    (hxLeader : x.l = false)
    (hyLeader : y.l = false)
    (hxEmpty : x.b = (0 : Fin 3))
    (hyEmpty : y.b = (0 : Fin 3)) :
    (certLiteralEPair x y).1.l = false ∧
    (certLiteralEPair x y).1.b = (0 : Fin 3) ∧
    (certLiteralEPair x y).2.l = false ∧
    (certLiteralEPair x y).2.b = (0 : Fin 3) ∧
    (certLiteralEPair x y).1.sg = (x.sg || y.sg) ∧
    (certLiteralEPair x y).2.sg = y.sg := by
  simp [certLiteralEPair, certFinThree,
    hxLeader, hyLeader, hxEmpty, hyEmpty]

/-- The full native-array facts, including the frame at every
off-edge site, for an empty-follower interaction. -/
theorem grantDrainEntranceFollowerEmptyNativeRows
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hxLeader : (N e).l = false)
    (hyLeader : (N (ring.rightNeighbor e)).l = false)
    (hxEmpty : (N e).b = (0 : Fin 3))
    (hyEmpty : (N (ring.rightNeighbor e)).b = (0 : Fin 3)) :
    (∀ i : Fin n,
      (nativeE ring N e i).l = (N i).l ∧
      (nativeE ring N e i).b = (N i).b) ∧
    (nativeE ring N e e).sg =
      ((N e).sg || (N (ring.rightNeighbor e)).sg) ∧
    (nativeE ring N e (ring.rightNeighbor e)).sg =
      (N (ring.rightNeighbor e)).sg := by
  have hPair := grantDrainEntranceFollowerEmptyPairERow
    (N e) (N (ring.rightNeighbor e))
    hxLeader hyLeader hxEmpty hyEmpty
  obtain ⟨hLX, hBX, hLY, hBY, hSX, hSY⟩ := hPair
  have hDistinct := grantDrainEntranceRightNeighborDistinct
    ring hn e
  refine ⟨?_, ?_, ?_⟩
  · intro i
    by_cases hi : i = e
    · subst i
      constructor
      · simpa [nativeE, hxLeader] using hLX
      · simpa [nativeE, hxEmpty] using hBX
    · by_cases hy : i = ring.rightNeighbor e
      · subst i
        constructor
        · simpa [nativeE, hDistinct, hyLeader] using hLY
        · simpa [nativeE, hDistinct, hyEmpty] using hBY
      · have hFrame := grantDrainEntranceNativeEFrame
          ring N e i hi hy
        rw [hFrame]
        exact ⟨rfl, rfl⟩
  · simpa [nativeE] using hSX
  · simpa [nativeE, hDistinct] using hSY

/-- A genuinely all-site E-closure subcase of ILocal. Two
empty followers cannot create bullets or leaders, and a copied
one at the initiator would contradict the old ahead-zero
condition at the responder. -/
theorem grantDrainEntranceILocalNativeEFollowerEmpty
    {n : Nat} (ring : DirectedRing n) (hn : 3 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hLocal : GrantDrainEntranceILocal ring N)
    (hxLeader : (N e).l = false)
    (hyLeader : (N (ring.rightNeighbor e)).l = false)
    (hxEmpty : (N e).b = (0 : Fin 3))
    (hyEmpty : (N (ring.rightNeighbor e)).b = (0 : Fin 3)) :
    GrantDrainEntranceILocal ring (nativeE ring N e) := by
  have hRows := grantDrainEntranceFollowerEmptyNativeRows
    ring (by omega : 2 ≤ n) N e
    hxLeader hyLeader hxEmpty hyEmpty
  have hAheadEq := grantDrainEntranceAheadFuelUniformFrame
    ring (nativeE ring N e) N
    (fun i => (hRows.1 i).1)
    (fun i => (hRows.1 i).2)
  refine ⟨nativeE_preserves_PPlus hn ring N e hLocal.1,
    ?_, ?_⟩
  · intro v hBullet hFollower hAhead
    have hOldBullet : HasBullet N v := by
      change (nativeE ring N e v).b ≠ (0 : Fin 3)
        at hBullet
      change (N v).b ≠ (0 : Fin 3)
      rw [← (hRows.1 v).2]
      exact hBullet
    have hOldFollower :
        (N (ring.rightNeighbor v)).l = false := by
      rw [← (hRows.1 (ring.rightNeighbor v)).1]
      exact hFollower
    exact hLocal.2.1 v hOldBullet hOldFollower
      ((hAheadEq n (ring.rightNeighbor v)).mp hAhead)
  · intro v hAhead
    have hOldAhead := (hAheadEq n v).mp hAhead
    have hOldZero := hLocal.2.2 v hOldAhead
    by_cases he : v = e
    · subst v
      have hEmptySource : ¬ HasBullet N e := by
        intro hBullet
        exact hBullet hxEmpty
      have hSpan : (n - 1) + 1 = n := by omega
      have hAtSucc :
          grantDrainEntranceAheadFuel ring N e
            ((n - 1) + 1) := by
        rw [hSpan]
        exact hOldAhead
      have hAtNext := grantDrainEntranceAheadFuelTailFromEmpty
        ring N e (n - 1) hEmptySource hAtSucc
      have hAheadRight :
          grantDrainEntranceAheadFuel ring N
            (ring.rightNeighbor e) n :=
        grantDrainEntranceAheadFuelMonotone
          ring N (n - 1) n (ring.rightNeighbor e)
          (by omega) hAtNext.2
      have hOldRightZero :=
        hLocal.2.2 (ring.rightNeighbor e) hAheadRight
      have hPairZero :
          ((N e).sg || (N (ring.rightNeighbor e)).sg) = false := by
        rw [hOldZero, hOldRightZero]
        rfl
      rw [hRows.2.1]
      exact hPairZero
    · by_cases hy : v = ring.rightNeighbor e
      · subst v
        rw [hRows.2.2]
        exact hOldZero
      · have hFrame := grantDrainEntranceNativeEFrame
          ring N e v he hy
        rw [hFrame]
        exact hOldZero

/-- A bullet already at an initiator excludes a second bullet at
its next follower, directly from the local uniqueness clause. -/
theorem grantDrainEntranceILocalFollowerBulletNextEmpty
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (e : Fin n)
    (hLocal : GrantDrainEntranceILocal ring N)
    (hBullet : HasBullet N e)
    (hFollower : (N (ring.rightNeighbor e)).l = false) :
    (N (ring.rightNeighbor e)).b = (0 : Fin 3) := by
  by_cases hEmpty :
      (N (ring.rightNeighbor e)).b = (0 : Fin 3)
  · exact hEmpty
  · have hAtNext :
        grantDrainEntranceAheadFuel ring N
          (ring.rightNeighbor e) 1 :=
      grantDrainEntranceAheadFuelBullet ring N
        (ring.rightNeighbor e) 0 hEmpty
    have hAhead :=
      grantDrainEntranceAheadFuelMonotone ring N
        1 n (ring.rightNeighbor e) ring.hn hAtNext
    exact False.elim ((hLocal.2.1 e hBullet hFollower) hAhead)

/-- Complete native source-to-responder transport under ILocal,
with no separately assumed responder emptiness or source zero. -/
theorem grantDrainEntranceILocalFollowerBulletNativeE
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hLocal : GrantDrainEntranceILocal ring N)
    (hxFollower : (N e).l = false)
    (hyFollower : (N (ring.rightNeighbor e)).l = false)
    (hxBullet : HasBullet N e) :
    (nativeE ring N e e).b = (0 : Fin 3) ∧
    (nativeE ring N e e).sg = false ∧
    (nativeE ring N e (ring.rightNeighbor e)).b = (N e).b ∧
    (nativeE ring N e (ring.rightNeighbor e)).sg = false := by
  have hEmpty :=
    grantDrainEntranceILocalFollowerBulletNextEmpty
      ring N e hLocal hxBullet hyFollower
  have hZero :=
    grantDrainEntranceILocalBulletSignalZero
      ring N hLocal e hxBullet
  exact grantDrainEntranceNonleaderBulletNativeE
    ring hn N e hxFollower hyFollower hxBullet hEmpty hZero

/-- The ready leader creates a LIVE bullet at the empty follower,
even when that follower had signal one: the native E row resets
the new bullet's signal to zero. -/
theorem grantDrainEntranceReadySourceGeneralPairERow
    (x y : CertNative)
    (hxLeader : x.l = true)
    (hxReady : x.sg = true)
    (hyFollower : y.l = false)
    (hyEmpty : y.b = (0 : Fin 3)) :
    (certLiteralEPair x y).1.sg = false ∧
    (certLiteralEPair x y).2.b = (2 : Fin 3) ∧
    (certLiteralEPair x y).2.sg = false := by
  simp [certLiteralEPair, certFinThree,
    hxLeader, hxReady, hyFollower, hyEmpty]

/-- The local invariant itself excludes any old bullet at a
ready leader or its immediate follower. Thus a ready-source E
row is the literal creation of the leftmost clean LIVE bullet.
This does not yet prove all-site ILocal closure for the row. -/
theorem grantDrainEntranceILocalReadySourceNativeE
    {n : Nat} (ring : DirectedRing n) (hn : 3 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hLocal : GrantDrainEntranceILocal ring N)
    (hxLeader : (N e).l = true)
    (hxReady : (N e).sg = true)
    (hyFollower : (N (ring.rightNeighbor e)).l = false) :
    (N e).b = (0 : Fin 3) ∧
    (N (ring.rightNeighbor e)).b = (0 : Fin 3) ∧
    (nativeE ring N e e).sg = false ∧
    (nativeE ring N e (ring.rightNeighbor e)).b =
      (2 : Fin 3) ∧
    (nativeE ring N e (ring.rightNeighbor e)).sg = false := by
  have hNoAhead :=
    grantDrainEntranceILocalReadyNoAhead ring N hLocal e hxReady
  have hSourceEmpty :
      (N e).b = (0 : Fin 3) := by
    by_cases hEmpty : (N e).b = (0 : Fin 3)
    · exact hEmpty
    · have hAt : grantDrainEntranceAheadFuel ring N e 1 :=
        grantDrainEntranceAheadFuelBullet ring N e 0 hEmpty
      have hFull := grantDrainEntranceAheadFuelMonotone
        ring N 1 n e (by omega) hAt
      exact False.elim (hNoAhead hFull)
  have hRightEmpty :
      (N (ring.rightNeighbor e)).b = (0 : Fin 3) := by
    by_cases hEmpty :
        (N (ring.rightNeighbor e)).b = (0 : Fin 3)
    · exact hEmpty
    · have hShort : grantDrainEntranceAheadFuel ring N e 2 := by
        exact Or.inr ⟨hyFollower, Or.inl hEmpty⟩
      have hFull := grantDrainEntranceAheadFuelMonotone
        ring N 2 n e (by omega) hShort
      exact False.elim (hNoAhead hFull)
  have hRow := grantDrainEntranceReadySourceGeneralPairERow
    (N e) (N (ring.rightNeighbor e))
    hxLeader hxReady hyFollower hRightEmpty
  have hDistinct := grantDrainEntranceRightNeighborDistinct
    ring (by omega : 2 ≤ n) e
  refine ⟨hSourceEmpty, hRightEmpty, ?_, ?_, ?_⟩
  · simpa [nativeE] using hRow.1
  · simpa [nativeE, hDistinct] using hRow.2.1
  · simpa [nativeE, hDistinct] using hRow.2.2

/-- Small, closed Fin 3 cases for exact literal-row checks. -/
theorem grantDrainEntranceLocalFinThreeCases (b : Fin 3) :
    b = (0 : Fin 3) ∨ b = (1 : Fin 3) ∨
      b = (2 : Fin 3) := by
  rcases b with ⟨v, hv⟩
  rcases v with _ | _ | _ | v
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · omega

/-- Any signal one retained at the responder came from its
own old signal; E does not copy the initiator signal rightward. -/
theorem grantDrainEntranceLiteralEResponderSignalOrigin
    (x y : CertNative) :
    (certLiteralEPair x y).2.sg = true → y.sg = true := by
  rcases x with ⟨xl, xb, xh, xs⟩
  rcases y with ⟨yl, yb, yh, ys⟩
  rcases grantDrainEntranceLocalFinThreeCases xb with ha | ha | ha <;>
  rcases grantDrainEntranceLocalFinThreeCases yb with hb | hb | hb <;>
  rw [ha, hb] <;>
  cases xl <;> cases yl <;> cases xh <;> cases yh <;>
  cases xs <;> cases ys <;> decide

/-- Any new initiator signal one has an old signal one at one
of the endpoints or an old leader at the responder. -/
theorem grantDrainEntranceLiteralEInitiatorSignalOrigin
    (x y : CertNative) :
    (certLiteralEPair x y).1.sg = true →
      (x.sg = true ∨ y.sg = true ∨ y.l = true) := by
  rcases x with ⟨xl, xb, xh, xs⟩
  rcases y with ⟨yl, yb, yh, ys⟩
  rcases grantDrainEntranceLocalFinThreeCases xb with ha | ha | ha <;>
  rcases grantDrainEntranceLocalFinThreeCases yb with hb | hb | hb <;>
  rw [ha, hb] <;>
  cases xl <;> cases yl <;> cases xh <;> cases yh <;>
  cases xs <;> cases ys <;> decide

/-- Instantiation of the responder signal-origin check on the
actual native array, rather than an abstract row surrogate. -/
theorem grantDrainEntranceNativeEResponderSignalOrigin
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hSignal :
      (nativeE ring N e (ring.rightNeighbor e)).sg = true) :
    (N (ring.rightNeighbor e)).sg = true := by
  have hne := grantDrainEntranceRightNeighborDistinct ring hn e
  have hPair :
      (certLiteralEPair (N e) (N (ring.rightNeighbor e))).2.sg =
        true := by
    simpa [nativeE, hne] using hSignal
  exact grantDrainEntranceLiteralEResponderSignalOrigin
    (N e) (N (ring.rightNeighbor e)) hPair

end L3.GrantDrainEntrance

/-!
Additional native-E cases for the rooted local I invariant.

The full all-edge native-E closure is NOT established here. In
particular, the incoming-LIVE leader-death/sector-merge and ready
leader birth cases still need global ahead-scan transport. No
axiom or statement of those cases is added as an assumption.
-/

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-- A bounded ahead witness can only be lost when bullets are erased
or follower paths are cut. This comparison uses exactly the two
fields read by the ahead scan, not signal or shield. -/
theorem grantDrainEntranceAheadFuelBackwardOfFields
    {n : Nat} (ring : DirectedRing n)
    (M N : Fin n → CertNative)
    (hBullet : ∀ i : Fin n, HasBullet M i → HasBullet N i)
    (hFollower : ∀ i : Fin n,
      (M i).l = false → (N i).l = false) :
    ∀ (fuel : Nat) (v : Fin n),
      grantDrainEntranceAheadFuel ring M v fuel →
        grantDrainEntranceAheadFuel ring N v fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro v h
      change False at h
      exact False.elim h
  | succ fuel ih =>
      intro v h
      change HasBullet M v ∨
        ((M (ring.rightNeighbor v)).l = false ∧
          grantDrainEntranceAheadFuel ring M
            (ring.rightNeighbor v) fuel) at h
      rcases h with hHere | hTail
      · exact Or.inl (hBullet v hHere)
      · exact Or.inr
          ⟨hFollower (ring.rightNeighbor v) hTail.1,
            ih (ring.rightNeighbor v) hTail.2⟩

/-- A useful transition principle: no new bullet and no newly
admitted follower path preserve uniqueness. Signal zeros need only
persist away from one exceptional site, provided that site has no
NEW ahead witness. -/
theorem grantDrainEntranceILocalOfReducedAheadExcept
    {n : Nat} (ring : DirectedRing n)
    (N M : Fin n → CertNative) (special : Fin n)
    (hOld : GrantDrainEntranceILocal ring N)
    (hPB : PPlus ring M)
    (hBullet : ∀ i : Fin n, HasBullet M i → HasBullet N i)
    (hFollower : ∀ i : Fin n,
      (M i).l = false → (N i).l = false)
    (hSignal : ∀ i : Fin n, i ≠ special →
      (N i).sg = false → (M i).sg = false)
    (hException :
      ¬ grantDrainEntranceAheadFuel ring M special n) :
    GrantDrainEntranceILocal ring M := by
  have hBackward :=
    grantDrainEntranceAheadFuelBackwardOfFields
      ring M N hBullet hFollower
  refine ⟨hPB, ?_, ?_⟩
  · intro v hNewBullet hNewFollower hNewAhead
    exact (hOld.2.1 v (hBullet v hNewBullet)
      (hFollower (ring.rightNeighbor v) hNewFollower))
      (hBackward n (ring.rightNeighbor v) hNewAhead)
  · intro v hNewAhead
    by_cases hv : v = special
    · subst v
      exact False.elim (hException hNewAhead)
    · exact hSignal v hv
        (hOld.2.2 v (hBackward n v hNewAhead))

/-- Follower target, empty old source, and no ready-leader firing.
The entire native E row keeps leader and bullet at both endpoints,
and its only effect on signal is the source's leftward copy. The
target may already hold a bullet. -/
theorem grantDrainEntranceLiteralEQuietEmptySource
    (x y : CertNative)
    (hxNotReady : x.l = false ∨ x.sg = false)
    (hxEmpty : x.b = (0 : Fin 3))
    (hyFollower : y.l = false) :
    (certLiteralEPair x y).1.l = x.l ∧
    (certLiteralEPair x y).1.b = (0 : Fin 3) ∧
    (certLiteralEPair x y).2.l = false ∧
    (certLiteralEPair x y).2.b = y.b ∧
    (certLiteralEPair x y).1.sg = (x.sg || y.sg) ∧
    (certLiteralEPair x y).2.sg = y.sg := by
  rcases hxNotReady with hxFollower | hxQuiet
  · simp [certLiteralEPair, certFinThree,
      hxFollower, hxEmpty, hyFollower]
  · simp [certLiteralEPair, certFinThree,
      hxQuiet, hxEmpty, hyFollower]

/-- The exact array frame for a non-firing empty source and a
follower responder. No assumptions are made on the target signal,
bullet kind, shield, or any off-edge state. -/
theorem grantDrainEntranceQuietEmptySourceNativeERows
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hxNotReady :
      (N e).l = false ∨ (N e).sg = false)
    (hxEmpty : (N e).b = (0 : Fin 3))
    (hyFollower : (N (ring.rightNeighbor e)).l = false) :
    (∀ i : Fin n,
      (nativeE ring N e i).l = (N i).l ∧
      (nativeE ring N e i).b = (N i).b) ∧
    (nativeE ring N e e).sg =
      ((N e).sg || (N (ring.rightNeighbor e)).sg) ∧
    (nativeE ring N e (ring.rightNeighbor e)).sg =
      (N (ring.rightNeighbor e)).sg := by
  have hPair := grantDrainEntranceLiteralEQuietEmptySource
    (N e) (N (ring.rightNeighbor e))
    hxNotReady hxEmpty hyFollower
  obtain ⟨hLX, hBX, hLY, hBY, hSX, hSY⟩ := hPair
  have hDistinct :=
    grantDrainEntranceRightNeighborDistinct ring hn e
  refine ⟨?_, ?_, ?_⟩
  · intro i
    by_cases he : i = e
    · subst i
      constructor
      · simpa [nativeE] using hLX
      · calc
          (nativeE ring N e e).b = (0 : Fin 3) := by
            simpa [nativeE] using hBX
          _ = (N e).b := hxEmpty.symm
    · by_cases hy : i = ring.rightNeighbor e
      · subst i
        constructor
        · have hNew :
              (nativeE ring N e (ring.rightNeighbor e)).l =
                false := by
            simpa [nativeE, hDistinct] using hLY
          rw [hNew]
          exact hyFollower.symm
        · simpa [nativeE, hDistinct] using hBY
      · have hFrame :=
          grantDrainEntranceNativeEFrame ring N e i he hy
        rw [hFrame]
        exact ⟨rfl, rfl⟩
  · simpa [nativeE] using hSX
  · simpa [nativeE, hDistinct] using hSY

/-- Complete ILocal closure for a source with no old bullet and
no ready-leader firing, feeding any follower. This includes an old
leader at the source with sg=0 and an already occupied responder;
the earlier empty-follower theorem covered only two empty followers. -/
theorem grantDrainEntranceILocalNativeEQuietEmptySource
    {n : Nat} (ring : DirectedRing n) (hn : 3 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hLocal : GrantDrainEntranceILocal ring N)
    (hxNotReady :
      (N e).l = false ∨ (N e).sg = false)
    (hxEmpty : (N e).b = (0 : Fin 3))
    (hyFollower : (N (ring.rightNeighbor e)).l = false) :
    GrantDrainEntranceILocal ring (nativeE ring N e) := by
  have hRows := grantDrainEntranceQuietEmptySourceNativeERows
    ring (by omega : 2 ≤ n) N e hxNotReady hxEmpty hyFollower
  have hAheadEq :=
    grantDrainEntranceAheadFuelUniformFrame
      ring (nativeE ring N e) N
      (fun i => (hRows.1 i).1)
      (fun i => (hRows.1 i).2)
  refine ⟨nativeE_preserves_PPlus hn ring N e hLocal.1,
    ?_, ?_⟩
  · intro v hBullet hFollower hAhead
    have hOldBullet : HasBullet N v := by
      change (nativeE ring N e v).b ≠ (0 : Fin 3)
        at hBullet
      change (N v).b ≠ (0 : Fin 3)
      rw [← (hRows.1 v).2]
      exact hBullet
    have hOldFollower :
        (N (ring.rightNeighbor v)).l = false := by
      rw [← (hRows.1 (ring.rightNeighbor v)).1]
      exact hFollower
    exact (hLocal.2.1 v hOldBullet hOldFollower)
      ((hAheadEq n (ring.rightNeighbor v)).mp hAhead)
  · intro v hAhead
    have hOldAhead := (hAheadEq n v).mp hAhead
    have hOldZero := hLocal.2.2 v hOldAhead
    by_cases he : v = e
    · subst v
      have hEmpty : ¬ HasBullet N e := by
        intro hb
        exact hb hxEmpty
      have hSpan : (n - 1) + 1 = n := by omega
      have hFromEmpty :
          grantDrainEntranceAheadFuel ring N e
            ((n - 1) + 1) := by
        rw [hSpan]
        exact hOldAhead
      have hTail := grantDrainEntranceAheadFuelTailFromEmpty
        ring N e (n - 1) hEmpty hFromEmpty
      have hRightAhead :
          grantDrainEntranceAheadFuel ring N
            (ring.rightNeighbor e) n :=
        grantDrainEntranceAheadFuelMonotone ring N
          (n - 1) n (ring.rightNeighbor e)
          (by omega) hTail.2
      have hRightZero := hLocal.2.2
        (ring.rightNeighbor e) hRightAhead
      rw [hRows.2.1]
      simp [hOldZero, hRightZero]
    · by_cases hy : v = ring.rightNeighbor e
      · subst v
        rw [hRows.2.2]
        exact hOldZero
      · have hFrame :=
          grantDrainEntranceNativeEFrame ring N e v he hy
        rw [hFrame]
        exact hOldZero

/-- A quiet OLD responder leader retains its bullet field through E
even when a LIVE arrives; the source always loses its bullet.
If the leader actually survives, the changed source signal is harmless
because it is immediately followed by a leader. -/
theorem grantDrainEntranceLiteralEQuietLeaderRow
    (x y : CertNative)
    (hyLeader : y.l = true)
    (hyQuiet : y.sg = false) :
    (certLiteralEPair x y).1.l = x.l ∧
    (certLiteralEPair x y).1.b = (0 : Fin 3) ∧
    (certLiteralEPair x y).2.b = y.b ∧
    (certLiteralEPair x y).2.sg = false := by
  rcases x with ⟨xl, xb, xh, xs⟩
  rcases y with ⟨yl, yb, yh, ys⟩
  rcases grantDrainEntranceLocalFinThreeCases xb with ha | ha | ha <;>
  rcases grantDrainEntranceLocalFinThreeCases yb with hb | hb | hb <;>
  rw [ha, hb] at * <;>
  cases xl <;> cases yl <;> cases xh <;> cases yh <;>
  cases xs <;> cases ys <;>
  simp [certLiteralEPair, certFinThree] at *

/-- The old leader y dies exactly when an effective LIVE is
delivered by the source and the effective responder shield is open.
Effective source LIVE may come from a ready leader or an old LIVE;
effective responder shield opens on readiness or was already open. -/
theorem grantDrainEntranceLiteralELeaderDeathCases
    (x y : CertNative)
    (hyLeader : y.l = true) :
    ((certLiteralEPair x y).2.l = false) ↔
      ((x.l = true ∧ x.sg = true ∨
          x.b = (2 : Fin 3)) ∧
        (y.sg = true ∨ y.sh = false)) := by
  rcases x with ⟨xl, xb, xh, xs⟩
  rcases y with ⟨yl, yb, yh, ys⟩
  rcases grantDrainEntranceLocalFinThreeCases xb with ha | ha | ha <;>
  rcases grantDrainEntranceLocalFinThreeCases yb with hb | hb | hb <;>
  rw [ha, hb] at * <;>
  cases xl <;> cases yl <;> cases xh <;> cases yh <;>
  cases xs <;> cases ys <;>
  simp [certLiteralEPair, certFinThree] at *

/-- REPLACE grantDrainEntranceLiteralEDeathSignalsZero (complete lemma).
Substitute the Fin-three bullet before splitting Boolean cases. -/
theorem grantDrainEntranceLiteralEDeathSignalsZero
    (x y : CertNative)
    (hyLeader : y.l = true)
    (hBulletZero : x.b ≠ (0 : Fin 3) → x.sg = false)
    (hDeath : (certLiteralEPair x y).2.l = false) :
    (certLiteralEPair x y).1.sg = false ∧
      (certLiteralEPair x y).2.sg = false := by
  rcases x with ⟨xl, xb, xh, xs⟩
  rcases y with ⟨yl, yb, yh, ys⟩
  rcases grantDrainEntranceLocalFinThreeCases xb with hx | hx | hx <;>
    subst xb <;>
    cases xl <;> cases xs <;> cases yl <;>
    cases yh <;> cases ys <;>
    simp [certLiteralEPair, certFinThree] at * <;> omega

/-- INSERT IMMEDIATELY BEFORE grantDrainEntranceILocalNativeEDeathEndpointZeros.
The WIP used the unavailable identifier nativeE_source_bullet_zero. -/
theorem grantDrainEntranceNativeESourceBulletZero
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (e : Fin n) :
    (nativeE ring N e e).b = (0 : Fin 3) := by
  have hPair : ∀ x y : CertNative,
      (certLiteralEPair x y).1.b = (0 : Fin 3) := by
    intro x y
    rcases x with ⟨xl, xb, xh, xs⟩
    rcases y with ⟨yl, yb, yh, ys⟩
    rcases grantDrainEntranceLocalFinThreeCases xb with hx | hx | hx <;>
      subst xb <;>
      cases xl <;> cases xs <;> cases yl <;>
      cases yh <;> cases ys <;>
      simp [certLiteralEPair, certFinThree]
  simpa [nativeE] using hPair (N e) (N (ring.rightNeighbor e))

/-- REPLACE grantDrainEntranceILocalNativeEDeathEndpointZeros (complete lemma). -/
theorem grantDrainEntranceILocalNativeEDeathEndpointZeros
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hLocal : GrantDrainEntranceILocal ring N)
    (hyLeader : (N (ring.rightNeighbor e)).l = true)
    (hDeath :
      (nativeE ring N e (ring.rightNeighbor e)).l = false) :
    (nativeE ring N e e).b = (0 : Fin 3) ∧
    (nativeE ring N e e).sg = false ∧
    (nativeE ring N e (ring.rightNeighbor e)).l = false ∧
    (nativeE ring N e (ring.rightNeighbor e)).sg = false := by
  have hDistinct := grantDrainEntranceRightNeighborDistinct ring hn e
  have hPairDeath :
      (certLiteralEPair
        (N e) (N (ring.rightNeighbor e))).2.l = false := by
    simpa [nativeE, hDistinct] using hDeath
  have hOldBulletZero :
      (N e).b ≠ (0 : Fin 3) → (N e).sg = false := by
    intro hb
    exact grantDrainEntranceILocalBulletSignalZero ring N hLocal e hb
  have hRow := grantDrainEntranceLiteralEDeathSignalsZero
    (N e) (N (ring.rightNeighbor e))
    hyLeader hOldBulletZero hPairDeath
  refine ⟨grantDrainEntranceNativeESourceBulletZero ring N e,
    ?_, hDeath, ?_⟩
  · simpa [nativeE] using hRow.1
  · simpa [nativeE, hDistinct] using hRow.2

/-- REPLACE grantDrainEntranceILocalNativeEQuietLeaderSurvives
(docstring through the end of its proof). -/
theorem grantDrainEntranceILocalNativeEQuietLeaderSurvives
    {n : Nat} (ring : DirectedRing n) (hn : 3 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hLocal : GrantDrainEntranceILocal ring N)
    (hyLeader : (N (ring.rightNeighbor e)).l = true)
    (hyQuiet : (N (ring.rightNeighbor e)).sg = false)
    (hSurvive :
      (nativeE ring N e (ring.rightNeighbor e)).l = true) :
    GrantDrainEntranceILocal ring (nativeE ring N e) := by
  have hPair := grantDrainEntranceLiteralEQuietLeaderRow
    (N e) (N (ring.rightNeighbor e)) hyLeader hyQuiet
  have hDistinct :=
    grantDrainEntranceRightNeighborDistinct ring (by omega : 2 ≤ n) e
  have hSourceLeader :
      (nativeE ring N e e).l = (N e).l := by
    simpa [nativeE] using hPair.1
  have hDestBullet :
      (nativeE ring N e (ring.rightNeighbor e)).b =
        (N (ring.rightNeighbor e)).b := by
    simpa [nativeE, hDistinct] using hPair.2.2.1
  have hDestZero :
      (nativeE ring N e (ring.rightNeighbor e)).sg = false := by
    simpa [nativeE, hDistinct] using hPair.2.2.2
  have hLeaderFixed :
      ∀ i : Fin n, (nativeE ring N e i).l = (N i).l := by
    intro i
    by_cases he : i = e
    · subst i
      exact hSourceLeader
    · by_cases hy : i = ring.rightNeighbor e
      · subst i
        rw [hyLeader]
        exact hSurvive
      · rw [grantDrainEntranceNativeEFrame ring N e i he hy]
  have hBulletBackward :
      ∀ i : Fin n, HasBullet (nativeE ring N e) i →
        HasBullet N i := by
    intro i hb
    by_cases he : i = e
    · subst i
      exact False.elim
        (hb (grantDrainEntranceNativeESourceBulletZero ring N e))
    · by_cases hy : i = ring.rightNeighbor e
      · subst i
        change (N (ring.rightNeighbor e)).b ≠ (0 : Fin 3)
        change (nativeE ring N e (ring.rightNeighbor e)).b ≠
          (0 : Fin 3) at hb
        rw [hDestBullet] at hb
        exact hb
      · have hFrame :=
          grantDrainEntranceNativeEFrame ring N e i he hy
        change (nativeE ring N e i).b ≠ (0 : Fin 3) at hb
        rw [hFrame] at hb
        exact hb
  have hFollowerBackward :
      ∀ i : Fin n,
        (nativeE ring N e i).l = false → (N i).l = false := by
    intro i hi
    rw [hLeaderFixed i] at hi
    exact hi
  have hSignalExcept :
      ∀ i : Fin n, i ≠ e →
        (N i).sg = false →
          (nativeE ring N e i).sg = false := by
    intro i he hi
    by_cases hy : i = ring.rightNeighbor e
    · subst i
      exact hDestZero
    · rw [grantDrainEntranceNativeEFrame ring N e i he hy]
      exact hi
  have hNoAheadSource :
      ¬ grantDrainEntranceAheadFuel ring
        (nativeE ring N e) e n := by
    have hEmpty : ¬ HasBullet (nativeE ring N e) e := by
      intro hb
      exact hb (grantDrainEntranceNativeESourceBulletZero ring N e)
    have hBarrier :=
      grantDrainEntranceAheadFuelLeaderBarrier ring
        (nativeE ring N e) e (n - 1) hEmpty hSurvive
    have hEq : n - 1 + 1 = n := by omega
    simpa only [hEq] using hBarrier
  exact grantDrainEntranceILocalOfReducedAheadExcept
    ring N (nativeE ring N e) e
    hLocal (nativeE_preserves_PPlus hn ring N e hLocal.1)
    hBulletBackward hFollowerBackward hSignalExcept hNoAheadSource

/-- Last-mile source-model assembly. This lemma is explicitly
CONDITIONAL on the still-missing native-E local closure, and therefore
is NOT the unconditional all-edge theorem. -/
theorem grantDrainEntranceIntermediateZNextOfNativeEILocal
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hNativeE :
      ∀ (N : Fin n → CertNative) (edge : Fin n),
        GrantDrainEntranceILocal ring N →
        (∀ b : Fin n,
          ¬ SharedPaperNonleftmostLiveExact ring N b) →
        GrantDrainEntranceILocal ring (nativeE ring N edge))
    (hz : GrantDrainEntranceIntermediateZ ring s) :
    GrantDrainEntranceIntermediateZ ring
      (grantDrainStep ring fresh update s e) := by
  have hOldI : I ring s.native := hz.2
  have hOldLocal : GrantDrainEntranceILocal ring s.native :=
    (grantDrainEntranceIffILocal ring s.native).mp hOldI
  have hENewLocal :
      GrantDrainEntranceILocal ring (nativeE ring s.native e) :=
    hNativeE s.native e hOldLocal hz.1
  exact grantDrainEntranceIntermediateZNextFromILocalE
    ring hn fresh update s e hz hENewLocal

end L3.GrantDrainEntrance

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/--
The responder's bullet survives a quiet leader's death.
A ready responder first overwrites its own bullet by a DUMMY.
This identity is independent of whether the leader then dies.
It corrects the proposed zero-versus-one death classification.
-/
theorem grantDrainEntranceLiteralELeaderBulletAfter
    (x y : CertNative)
    (hyLeader : y.l = true) :
    (certLiteralEPair x y).2.b =
        (if y.sg then (1 : Fin 3) else y.b) ∧
      (certLiteralEPair x y).2.sg = false := by
  rcases x with ⟨xl, xb, xh, xs⟩
  rcases y with ⟨yl, yb, yh, ys⟩
  rcases grantDrainEntranceLocalFinThreeCases xb with hx | hx | hx <;>
    rcases grantDrainEntranceLocalFinThreeCases yb with hy | hy | hy <;>
    rw [hx, hy] at * <;>
    cases xl <;> cases yl <;> cases xs <;>
    cases ys <;> cases yh <;>
    simp [certLiteralEPair, certFinThree] at *

/-- The exact responder bullet/signal projection of native E. -/
theorem grantDrainEntranceNativeELeaderBulletAfter
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hyLeader : (N (ring.rightNeighbor e)).l = true) :
    (nativeE ring N e (ring.rightNeighbor e)).b =
        (if (N (ring.rightNeighbor e)).sg then
          (1 : Fin 3) else (N (ring.rightNeighbor e)).b) ∧
      (nativeE ring N e (ring.rightNeighbor e)).sg = false := by
  have hDistinct :=
    grantDrainEntranceRightNeighborDistinct ring hn e
  have hRow := grantDrainEntranceLiteralELeaderBulletAfter
    (N e) (N (ring.rightNeighbor e)) hyLeader
  constructor
  · simpa [nativeE, hDistinct] using hRow.1
  · simpa [nativeE, hDistinct] using hRow.2

/-- A quiet victim's old resident bullet is NOT consumed by death. -/
theorem grantDrainEntranceNativeEQuietVictimBulletRetained
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hyLeader : (N (ring.rightNeighbor e)).l = true)
    (hyQuiet : (N (ring.rightNeighbor e)).sg = false) :
    (nativeE ring N e (ring.rightNeighbor e)).b =
      (N (ring.rightNeighbor e)).b := by
  have hRow :=
    (grantDrainEntranceNativeELeaderBulletAfter
      ring hn N e hyLeader).1
  simpa [hyQuiet] using hRow

/-- A ready victim emits a DUMMY before the possible deletion. -/
theorem grantDrainEntranceNativeEReadyVictimBulletDummy
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hyLeader : (N (ring.rightNeighbor e)).l = true)
    (hyReady : (N (ring.rightNeighbor e)).sg = true) :
    (nativeE ring N e (ring.rightNeighbor e)).b =
      (1 : Fin 3) := by
  have hRow :=
    (grantDrainEntranceNativeELeaderBulletAfter
      ring hn N e hyLeader).1
  simpa [hyReady] using hRow

/--
Corrected endpoint classification for an actual leader-death row
under the old ILocal invariant. Unlike the proposed classification,
a non-ready victim retains its old b, which may be DUMMY.
-/
theorem grantDrainEntranceILocalDeathCorrectedEndpoints
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hLocal : GrantDrainEntranceILocal ring N)
    (hyLeader : (N (ring.rightNeighbor e)).l = true)
    (hDeath :
      (nativeE ring N e (ring.rightNeighbor e)).l = false) :
    (nativeE ring N e (ring.rightNeighbor e)).l = false ∧
    (nativeE ring N e (ring.rightNeighbor e)).b =
      (if (N (ring.rightNeighbor e)).sg then
        (1 : Fin 3) else (N (ring.rightNeighbor e)).b) ∧
    (nativeE ring N e (ring.rightNeighbor e)).sg = false ∧
    (nativeE ring N e e).b = (0 : Fin 3) ∧
    (nativeE ring N e e).sg = false := by
  have hZero := grantDrainEntranceILocalNativeEDeathEndpointZeros
    ring hn N e hLocal hyLeader hDeath
  have hBullet := grantDrainEntranceNativeELeaderBulletAfter
    ring hn N e hyLeader
  exact ⟨hZero.2.2.1, hBullet.1, hBullet.2,
    hZero.1, hZero.2.1⟩

/-- The old ILocal zero-trail clause excludes an ahead bullet
at a ready leader, even before the victim's sector is examined. -/
theorem grantDrainEntranceReadyVictimNoAhead
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (e : Fin n)
    (hLocal : GrantDrainEntranceILocal ring N)
    (hyReady : (N (ring.rightNeighbor e)).sg = true) :
    ¬ grantDrainEntranceAheadFuel ring N
        (ring.rightNeighbor e) n := by
  exact grantDrainEntranceILocalReadyNoAhead ring N hLocal
    (ring.rightNeighbor e) hyReady

/--
If a ready leader is the source of a sectorLength interval,
that entire old sector contains no bullet, including its leader.
This is the uniqueness input for the newly generated death DUMMY.
-/
theorem grantDrainEntranceReadyLeaderSectorBulletFree
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (p : Fin n) (d : Fin (n + 1))
    (hLocal : GrantDrainEntranceILocal ring N)
    (hSector : sectorLength ring N p d)
    (hReady : (N p).sg = true) :
    ∀ a : Fin n, a.val < d.val →
      ¬ HasBullet N (PPL.shiftRight ring p a.val) := by
  intro a ha hBullet
  have hAtZero :
      PPL.shiftRight ring p 0 = p := by
    apply Fin.ext
    change (p.val + 0) % n = p.val
    rw [Nat.add_zero, Nat.mod_eq_of_lt p.isLt]
  have hAhead : grantDrainEntranceAheadFuel ring N p n := by
    have hScan := grantDrainEntranceAheadSectorEarlier
      ring N p d hSector a
        (⟨0, ring.hn⟩ : Fin n) ha (Nat.zero_le _) hBullet
    simpa only [hAtZero] using hScan
  exact (grantDrainEntranceILocalReadyNoAhead
    ring N hLocal p hReady) hAhead

/--
First exact scan splice at the killed boundary: the source e has
no post-E bullet and the successor r is now a follower. Thus the
new scan at e is exactly the new scan at r with one less fuel.
No claim about old-vs-new scans beyond r is made here.
-/
theorem grantDrainEntranceDeathScanAtSource
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (e : Fin n) (fuel : Nat)
    (hDeath :
      (nativeE ring N e (ring.rightNeighbor e)).l = false) :
    grantDrainEntranceAheadFuel ring (nativeE ring N e)
        e (fuel + 1) ↔
      grantDrainEntranceAheadFuel ring (nativeE ring N e)
        (ring.rightNeighbor e) fuel := by
  have hEmpty : ¬ HasBullet (nativeE ring N e) e := by
    intro hBullet
    exact hBullet (grantDrainEntranceNativeESourceBulletZero
      ring N e)
  constructor
  · intro hAhead
    exact (grantDrainEntranceAheadFuelTailFromEmpty
      ring (nativeE ring N e) e fuel hEmpty hAhead).2
  · intro hAhead
    exact Or.inr ⟨hDeath, hAhead⟩

/-- Concrete n=5 ring with a clean incoming LIVE and a quiet
leader carrying a DUMMY on its own sector's leftmost site. -/
private def grantDrainEntranceDeathWitnessRing : DirectedRing 5 :=
  ⟨by decide⟩

private def grantDrainEntranceDeathWitnessNative :
    Fin 5 → CertNative :=
  fun i =>
    if i.val = 0 then
      { l := true, b := 0, sh := true, sg := false }
    else if i.val = 2 then
      { l := false, b := 2, sh := false, sg := false }
    else if i.val = 3 then
      { l := true, b := 1, sh := false, sg := false }
    else
      { l := false, b := 0, sh := false, sg := false }

/--
At e=2, r=3 dies, yet its signal was zero and its DUMMY
survives. This refutes the proposed non-ready => b=0 subcase.
The equalities are closed, small kernel reductions.
-/
theorem grantDrainEntranceDeathWitnessRow :
    (grantDrainEntranceDeathWitnessNative (3 : Fin 5)).l = true ∧
    (grantDrainEntranceDeathWitnessNative (3 : Fin 5)).sg = false ∧
    (grantDrainEntranceDeathWitnessNative (3 : Fin 5)).b =
      (1 : Fin 3) ∧
    (nativeE grantDrainEntranceDeathWitnessRing
      grantDrainEntranceDeathWitnessNative
      (2 : Fin 5) (3 : Fin 5)).l = false ∧
    (nativeE grantDrainEntranceDeathWitnessRing
      grantDrainEntranceDeathWitnessNative
      (2 : Fin 5) (3 : Fin 5)).b = (1 : Fin 3) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end L3.GrantDrainEntrance

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-- Reverse direction of the exact, fuel-bounded ahead witness.
This works for every native word, without ILocal or PPlus. -/
theorem grantDrainEntranceAheadFuelWitnessReverse
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) :
    ∀ (fuel : Nat) (v : Fin n) (t : Nat),
      t < fuel →
      HasBullet N (PPL.shiftRight ring v t) →
      (∀ j : Nat, 0 < j → j ≤ t →
        (N (PPL.shiftRight ring v j)).l = false) →
      grantDrainEntranceAheadFuel ring N v fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro v t ht hb hpath
      omega
  | succ fuel ih =>
      intro v t ht hb hpath
      cases t with
      | zero =>
          have hz : PPL.shiftRight ring v 0 = v := by
            apply Fin.ext
            simp [PPL.shiftRight, Nat.mod_eq_of_lt v.isLt]
          rw [hz] at hb
          exact Or.inl hb
      | succ t =>
          have hFirst := hpath 1 (by omega) (by omega)
          have hFollower :
              (N (ring.rightNeighbor v)).l = false := by
            change (N (ring.rightNeighbor v)).l = false at hFirst
            exact hFirst
          have hTailBullet :
              HasBullet N
                (PPL.shiftRight ring (ring.rightNeighbor v) t) := by
            rw [grantDrainEntranceAheadRightShift ring v t]
            exact hb
          have hTailPath :
              ∀ j : Nat, 0 < j → j ≤ t →
                (N (PPL.shiftRight ring
                  (ring.rightNeighbor v) j)).l = false := by
            intro j hj hjt
            have hOld := hpath (j + 1) (by omega) (by omega)
            rw [← grantDrainEntranceAheadRightShift ring v j] at hOld
            exact hOld
          exact Or.inr
            ⟨hFollower,
              ih (ring.rightNeighbor v) t
                (by omega) hTailBullet hTailPath⟩

/-- Exact bounded ahead-scan equivalence, not just the witness
extraction already available. -/
theorem grantDrainEntranceAheadFuelIffWitness
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (fuel : Nat) (v : Fin n) :
    grantDrainEntranceAheadFuel ring N v fuel ↔
      ∃ t : Nat, t < fuel ∧
        HasBullet N (PPL.shiftRight ring v t) ∧
        (∀ j : Nat, 0 < j → j ≤ t →
          (N (PPL.shiftRight ring v j)).l = false) := by
  constructor
  · exact grantDrainEntranceAheadFuelWitness ring N fuel v
  · rintro ⟨t, ht, hb, hp⟩
    exact grantDrainEntranceAheadFuelWitnessReverse
      ring N fuel v t ht hb hp

/-- Literal E never changes the initiator's leader bit. -/
theorem grantDrainEntranceLiteralESourceLeaderFixed
    (x y : CertNative) :
    (certLiteralEPair x y).1.l = x.l := by
  rcases x with ⟨xl, xb, xh, xs⟩
  rcases y with ⟨yl, yb, yh, ys⟩
  rcases grantDrainEntranceLocalFinThreeCases xb with hx | hx | hx <;>
    rcases grantDrainEntranceLocalFinThreeCases yb with hy | hy | hy <;>
    rw [hx, hy] at * <;>
    cases xl <;> cases yl <;> cases xh <;> cases yh <;>
    cases xs <;> cases ys <;>
    simp [certLiteralEPair, certFinThree] at *

/-- These are the exact new leader bits expressed in OLD fields,
assuming the responder leader is killed. -/
def grantDrainEntranceDeathLeaderAt
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (e i : Fin n) : Bool :=
  if i = ring.rightNeighbor e then false else (N i).l

/-- Exact new bullet expressed in OLD fields. A quiet victim
retains its resident bullet, while a ready victim emits DUMMY. -/
def grantDrainEntranceDeathBulletAt
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (e i : Fin n) : Fin 3 :=
  if i = e then (0 : Fin 3)
  else if i = ring.rightNeighbor e then
    if (N (ring.rightNeighbor e)).sg then (1 : Fin 3)
    else (N (ring.rightNeighbor e)).b
  else (N i).b

/-- Exact post-E signal on a death edge under old ILocal:
both changed endpoints have signal zero, all others are framed. -/
def grantDrainEntranceDeathSignalAt
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (e i : Fin n) : Bool :=
  if i = e then false
  else if i = ring.rightNeighbor e then false
  else (N i).sg

/-- Three-field exact native-E death-row description at EVERY site.
No sector-merge hypothesis is hidden here. -/
theorem grantDrainEntranceNativeEDeathFields
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hLocal : GrantDrainEntranceILocal ring N)
    (hyLeader : (N (ring.rightNeighbor e)).l = true)
    (hDeath :
      (nativeE ring N e (ring.rightNeighbor e)).l = false) :
    ∀ i : Fin n,
      (nativeE ring N e i).l =
        grantDrainEntranceDeathLeaderAt ring N e i ∧
      (nativeE ring N e i).b =
        grantDrainEntranceDeathBulletAt ring N e i ∧
      (nativeE ring N e i).sg =
        grantDrainEntranceDeathSignalAt ring N e i := by
  have hDistinct :=
    grantDrainEntranceRightNeighborDistinct ring hn e
  have hDistinctRev : e ≠ ring.rightNeighbor e :=
    Ne.symm hDistinct
  have hEnds :=
    grantDrainEntranceILocalDeathCorrectedEndpoints
      ring hn N e hLocal hyLeader hDeath
  have hSourceLeader :
      (nativeE ring N e e).l = (N e).l := by
    simpa [nativeE] using
      grantDrainEntranceLiteralESourceLeaderFixed
        (N e) (N (ring.rightNeighbor e))
  intro i
  by_cases he : i = e
  · subst i
    refine ⟨?_, ?_, ?_⟩
    · simpa [grantDrainEntranceDeathLeaderAt, hDistinctRev]
        using hSourceLeader
    · simpa [grantDrainEntranceDeathBulletAt]
        using hEnds.2.2.2.1
    · simpa [grantDrainEntranceDeathSignalAt]
        using hEnds.2.2.2.2
  · by_cases hr : i = ring.rightNeighbor e
    · subst i
      refine ⟨?_, ?_, ?_⟩
      · simpa [grantDrainEntranceDeathLeaderAt]
          using hEnds.1
      · simpa [grantDrainEntranceDeathBulletAt, hDistinct]
          using hEnds.2.1
      · simpa [grantDrainEntranceDeathSignalAt, hDistinct]
          using hEnds.2.2.1
    · have hFrame :=
        grantDrainEntranceNativeEFrame ring N e i he hr
      rw [hFrame]
      exact
        ⟨by simp [grantDrainEntranceDeathLeaderAt, hr],
          by simp [grantDrainEntranceDeathBulletAt, he, hr],
          by simp [grantDrainEntranceDeathSignalAt, he, hr]⟩

/-- An exact Prop characterizing the POST-DEATH ahead scan
using only OLD native fields and the killed edge. -/
def GrantDrainEntranceDeathAheadOld
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (e v : Fin n) : Prop :=
  ∃ t : Nat, t < n ∧
    grantDrainEntranceDeathBulletAt ring N e
      (PPL.shiftRight ring v t) ≠ (0 : Fin 3) ∧
    ∀ j : Nat, 0 < j → j ≤ t →
      grantDrainEntranceDeathLeaderAt ring N e
        (PPL.shiftRight ring v j) = false

/-- The OLD-field formula exactly recognizes EVERY new ahead scan,
including scans crossing e and the newly deleted leader r. -/
theorem grantDrainEntranceDeathAheadOldIff
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (N : Fin n → CertNative) (e v : Fin n)
    (hLocal : GrantDrainEntranceILocal ring N)
    (hyLeader : (N (ring.rightNeighbor e)).l = true)
    (hDeath :
      (nativeE ring N e (ring.rightNeighbor e)).l = false) :
    grantDrainEntranceAheadFuel ring
        (nativeE ring N e) v n ↔
      GrantDrainEntranceDeathAheadOld ring N e v := by
  have hFields := grantDrainEntranceNativeEDeathFields
    ring hn N e hLocal hyLeader hDeath
  rw [grantDrainEntranceAheadFuelIffWitness
    ring (nativeE ring N e) n v]
  unfold GrantDrainEntranceDeathAheadOld
  constructor
  · rintro ⟨t, ht, hb, hp⟩
    refine ⟨t, ht, ?_, ?_⟩
    · change (nativeE ring N e
        (PPL.shiftRight ring v t)).b ≠ (0 : Fin 3) at hb
      rw [(hFields (PPL.shiftRight ring v t)).2.1] at hb
      exact hb
    · intro j hj hjt
      have hOld := hp j hj hjt
      rw [(hFields (PPL.shiftRight ring v j)).1] at hOld
      exact hOld
  · rintro ⟨t, ht, hb, hp⟩
    refine ⟨t, ht, ?_, ?_⟩
    · change (nativeE ring N e
        (PPL.shiftRight ring v t)).b ≠ (0 : Fin 3)
      rw [(hFields (PPL.shiftRight ring v t)).2.1]
      exact hb
    · intro j hj hjt
      rw [(hFields (PPL.shiftRight ring v j)).1]
      exact hp j hj hjt

/-- Outstanding universal merged-sector certificate stated entirely
using the old-field death maps for bullet and signal. The finite
enumerator verifies it, but it is NOT proved here for arbitrary n. -/
def GrantDrainEntranceDeathOldFieldMergeObligations
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (e : Fin n) : Prop :=
  ∀ (p : Fin n) (d : Fin (n + 1)),
    sectorLength ring (nativeE ring N e) p d →
      (∀ (a b : Fin n), a.val < d.val → b.val < d.val →
        grantDrainEntranceDeathBulletAt ring N e
          (PPL.shiftRight ring p a.val) ≠ (0 : Fin 3) →
        grantDrainEntranceDeathBulletAt ring N e
          (PPL.shiftRight ring p b.val) ≠ (0 : Fin 3) →
        a = b) ∧
      (∀ a : Fin n, a.val < d.val →
        grantDrainEntranceDeathBulletAt ring N e
          (PPL.shiftRight ring p a.val) ≠ (0 : Fin 3) →
        ∀ k : Fin n, k.val ≤ a.val →
          grantDrainEntranceDeathSignalAt ring N e
            (PPL.shiftRight ring p k.val) = false)

/-- Explicit CONDITIONAL final assembly from the missing old-field
merge certificate. It must not be misread as unconditional closure. -/
theorem grantDrainEntranceILocalDeathOfOldFieldMergeObligations
    {n : Nat} (ring : DirectedRing n) (hn : 3 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hLocal : GrantDrainEntranceILocal ring N)
    (hyLeader : (N (ring.rightNeighbor e)).l = true)
    (hDeath :
      (nativeE ring N e (ring.rightNeighbor e)).l = false)
    (hMerge :
      GrantDrainEntranceDeathOldFieldMergeObligations ring N e) :
    GrantDrainEntranceILocal ring (nativeE ring N e) := by
  have hFields := grantDrainEntranceNativeEDeathFields
    ring (by omega : 2 ≤ n) N e hLocal hyLeader hDeath
  have hI : I ring (nativeE ring N e) := by
    refine ⟨nativeE_preserves_PPlus
      hn ring N e hLocal.1, ?_⟩
    intro p d hSector
    obtain ⟨hUnique, hZero⟩ := hMerge p d hSector
    constructor
    · intro a b ha hb hA hB
      apply hUnique a b ha hb
      · change (nativeE ring N e
          (PPL.shiftRight ring p a.val)).b ≠ (0 : Fin 3) at hA
        rw [(hFields (PPL.shiftRight ring p a.val)).2.1] at hA
        exact hA
      · change (nativeE ring N e
          (PPL.shiftRight ring p b.val)).b ≠ (0 : Fin 3) at hB
        rw [(hFields (PPL.shiftRight ring p b.val)).2.1] at hB
        exact hB
    · intro a ha hA k hk
      have hbOld :
          grantDrainEntranceDeathBulletAt ring N e
            (PPL.shiftRight ring p a.val) ≠ (0 : Fin 3) := by
        change (nativeE ring N e
          (PPL.shiftRight ring p a.val)).b ≠ (0 : Fin 3) at hA
        rw [(hFields (PPL.shiftRight ring p a.val)).2.1] at hA
        exact hA
      have hZeroOld := hZero a ha hbOld k hk
      rw [(hFields (PPL.shiftRight ring p k.val)).2.2]
      exact hZeroOld
  exact (grantDrainEntranceIffILocal ring
    (nativeE ring N e)).mp hI

end L3.GrantDrainEntrance

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-- Clockwise offsets really are inverse to shifts below one turn.
This exposes the finite coordinate needed for a sector merge. -/
private theorem grantDrainEntranceDeathOffsetShift
    {n : Nat} (ring : DirectedRing n) (p : Fin n)
    (k : Nat) (hk : k < n) :
    PPL.cyclicOffset ring p (PPL.shiftRight ring p k) = k := by
  change (((p.val + k) % n + n - p.val) % n) = k
  by_cases hs : p.val + k < n
  · rw [Nat.mod_eq_of_lt hs]
    have he : p.val + k + n - p.val = n + k := by omega
    rw [he, Nat.add_mod_left, Nat.mod_eq_of_lt hk]
  · have hge : n ≤ p.val + k := by omega
    have hlt : p.val + k - n < n := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt]
    have he : p.val + k - n + n - p.val = k := by omega
    rw [he, Nat.mod_eq_of_lt hk]

/-- Any short clockwise index is uniquely determined by its site. -/
private theorem grantDrainEntranceDeathOffsetIndex
    {n : Nat} (ring : DirectedRing n)
    (p i : Fin n) (k : Nat) (hk : k < n)
    (hi : PPL.shiftRight ring p k = i) :
    PPL.cyclicOffset ring p i = k := by
  rw [← hi]
  exact grantDrainEntranceDeathOffsetShift ring p k hk

/-- Death deletes exactly one old leader. At every OTHER site the
old and new leader bits are identical. -/
private theorem grantDrainEntranceDeathLeaderAway
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (N : Fin n → CertNative) (e i : Fin n)
    (hLocal : GrantDrainEntranceILocal ring N)
    (hyLeader : (N (ring.rightNeighbor e)).l = true)
    (hDeath :
      (nativeE ring N e (ring.rightNeighbor e)).l = false)
    (hi : i ≠ ring.rightNeighbor e) :
    (nativeE ring N e i).l = (N i).l := by
  have hFields := grantDrainEntranceNativeEDeathFields
    ring hn N e hLocal hyLeader hDeath i
  simpa [grantDrainEntranceDeathLeaderAt, hi] using hFields.1

/-- A post-death sector is either a completely framed OLD sector
or the concatenation of precisely two OLD sectors, divided at r.
In the latter case e is immediately before the split boundary.
The offsets t and d-t are genuine strict lengths, not cyclic
modulo-n guesses. -/
theorem grantDrainEntranceDeathSectorPartition
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hLocal : GrantDrainEntranceILocal ring N)
    (hyLeader : (N (ring.rightNeighbor e)).l = true)
    (hDeath :
      (nativeE ring N e (ring.rightNeighbor e)).l = false)
    (p : Fin n) (d : Fin (n + 1))
    (hSector : sectorLength ring (nativeE ring N e) p d) :
    (sectorLength ring N p d ∧
      ∀ k : Nat, k < d.val →
        PPL.shiftRight ring p k ≠ e ∧
        PPL.shiftRight ring p k ≠ ring.rightNeighbor e)
      ∨
    (∃ t : Fin (n + 1), 0 < t.val ∧ t.val < d.val ∧
      PPL.shiftRight ring p t.val = ring.rightNeighbor e ∧
      PPL.shiftRight ring p (t.val - 1) = e ∧
      sectorLength ring N p t ∧
      sectorLength ring N (ring.rightNeighbor e)
        (⟨d.val - t.val, by omega⟩ : Fin (n + 1))) := by
  have hdLe : d.val ≤ n := by omega
  have hOldAway :
      ∀ i : Fin n, i ≠ ring.rightNeighbor e →
        (nativeE ring N e i).l = (N i).l := by
    intro i hi
    exact grantDrainEntranceDeathLeaderAway
      ring hn N e i hLocal hyLeader hDeath hi
  have hRightAt :
      PPL.shiftRight ring p
        (PPL.cyclicOffset ring p (ring.rightNeighbor e)) =
          ring.rightNeighbor e :=
    grantDrainMarksArcShiftRightOffset ring p (ring.rightNeighbor e)
  have htLt :
      PPL.cyclicOffset ring p (ring.rightNeighbor e) < n :=
    grantDrainEntranceArcOffsetLt ring p (ring.rightNeighbor e)
  have hRightNotP : ring.rightNeighbor e ≠ p := by
    intro he
    have hNewP : (nativeE ring N e
        (ring.rightNeighbor e)).l = true := by
      rw [he]
      exact hSector.2.1
    rw [hDeath] at hNewP
    cases hNewP
  have hRightNotQ :
      ring.rightNeighbor e ≠ PPL.shiftRight ring p d.val := by
    intro he
    have hNewQ :
        (nativeE ring N e (ring.rightNeighbor e)).l = true := by
      rw [he]
      exact hSector.2.2.1
    rw [hDeath] at hNewQ
    cases hNewQ
  have hOldP : (N p).l = true := by
    exact (hOldAway p hRightNotP.symm).symm.trans hSector.2.1
  have hOldQ :
      (N (PPL.shiftRight ring p d.val)).l = true := by
    exact (hOldAway _ hRightNotQ.symm).symm.trans hSector.2.2.1
  have hNotRightAt :
      ∀ k : Nat, k < n →
        k ≠ PPL.cyclicOffset ring p (ring.rightNeighbor e) →
        PPL.shiftRight ring p k ≠ ring.rightNeighbor e := by
    intro k hk hneq heq
    exact hneq
      ((grantDrainEntranceDeathOffsetIndex ring p
        (ring.rightNeighbor e) k hk heq).symm)
  by_cases ht :
      PPL.cyclicOffset ring p (ring.rightNeighbor e) < d.val
  · right
    have htPos :
        0 < PPL.cyclicOffset ring p (ring.rightNeighbor e) := by
      by_cases hz :
          PPL.cyclicOffset ring p (ring.rightNeighbor e) = 0
      · have hrp : ring.rightNeighbor e = p := by
          rw [hz] at hRightAt
          have hZero : PPL.shiftRight ring p 0 = p := by
            apply Fin.ext
            simp [PPL.shiftRight, Nat.mod_eq_of_lt p.isLt]
          exact (hZero.symm.trans hRightAt).symm
        exact False.elim (hRightNotP hrp)
      · omega
    have hLeftInverse :
        PPL.shiftLeft ring (ring.rightNeighbor e) 1 = e := by
      have hs := grantDrainMarksArcShiftLeftRight
        ring e 1 1 (by omega) (by omega)
      change PPL.shiftLeft ring (ring.rightNeighbor e) 1 =
        PPL.shiftRight ring e (1 - 1) at hs
      simpa [PPL.shiftRight, Nat.mod_eq_of_lt e.isLt] using hs
    have hSourceAt :
        PPL.shiftRight ring p
          (PPL.cyclicOffset ring p (ring.rightNeighbor e) - 1) =
            e := by
      have hs := grantDrainMarksArcShiftLeftRight ring p
        (PPL.cyclicOffset ring p (ring.rightNeighbor e))
        1 (by omega) htLt
      rw [hRightAt] at hs
      calc
        PPL.shiftRight ring p
            (PPL.cyclicOffset ring p (ring.rightNeighbor e) - 1) =
          PPL.shiftLeft ring (ring.rightNeighbor e) 1 := hs.symm
        _ = e := hLeftInverse
    refine ⟨⟨PPL.cyclicOffset ring p (ring.rightNeighbor e), by omega⟩,
      htPos, ht, hRightAt, hSourceAt, ?_, ?_⟩
    · refine ⟨htPos, hOldP, ?_, ?_⟩
      · rw [hRightAt]
        exact hyLeader
      · intro k hkpos hklt
        change k.val < PPL.cyclicOffset ring p
          (ring.rightNeighbor e) at hklt
        have hkNotR :=
          hNotRightAt k.val k.isLt (by omega)
        have hNewFollower := hSector.2.2.2
          k hkpos (by omega)
        rw [hOldAway _ hkNotR] at hNewFollower
        exact hNewFollower
    · have hVictimLengthPos :
          0 < d.val - PPL.cyclicOffset ring p
            (ring.rightNeighbor e) := by omega
      refine ⟨hVictimLengthPos, hyLeader, ?_, ?_⟩
      · have hArc :
            PPL.shiftRight ring (ring.rightNeighbor e)
              (d.val -
                PPL.cyclicOffset ring p (ring.rightNeighbor e)) =
              PPL.shiftRight ring p d.val := by
          calc
            PPL.shiftRight ring (ring.rightNeighbor e)
                (d.val - PPL.cyclicOffset ring p
                  (ring.rightNeighbor e)) =
              PPL.shiftRight ring
                (PPL.shiftRight ring p
                  (PPL.cyclicOffset ring p (ring.rightNeighbor e)))
                (d.val - PPL.cyclicOffset ring p
                  (ring.rightNeighbor e)) := by
                    rw [hRightAt]
            _ = PPL.shiftRight ring p
                (PPL.cyclicOffset ring p (ring.rightNeighbor e) +
                  (d.val - PPL.cyclicOffset ring p
                    (ring.rightNeighbor e))) :=
              grantDrainEntranceArcShiftRightAdd ring p
                (PPL.cyclicOffset ring p (ring.rightNeighbor e))
                (d.val - PPL.cyclicOffset ring p
                  (ring.rightNeighbor e))
            _ = PPL.shiftRight ring p d.val := by
              congr 1
              omega
        rw [hArc]
        exact hOldQ
      · intro k hkpos hklt
        change k.val < d.val -
          PPL.cyclicOffset ring p (ring.rightNeighbor e) at hklt
        have hArc :
            PPL.shiftRight ring (ring.rightNeighbor e) k.val =
              PPL.shiftRight ring p
                (PPL.cyclicOffset ring p
                  (ring.rightNeighbor e) + k.val) := by
          calc
            PPL.shiftRight ring (ring.rightNeighbor e) k.val =
              PPL.shiftRight ring
                (PPL.shiftRight ring p
                  (PPL.cyclicOffset ring p (ring.rightNeighbor e)))
                k.val := by rw [hRightAt]
            _ = PPL.shiftRight ring p
                (PPL.cyclicOffset ring p (ring.rightNeighbor e) +
                  k.val) :=
              grantDrainEntranceArcShiftRightAdd ring p
                (PPL.cyclicOffset ring p (ring.rightNeighbor e))
                k.val
        have hIndexLt :
            PPL.cyclicOffset ring p (ring.rightNeighbor e) +
              k.val < d.val := by omega
        have hIndexNotR :
            PPL.shiftRight ring p
                (PPL.cyclicOffset ring p
                  (ring.rightNeighbor e) + k.val) ≠
              ring.rightNeighbor e := by
          apply hNotRightAt _ (by omega)
          omega
        have hIndexPos :
            0 < PPL.cyclicOffset ring p (ring.rightNeighbor e) +
              k.val := by omega
        have hIndexNatLt :
            PPL.cyclicOffset ring p (ring.rightNeighbor e) +
              k.val < n := by omega
        have hNewFollower := hSector.2.2.2
          (⟨PPL.cyclicOffset ring p (ring.rightNeighbor e) +
              k.val, hIndexNatLt⟩ : Fin n)
          hIndexPos hIndexLt
        rw [hOldAway _ hIndexNotR] at hNewFollower
        rw [hArc]
        exact hNewFollower
  · left
    have hNoRight :
        ∀ k : Nat, k < d.val →
          PPL.shiftRight ring p k ≠ ring.rightNeighbor e := by
      intro k hk
      apply hNotRightAt k (by omega)
      omega
    have hNoSource :
        ∀ k : Nat, k < d.val →
          PPL.shiftRight ring p k ≠ e := by
      intro k hk hSource
      have hRAt :
          PPL.shiftRight ring p (k + 1) =
            ring.rightNeighbor e := by
        calc
          PPL.shiftRight ring p (k + 1) =
              ring.rightNeighbor (PPL.shiftRight ring p k) := by
                exact (grantDrainEntranceAheadShiftSucc ring p k).symm
          _ = ring.rightNeighbor e := by rw [hSource]
      by_cases hFull : k + 1 = n
      · have hReturn := grantDrainEntranceAheadShiftFull ring p
        rw [hFull, hReturn] at hRAt
        exact hRightNotP hRAt.symm
      · have hNextLt : k + 1 < n := by omega
        have hIndex :=
          grantDrainEntranceDeathOffsetIndex ring p
            (ring.rightNeighbor e) (k + 1) hNextLt hRAt
        have hkLe : k + 1 ≤ d.val := by omega
        by_cases hAtEnd : k + 1 = d.val
        · have hAtNext :
              ring.rightNeighbor e = PPL.shiftRight ring p d.val := by
            rw [← hAtEnd]
            exact hRAt.symm
          exact hRightNotQ hAtNext
        · omega
    refine ⟨?_, ?_⟩
    · refine ⟨hSector.1, hOldP, hOldQ, ?_⟩
      intro k hkpos hklt
      have hNewFollower :=
        hSector.2.2.2 k hkpos hklt
      rw [hOldAway _ (hNoRight k.val hklt)] at hNewFollower
      exact hNewFollower
    · intro k hk
      exact ⟨hNoSource k hk, hNoRight k hk⟩

/-- A framed post-sector inherits both I-clauses directly from
the corresponding old sector. Endpoint e may be the NEXT leader,
but is outside [0,d) and cannot affect its certificate. -/
theorem grantDrainEntranceDeathFramedSector
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (e : Fin n)
    (hLocal : GrantDrainEntranceILocal ring N)
    (p : Fin n) (d : Fin (n + 1))
    (hOldSector : sectorLength ring N p d)
    (hAvoid : ∀ k : Nat, k < d.val →
      PPL.shiftRight ring p k ≠ e ∧
      PPL.shiftRight ring p k ≠ ring.rightNeighbor e) :
    (∀ (a b : Fin n), a.val < d.val → b.val < d.val →
      grantDrainEntranceDeathBulletAt ring N e
        (PPL.shiftRight ring p a.val) ≠ (0 : Fin 3) →
      grantDrainEntranceDeathBulletAt ring N e
        (PPL.shiftRight ring p b.val) ≠ (0 : Fin 3) →
      a = b) ∧
    (∀ a : Fin n, a.val < d.val →
      grantDrainEntranceDeathBulletAt ring N e
        (PPL.shiftRight ring p a.val) ≠ (0 : Fin 3) →
      ∀ k : Fin n, k.val ≤ a.val →
        grantDrainEntranceDeathSignalAt ring N e
          (PPL.shiftRight ring p k.val) = false) := by
  have hOldI := grantDrainEntranceILocalImpliesI ring N hLocal
  have hOld := hOldI.2 p d hOldSector
  have hBulletField :
      ∀ k : Nat, k < d.val →
        grantDrainEntranceDeathBulletAt ring N e
          (PPL.shiftRight ring p k) =
            (N (PPL.shiftRight ring p k)).b := by
    intro k hk
    have hs := hAvoid k hk
    simp [grantDrainEntranceDeathBulletAt, hs.1, hs.2]
  have hSignalField :
      ∀ k : Nat, k < d.val →
        grantDrainEntranceDeathSignalAt ring N e
          (PPL.shiftRight ring p k) =
            (N (PPL.shiftRight ring p k)).sg := by
    intro k hk
    have hs := hAvoid k hk
    simp [grantDrainEntranceDeathSignalAt, hs.1, hs.2]
  constructor
  · intro a b ha hb hA hB
    rw [hBulletField a.val ha] at hA
    rw [hBulletField b.val hb] at hB
    exact hOld.1 a b ha hb hA hB
  · intro a ha hA k hk
    rw [hBulletField a.val ha] at hA
    have hOldZero := hOld.2 a ha hA k hk
    rw [hSignalField k.val (by omega)]
    exact hOldZero

/-- The complete literal death prerequisite, including ready-source
emission as well as an already present source LIVE. -/
theorem grantDrainEntranceDeathEffectiveSource
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hyLeader : (N (ring.rightNeighbor e)).l = true)
    (hDeath :
      (nativeE ring N e (ring.rightNeighbor e)).l = false) :
    ((N e).l = true ∧ (N e).sg = true) ∨
      (N e).b = (2 : Fin 3) := by
  have hDistinct := grantDrainEntranceRightNeighborDistinct ring hn e
  have hPairDeath :
      (certLiteralEPair
        (N e) (N (ring.rightNeighbor e))).2.l = false := by
    simpa [nativeE, hDistinct] using hDeath
  have hCases := (grantDrainEntranceLiteralELeaderDeathCases
    (N e) (N (ring.rightNeighbor e)) hyLeader).mp hPairDeath
  exact hCases.1


/-- In the old source sector, every site strictly before the doomed
leader becomes bullet-free and signal-zero. An old LIVE at e uses
the old I zero trail; a ready source is itself the preceding leader,
so the source sector has length one and E resets its signal. -/
theorem grantDrainEntranceDeathSourcePrefixClean
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hLocal : GrantDrainEntranceILocal ring N)
    (hyLeader : (N (ring.rightNeighbor e)).l = true)
    (hDeath :
      (nativeE ring N e (ring.rightNeighbor e)).l = false)
    (p : Fin n) (t : Fin (n + 1))
    (htPos : 0 < t.val) (htLt : t.val < n)
    (hR : PPL.shiftRight ring p t.val = ring.rightNeighbor e)
    (hE : PPL.shiftRight ring p (t.val - 1) = e)
    (hOld : sectorLength ring N p t) :
    ∀ k : Nat, k < t.val →
      grantDrainEntranceDeathBulletAt ring N e
        (PPL.shiftRight ring p k) = (0 : Fin 3) ∧
      grantDrainEntranceDeathSignalAt ring N e
        (PPL.shiftRight ring p k) = false := by
  have hI := (grantDrainEntranceILocalImpliesI
    ring N hLocal).2 p t hOld
  have hInput := grantDrainEntranceDeathEffectiveSource
    ring hn N e hyLeader hDeath
  have hNoR : ∀ k : Nat, k < t.val →
      PPL.shiftRight ring p k ≠ ring.rightNeighbor e := by
    intro k hk heq
    have ho := grantDrainEntranceDeathOffsetIndex
      ring p (ring.rightNeighbor e) k (by omega) heq
    have htOff := grantDrainEntranceDeathOffsetIndex
      ring p (ring.rightNeighbor e) t.val htLt hR
    omega
  rcases hInput with hReady | hLive
  · have htOne : t.val = 1 := by
      by_cases hOne : t.val = 1
      · exact hOne
      · have hMore : 1 < t.val := by omega
        have hLastPositive : 0 < t.val - 1 := by omega
        have hLastInside : t.val - 1 < t.val := by omega
        have hLastInRing : t.val - 1 < n := by omega
        have hFollower : (N (PPL.shiftRight ring p
            (t.val - 1))).l = false :=
          hOld.2.2.2
            (⟨t.val - 1, hLastInRing⟩ : Fin n)
            hLastPositive hLastInside
        rw [hE, hReady.1] at hFollower
        cases hFollower
    intro k hk
    have hSite : PPL.shiftRight ring p k = e := by
      have hkZero : k = 0 := by omega
      simpa [htOne, hkZero] using hE
    constructor
    · simp [grantDrainEntranceDeathBulletAt, hSite]
    · simp [grantDrainEntranceDeathSignalAt, hSite]
  · have hEbullet :
        HasBullet N (PPL.shiftRight ring p (t.val - 1)) := by
      rw [hE]
      change (N e).b ≠ (0 : Fin 3)
      rw [hLive]
      simp
    intro k hk
    have hNoRk := hNoR k hk
    have hLastInside : t.val - 1 < t.val := by omega
    have hLastInRing : t.val - 1 < n := by omega
    have hkInRing : k < n := by omega
    have hkBeforeLast : k ≤ t.val - 1 := by omega
    have hOldZero :
        (N (PPL.shiftRight ring p k)).sg = false :=
      hI.2 (⟨t.val - 1, hLastInRing⟩ : Fin n)
        hLastInside hEbullet
        (⟨k, hkInRing⟩ : Fin n) hkBeforeLast
    have hBulletZero :
        grantDrainEntranceDeathBulletAt ring N e
          (PPL.shiftRight ring p k) = (0 : Fin 3) := by
      by_cases hkE : PPL.shiftRight ring p k = e
      · simp [grantDrainEntranceDeathBulletAt, hkE]
      · have hOldBZero :
            (N (PPL.shiftRight ring p k)).b = (0 : Fin 3) := by
          by_cases hb : (N (PPL.shiftRight ring p k)).b =
              (0 : Fin 3)
          · exact hb
          · have hSame := hI.1
              (⟨k, hkInRing⟩ : Fin n)
              (⟨t.val - 1, hLastInRing⟩ : Fin n)
              hk hLastInside hb hEbullet
            have hkEq : k = t.val - 1 :=
              congrArg Fin.val hSame
            have hSite : PPL.shiftRight ring p k = e := by
              rw [hkEq]
              exact hE
            exact False.elim (hkE hSite)
        simp [grantDrainEntranceDeathBulletAt,
          hkE, hNoRk, hOldBZero]
    refine ⟨hBulletZero, ?_⟩
    by_cases hkE : PPL.shiftRight ring p k = e
    · simp [grantDrainEntranceDeathSignalAt, hkE]
    · simp [grantDrainEntranceDeathSignalAt,
        hkE, hNoRk, hOldZero]

/-- The old victim sector contributes at most one post-death bullet.
If ready, it becomes exactly the DUMMY at its old leader r, and
the old victim sector was empty. If quiet, the old bullet and
zero trail are preserved, including an old DUMMY already at r. -/
theorem grantDrainEntranceDeathVictimSuffixClean
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hLocal : GrantDrainEntranceILocal ring N)
    (hyLeader : (N (ring.rightNeighbor e)).l = true)
    (p : Fin n) (d t : Fin (n + 1))
    (htPos : 0 < t.val) (htLt : t.val < d.val)
    (hR : PPL.shiftRight ring p t.val = ring.rightNeighbor e)
    (hE : PPL.shiftRight ring p (t.val - 1) = e)
    (hOld : sectorLength ring N (ring.rightNeighbor e)
      (⟨d.val - t.val, by omega⟩ : Fin (n + 1))) :
    (∀ (a b : Fin n), t.val ≤ a.val → a.val < d.val →
      t.val ≤ b.val → b.val < d.val →
      grantDrainEntranceDeathBulletAt ring N e
        (PPL.shiftRight ring p a.val) ≠ (0 : Fin 3) →
      grantDrainEntranceDeathBulletAt ring N e
        (PPL.shiftRight ring p b.val) ≠ (0 : Fin 3) →
      a = b) ∧
    (∀ a : Fin n, t.val ≤ a.val → a.val < d.val →
      grantDrainEntranceDeathBulletAt ring N e
        (PPL.shiftRight ring p a.val) ≠ (0 : Fin 3) →
      ∀ k : Fin n, t.val ≤ k.val → k.val ≤ a.val →
        grantDrainEntranceDeathSignalAt ring N e
          (PPL.shiftRight ring p k.val) = false) := by
  have hdLe : d.val ≤ n := by omega
  have hDistinct := grantDrainEntranceRightNeighborDistinct ring hn e
  have hEne : ring.rightNeighbor e ≠ e := hDistinct
  have hTailSite : ∀ k : Nat, t.val ≤ k → k < d.val →
      PPL.shiftRight ring p k =
        PPL.shiftRight ring (ring.rightNeighbor e) (k - t.val) := by
    intro k hk hkd
    calc
      PPL.shiftRight ring p k =
          PPL.shiftRight ring p (t.val + (k - t.val)) := by
            congr 1
            omega
      _ = PPL.shiftRight ring (PPL.shiftRight ring p t.val)
            (k - t.val) :=
          (grantDrainEntranceArcShiftRightAdd
            ring p t.val (k - t.val)).symm
      _ = PPL.shiftRight ring (ring.rightNeighbor e) (k - t.val) := by
            rw [hR]
  have hNoE : ∀ k : Nat, t.val ≤ k → k < d.val →
      PPL.shiftRight ring p k ≠ e := by
    intro k hk hkd heq
    have hOffK := grantDrainEntranceDeathOffsetIndex
      ring p e k (by omega) heq
    have hOffE := grantDrainEntranceDeathOffsetIndex
      ring p e (t.val - 1) (by omega) hE
    omega
  have hNoRStrict : ∀ k : Nat, t.val < k → k < d.val →
      PPL.shiftRight ring p k ≠ ring.rightNeighbor e := by
    intro k hk hkd heq
    have hOffK := grantDrainEntranceDeathOffsetIndex
      ring p (ring.rightNeighbor e) k (by omega) heq
    have hOffR := grantDrainEntranceDeathOffsetIndex
      ring p (ring.rightNeighbor e) t.val (by omega) hR
    omega
  have hOldI := (grantDrainEntranceILocalImpliesI
    ring N hLocal).2 (ring.rightNeighbor e)
      (⟨d.val - t.val, by omega⟩ : Fin (n + 1)) hOld
  by_cases hReady : (N (ring.rightNeighbor e)).sg = true
  · have hVictimEmpty :=
      grantDrainEntranceReadyLeaderSectorBulletFree
        ring N (ring.rightNeighbor e)
        (⟨d.val - t.val, by omega⟩ : Fin (n + 1))
        hLocal hOld hReady
    have hStrictEmpty :
        ∀ k : Nat, t.val < k → k < d.val →
          grantDrainEntranceDeathBulletAt ring N e
            (PPL.shiftRight ring p k) = (0 : Fin 3) := by
      intro k hk hkd
      have hNotE := hNoE k (by omega) hkd
      have hNotR := hNoRStrict k hk hkd
      have hTailIndexLt :
          k - t.val < d.val - t.val := by omega
      have hTailIndexInRing : k - t.val < n := by omega
      have hNoBullet := hVictimEmpty
        (⟨k - t.val, hTailIndexInRing⟩ : Fin n)
        hTailIndexLt
      have hSite := hTailSite k (by omega) hkd
      have hEmpty : (N (PPL.shiftRight ring p k)).b =
          (0 : Fin 3) := by
        rw [hSite]
        by_cases hb :
            (N (PPL.shiftRight ring
              (ring.rightNeighbor e) (k - t.val))).b =
              (0 : Fin 3)
        · exact hb
        · exact False.elim (hNoBullet hb)
      simp [grantDrainEntranceDeathBulletAt,
        hNotE, hNotR, hEmpty]
    have hOnlyR : ∀ a : Fin n, t.val ≤ a.val →
        a.val < d.val →
        grantDrainEntranceDeathBulletAt ring N e
          (PPL.shiftRight ring p a.val) ≠ (0 : Fin 3) →
        a.val = t.val := by
      intro a ha hda hb
      by_cases hEq : a.val = t.val
      · exact hEq
      · exact False.elim
          (hb (hStrictEmpty a.val (by omega) hda))
    constructor
    · intro a b ha hda hb hdb hBulletA hBulletB
      have hEqA := hOnlyR a ha hda hBulletA
      have hEqB := hOnlyR b hb hdb hBulletB
      apply Fin.ext
      omega
    · intro a ha hda hBullet k hk hka
      have haEq := hOnlyR a ha hda hBullet
      have hkEq : k.val = t.val := by omega
      have hSite : PPL.shiftRight ring p k.val =
          ring.rightNeighbor e := by
        rw [hkEq]
        exact hR
      simp [grantDrainEntranceDeathSignalAt,
        hSite, hDistinct]
  · have hQuiet :
        (N (ring.rightNeighbor e)).sg = false := by
      cases hs : (N (ring.rightNeighbor e)).sg with
      | false => rfl
      | true => exact False.elim (hReady hs)
    have hBulletField :
        ∀ k : Nat, t.val ≤ k → k < d.val →
          grantDrainEntranceDeathBulletAt ring N e
            (PPL.shiftRight ring p k) =
              (N (PPL.shiftRight ring
                (ring.rightNeighbor e) (k - t.val))).b := by
      intro k hk hkd
      have hNotE := hNoE k hk hkd
      by_cases hAtR :
          PPL.shiftRight ring p k = ring.rightNeighbor e
      · have hOldEq :
            grantDrainEntranceDeathBulletAt ring N e
              (PPL.shiftRight ring p k) =
                (N (PPL.shiftRight ring p k)).b := by
          simp [grantDrainEntranceDeathBulletAt,
            hAtR, hDistinct, hQuiet]
        calc
          grantDrainEntranceDeathBulletAt ring N e
              (PPL.shiftRight ring p k) =
            (N (PPL.shiftRight ring p k)).b := hOldEq
          _ = (N (PPL.shiftRight ring
                (ring.rightNeighbor e) (k - t.val))).b := by
              rw [hTailSite k hk hkd]
      · have hOldEq :
            grantDrainEntranceDeathBulletAt ring N e
              (PPL.shiftRight ring p k) =
                (N (PPL.shiftRight ring p k)).b := by
          simp [grantDrainEntranceDeathBulletAt, hNotE, hAtR]
        calc
          grantDrainEntranceDeathBulletAt ring N e
              (PPL.shiftRight ring p k) =
            (N (PPL.shiftRight ring p k)).b := hOldEq
          _ = (N (PPL.shiftRight ring
                (ring.rightNeighbor e) (k - t.val))).b := by
              rw [hTailSite k hk hkd]
    have hSignalField :
        ∀ k : Nat, t.val ≤ k → k < d.val →
          grantDrainEntranceDeathSignalAt ring N e
            (PPL.shiftRight ring p k) =
              (N (PPL.shiftRight ring
                (ring.rightNeighbor e) (k - t.val))).sg := by
      intro k hk hkd
      have hNotE := hNoE k hk hkd
      by_cases hAtR :
          PPL.shiftRight ring p k = ring.rightNeighbor e
      · have hOldEq :
            grantDrainEntranceDeathSignalAt ring N e
              (PPL.shiftRight ring p k) =
                (N (PPL.shiftRight ring p k)).sg := by
          simp [grantDrainEntranceDeathSignalAt,
            hAtR, hDistinct, hQuiet]
        calc
          grantDrainEntranceDeathSignalAt ring N e
              (PPL.shiftRight ring p k) =
            (N (PPL.shiftRight ring p k)).sg := hOldEq
          _ = (N (PPL.shiftRight ring
                (ring.rightNeighbor e) (k - t.val))).sg := by
              rw [hTailSite k hk hkd]
      · have hOldEq :
            grantDrainEntranceDeathSignalAt ring N e
              (PPL.shiftRight ring p k) =
                (N (PPL.shiftRight ring p k)).sg := by
          simp [grantDrainEntranceDeathSignalAt, hNotE, hAtR]
        calc
          grantDrainEntranceDeathSignalAt ring N e
              (PPL.shiftRight ring p k) =
            (N (PPL.shiftRight ring p k)).sg := hOldEq
          _ = (N (PPL.shiftRight ring
                (ring.rightNeighbor e) (k - t.val))).sg := by
              rw [hTailSite k hk hkd]
    constructor
    · intro a b ha hda hb hdb hBulletA hBulletB
      rw [hBulletField a.val ha hda] at hBulletA
      rw [hBulletField b.val hb hdb] at hBulletB
      have haOffsetInside :
          a.val - t.val < d.val - t.val := by omega
      have hbOffsetInside :
          b.val - t.val < d.val - t.val := by omega
      have hOldSame := hOldI.1
        (⟨a.val - t.val, by omega⟩ : Fin n)
        (⟨b.val - t.val, by omega⟩ : Fin n)
        haOffsetInside hbOffsetInside hBulletA hBulletB
      have hVal : a.val - t.val = b.val - t.val :=
        congrArg Fin.val hOldSame
      apply Fin.ext
      omega
    · intro a ha hda hBullet k hk hka
      rw [hBulletField a.val ha hda] at hBullet
      have haOffsetInside :
          a.val - t.val < d.val - t.val := by omega
      have hkOffsetBefore :
          k.val - t.val ≤ a.val - t.val := by omega
      have hOldZero := hOldI.2
        (⟨a.val - t.val, by omega⟩ : Fin n)
        haOffsetInside hBullet
        (⟨k.val - t.val, by omega⟩ : Fin n)
        hkOffsetBefore
      rw [hSignalField k.val hk (by omega)]
      exact hOldZero

/-- The split's two zero/bullet certificates concatenate to the
post-sector I-clauses. This arithmetic statement is independent
of native E, and allows the victim sector to be empty. -/
theorem grantDrainEntranceDeathAssembleSplit
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (e : Fin n)
    (p : Fin n) (d t : Fin (n + 1))
    (ht : t.val < d.val)
    (hPrefix : ∀ k : Nat, k < t.val →
      grantDrainEntranceDeathBulletAt ring N e
        (PPL.shiftRight ring p k) = (0 : Fin 3) ∧
      grantDrainEntranceDeathSignalAt ring N e
        (PPL.shiftRight ring p k) = false)
    (hTail :
      (∀ (a b : Fin n), t.val ≤ a.val → a.val < d.val →
        t.val ≤ b.val → b.val < d.val →
        grantDrainEntranceDeathBulletAt ring N e
          (PPL.shiftRight ring p a.val) ≠ (0 : Fin 3) →
        grantDrainEntranceDeathBulletAt ring N e
          (PPL.shiftRight ring p b.val) ≠ (0 : Fin 3) →
        a = b) ∧
      (∀ a : Fin n, t.val ≤ a.val → a.val < d.val →
        grantDrainEntranceDeathBulletAt ring N e
          (PPL.shiftRight ring p a.val) ≠ (0 : Fin 3) →
        ∀ k : Fin n, t.val ≤ k.val → k.val ≤ a.val →
          grantDrainEntranceDeathSignalAt ring N e
            (PPL.shiftRight ring p k.val) = false)) :
    (∀ (a b : Fin n), a.val < d.val → b.val < d.val →
      grantDrainEntranceDeathBulletAt ring N e
        (PPL.shiftRight ring p a.val) ≠ (0 : Fin 3) →
      grantDrainEntranceDeathBulletAt ring N e
        (PPL.shiftRight ring p b.val) ≠ (0 : Fin 3) →
      a = b) ∧
    (∀ a : Fin n, a.val < d.val →
      grantDrainEntranceDeathBulletAt ring N e
        (PPL.shiftRight ring p a.val) ≠ (0 : Fin 3) →
      ∀ k : Fin n, k.val ≤ a.val →
        grantDrainEntranceDeathSignalAt ring N e
          (PPL.shiftRight ring p k.val) = false) := by
  constructor
  · intro a b ha hb hA hB
    have haTail : t.val ≤ a.val := by
      by_cases hal : a.val < t.val
      · exact False.elim (hA (hPrefix a.val hal).1)
      · omega
    have hbTail : t.val ≤ b.val := by
      by_cases hbl : b.val < t.val
      · exact False.elim (hB (hPrefix b.val hbl).1)
      · omega
    exact hTail.1 a b haTail ha hbTail hb hA hB
  · intro a ha hA k hk
    have haTail : t.val ≤ a.val := by
      by_cases hal : a.val < t.val
      · exact False.elim (hA (hPrefix a.val hal).1)
      · omega
    by_cases hkl : k.val < t.val
    · exact (hPrefix k.val hkl).2
    · exact hTail.2 a haTail ha hA k (by omega) hk

/-- The previously conditional death-merge obligation is derivable
from old ILocal, the literal old leader and its actual E deletion. -/
theorem grantDrainEntranceDeathOldFieldMergeClosed
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hLocal : GrantDrainEntranceILocal ring N)
    (hyLeader : (N (ring.rightNeighbor e)).l = true)
    (hDeath :
      (nativeE ring N e (ring.rightNeighbor e)).l = false) :
    GrantDrainEntranceDeathOldFieldMergeObligations ring N e := by
  intro p d hSector
  rcases grantDrainEntranceDeathSectorPartition
    ring hn N e hLocal hyLeader hDeath p d hSector with
    hFramed | hSplit
  · exact grantDrainEntranceDeathFramedSector
      ring N e hLocal p d hFramed.1 hFramed.2
  · obtain ⟨t, htPos, htLt, hR, hE, hSource, hVictim⟩ := hSplit
    have hPrefix := grantDrainEntranceDeathSourcePrefixClean
      ring hn N e hLocal hyLeader hDeath
      p t htPos (by omega) hR hE hSource
    have hTail := grantDrainEntranceDeathVictimSuffixClean
      ring hn N e hLocal hyLeader
      p d t htPos htLt hR hE hVictim
    exact grantDrainEntranceDeathAssembleSplit
      ring N e p d t htLt hPrefix hTail

/-- Unconditional native-E ILocal closure for the leader-death case.
The prior conditional assembler is now instantiated with the actual
merged-sector certificate rather than postulating it. -/
theorem grantDrainEntranceILocalNativeELeaderDeath
    {n : Nat} (ring : DirectedRing n) (hn : 3 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hLocal : GrantDrainEntranceILocal ring N)
    (hyLeader : (N (ring.rightNeighbor e)).l = true)
    (hDeath :
      (nativeE ring N e (ring.rightNeighbor e)).l = false) :
    GrantDrainEntranceILocal ring (nativeE ring N e) := by
  exact grantDrainEntranceILocalDeathOfOldFieldMergeObligations
    ring hn N e hLocal hyLeader hDeath
    (grantDrainEntranceDeathOldFieldMergeClosed
      ring (by omega : 2 ≤ n) N e hLocal hyLeader hDeath)

end L3.GrantDrainEntrance

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-- Successor is injective on a ring with at least two sites.
This makes the unique predecessor of an inserted bullet explicit. -/
private theorem grantDrainEntranceESuccessorInjective
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n) :
    Function.Injective ring.rightNeighbor := by
  have hInverse : ∀ i : Fin n,
      PPL.shiftLeft ring (ring.rightNeighbor i) 1 = i := by
    intro i
    have hs := grantDrainMarksArcShiftLeftRight
      ring i 1 1 (by omega) (by omega : 1 < n)
    have hRight : PPL.shiftRight ring i 1 =
        ring.rightNeighbor i := rfl
    have hZero : PPL.shiftRight ring i (1 - 1) = i := by
      apply Fin.ext
      simp [PPL.shiftRight, Nat.mod_eq_of_lt i.isLt]
    rw [hRight, hZero] at hs
    exact hs
  intro i j hij
  calc
    i = PPL.shiftLeft ring (ring.rightNeighbor i) 1 :=
      (hInverse i).symm
    _ = PPL.shiftLeft ring (ring.rightNeighbor j) 1 := by
      rw [hij]
    _ = j := hInverse j

/-- If an empty position sees no bullet within one full turn,
then its next follower also sees none. The only extra nth scan
position from the successor would be the empty starting site. -/
theorem grantDrainEntranceAheadNextEmptyNoAhead
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (v : Fin n)
    (hEmpty : (N v).b = (0 : Fin 3))
    (hNextFollower : (N (ring.rightNeighbor v)).l = false)
    (hNoAhead :
      ¬ grantDrainEntranceAheadFuel ring N v n) :
    ¬ grantDrainEntranceAheadFuel ring N
      (ring.rightNeighbor v) n := by
  intro hAhead
  obtain ⟨t, ht, hb, hp⟩ :=
    grantDrainEntranceAheadFuelWitness
      ring N n (ring.rightNeighbor v) hAhead
  by_cases hLast : t + 1 = n
  · have hSite :
        PPL.shiftRight ring (ring.rightNeighbor v) t = v := by
      rw [grantDrainEntranceAheadRightShift ring v t]
      rw [hLast]
      exact grantDrainEntranceAheadShiftFull ring v
    rw [hSite] at hb
    exact hb hEmpty
  · have htShort : t < n - 1 := by omega
    have hShort := grantDrainEntranceAheadFuelWitnessReverse
      ring N (n - 1) (ring.rightNeighbor v)
      t htShort hb hp
    have hFromV := grantDrainEntranceAheadFuelStep
      ring N v (n - 1) hNextFollower hShort
    have hEq : n - 1 + 1 = n := by omega
    exact hNoAhead (by simpa only [hEq] using hFromV)

/-- An additional bullet at a STILL-LEADER site cannot become visible
from another starting site: entering that leader is forbidden by the
ahead-scan follower guard. -/
theorem grantDrainEntranceAheadBackwardExceptLeader
    {n : Nat} (ring : DirectedRing n)
    (N M : Fin n → CertNative) (special : Fin n)
    (hLeader : (M special).l = true)
    (hBulletAway : ∀ i : Fin n, i ≠ special →
      HasBullet M i → HasBullet N i)
    (hFollower : ∀ i : Fin n,
      (M i).l = false → (N i).l = false) :
    ∀ (fuel : Nat) (v : Fin n), v ≠ special →
      grantDrainEntranceAheadFuel ring M v fuel →
        grantDrainEntranceAheadFuel ring N v fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro v hv hAhead
      change False at hAhead
      exact False.elim hAhead
  | succ fuel ih =>
      intro v hv hAhead
      change HasBullet M v ∨
        ((M (ring.rightNeighbor v)).l = false ∧
          grantDrainEntranceAheadFuel ring M
            (ring.rightNeighbor v) fuel) at hAhead
      rcases hAhead with hb | hTail
      · exact Or.inl (hBulletAway v hv hb)
      · have hNextAway :
            ring.rightNeighbor v ≠ special := by
          intro he
          have hFalse : true = false := by
            rw [he, hLeader] at hTail
            exact hTail.1
          cases hFalse
        exact Or.inr ⟨hFollower _ hTail.1,
          ih (ring.rightNeighbor v) hNextAway hTail.2⟩

/-- A follower bullet that moves e -> right e leaves an OLD bullet
at e available to certify every NEW ahead scan starting outside the
responder. When a scan reaches the moved bullet, it can stop one site
earlier at the old source. -/
theorem grantDrainEntranceAheadBackwardMovedBullet
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (N M : Fin n → CertNative) (e : Fin n)
    (hOldSourceBullet : HasBullet N e)
    (hBulletAway : ∀ i : Fin n,
      i ≠ ring.rightNeighbor e →
        HasBullet M i → HasBullet N i)
    (hFollower : ∀ i : Fin n,
      (M i).l = false → (N i).l = false) :
    ∀ (fuel : Nat) (v : Fin n),
      v ≠ ring.rightNeighbor e →
      grantDrainEntranceAheadFuel ring M v fuel →
        grantDrainEntranceAheadFuel ring N v fuel := by
  have hInjective :=
    grantDrainEntranceESuccessorInjective ring hn
  intro fuel
  induction fuel with
  | zero =>
      intro v hv hAhead
      change False at hAhead
      exact False.elim hAhead
  | succ fuel ih =>
      intro v hv hAhead
      change HasBullet M v ∨
        ((M (ring.rightNeighbor v)).l = false ∧
          grantDrainEntranceAheadFuel ring M
            (ring.rightNeighbor v) fuel) at hAhead
      rcases hAhead with hb | hTail
      · exact Or.inl (hBulletAway v hv hb)
      · by_cases hy : ring.rightNeighbor v = ring.rightNeighbor e
        · have hvE : v = e := hInjective hy
          subst v
          exact Or.inl hOldSourceBullet
        · exact Or.inr
            ⟨hFollower _ hTail.1,
              ih (ring.rightNeighbor v) hy hTail.2⟩

/-- If a ready source leader creates a new bullet at its immediate
follower, that bullet cannot be reached from an unrelated site
without first crossing the source leader. -/
theorem grantDrainEntranceAheadBackwardReadySource
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (N M : Fin n → CertNative) (e : Fin n)
    (hSourceLeader : (M e).l = true)
    (hBulletAway : ∀ i : Fin n,
      i ≠ e → i ≠ ring.rightNeighbor e →
        HasBullet M i → HasBullet N i)
    (hFollower : ∀ i : Fin n,
      (M i).l = false → (N i).l = false) :
    ∀ (fuel : Nat) (v : Fin n),
      v ≠ e → v ≠ ring.rightNeighbor e →
      grantDrainEntranceAheadFuel ring M v fuel →
        grantDrainEntranceAheadFuel ring N v fuel := by
  have hInjective :=
    grantDrainEntranceESuccessorInjective ring hn
  intro fuel
  induction fuel with
  | zero =>
      intro v he hy hAhead
      change False at hAhead
      exact False.elim hAhead
  | succ fuel ih =>
      intro v he hy hAhead
      change HasBullet M v ∨
        ((M (ring.rightNeighbor v)).l = false ∧
          grantDrainEntranceAheadFuel ring M
            (ring.rightNeighbor v) fuel) at hAhead
      rcases hAhead with hb | hTail
      · exact Or.inl (hBulletAway v he hy hb)
      · have hNextNotSource :
            ring.rightNeighbor v ≠ e := by
          intro hw
          have hFalse : true = false := by
            rw [hw, hSourceLeader] at hTail
            exact hTail.1
          cases hFalse
        have hNextNotTarget :
            ring.rightNeighbor v ≠ ring.rightNeighbor e := by
          intro hw
          exact he (hInjective hw)
        exact Or.inr
          ⟨hFollower _ hTail.1,
            ih (ring.rightNeighbor v)
              hNextNotSource hNextNotTarget hTail.2⟩

/-- In the follower-responder row the responder remains a follower,
regardless of source readiness or bullet value. -/
theorem grantDrainEntranceLiteralEFollowerResponderRemains
    (x y : CertNative) (hyFollower : y.l = false) :
    (certLiteralEPair x y).2.l = false := by
  rcases x with ⟨xl, xb, xh, xs⟩
  rcases y with ⟨yl, yb, yh, ys⟩
  rcases grantDrainEntranceLocalFinThreeCases xb with hx | hx | hx <;>
    subst xb <;>
    cases xl <;> cases xs <;> cases yl <;>
    simp [certLiteralEPair, certFinThree] at *

/-- If E does not change the responder's leader bit, the leader
array is fixed everywhere; the source leader bit is always fixed. -/
theorem grantDrainEntranceNativeELeadersFixed
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hResponder :
      (nativeE ring N e (ring.rightNeighbor e)).l =
        (N (ring.rightNeighbor e)).l) :
    ∀ i : Fin n,
      (nativeE ring N e i).l = (N i).l := by
  have hDistinct := grantDrainEntranceRightNeighborDistinct
    ring hn e
  have hSource :
      (nativeE ring N e e).l = (N e).l := by
    simpa [nativeE] using
      grantDrainEntranceLiteralESourceLeaderFixed
        (N e) (N (ring.rightNeighbor e))
  intro i
  by_cases he : i = e
  · subst i
    exact hSource
  · by_cases hr : i = ring.rightNeighbor e
    · subst i
      exact hResponder
    · rw [grantDrainEntranceNativeEFrame ring N e i he hr]

/-- The one-bullet exception principle. It applies when old y was
empty and did not see another bullet, both changed signals are
cleared, leaders are fixed, and every relevant NEW scan can be
traced back to an OLD scan. -/
theorem grantDrainEntranceILocalRightBulletPrinciple
    {n : Nat} (ring : DirectedRing n) (hn : 3 ≤ n)
    (N M : Fin n → CertNative) (e : Fin n)
    (hOld : GrantDrainEntranceILocal ring N)
    (hNewPB : PPlus ring M)
    (hLeaders : ∀ i : Fin n, (M i).l = (N i).l)
    (hSourceEmpty : (M e).b = (0 : Fin 3))
    (hSourceZero : (M e).sg = false)
    (hTargetOldEmpty : (N (ring.rightNeighbor e)).b = (0 : Fin 3))
    (hTargetZero : (M (ring.rightNeighbor e)).sg = false)
    (hBulletBackward : ∀ i : Fin n,
      i ≠ ring.rightNeighbor e →
        HasBullet M i → HasBullet N i)
    (hOutsideScan :
      ∀ fuel : Nat, ∀ v : Fin n,
        v ≠ e → v ≠ ring.rightNeighbor e →
        grantDrainEntranceAheadFuel ring M v fuel →
          grantDrainEntranceAheadFuel ring N v fuel)
    (hSourceScan :
      ∀ fuel : Nat, (M e).l = false →
        grantDrainEntranceAheadFuel ring M e fuel →
          grantDrainEntranceAheadFuel ring N e fuel)
    (hOtherSignal : ∀ i : Fin n,
      i ≠ e → i ≠ ring.rightNeighbor e →
      (M i).sg = (N i).sg)
    (hNoOldTargetAhead :
      ¬ grantDrainEntranceAheadFuel ring N
        (ring.rightNeighbor e) n) :
    GrantDrainEntranceILocal ring M := by
  have hDistinct := grantDrainEntranceRightNeighborDistinct
    ring (by omega : 2 ≤ n) e
  have hInjective := grantDrainEntranceESuccessorInjective
    ring (by omega : 2 ≤ n)
  have hOldNextZero :
      ∀ w : Fin n,
        w = ring.rightNeighbor (ring.rightNeighbor e) →
        (N w).l = false →
        ¬ grantDrainEntranceAheadFuel ring N w n := by
    intro w hw hFollower
    subst w
    exact grantDrainEntranceAheadNextEmptyNoAhead ring N
      (ring.rightNeighbor e) hTargetOldEmpty
      hFollower hNoOldTargetAhead
  refine ⟨hNewPB, ?_, ?_⟩
  · intro v hBullet hFollower hAhead
    by_cases hvTarget : v = ring.rightNeighbor e
    · subst v
      have hOldFollower :
          (N (ring.rightNeighbor (ring.rightNeighbor e))).l =
            false := by
        rw [← hLeaders (ring.rightNeighbor (ring.rightNeighbor e))]
        exact hFollower
      have hBack :
          grantDrainEntranceAheadFuel ring N
            (ring.rightNeighbor (ring.rightNeighbor e)) n := by
        by_cases he :
            ring.rightNeighbor (ring.rightNeighbor e) = e
        · rw [he] at hFollower hAhead
          rw [he]
          exact hSourceScan n hFollower hAhead
        · have hy :
              ring.rightNeighbor (ring.rightNeighbor e) ≠
                ring.rightNeighbor e :=
            grantDrainEntranceRightNeighborDistinct
              ring (by omega : 2 ≤ n) (ring.rightNeighbor e)
          exact hOutsideScan n
            (ring.rightNeighbor (ring.rightNeighbor e))
              he hy hAhead
      exact False.elim
        (hOldNextZero _ rfl hOldFollower hBack)
    · have hOldBullet : HasBullet N v :=
        hBulletBackward v hvTarget hBullet
      have hOldFollower :
          (N (ring.rightNeighbor v)).l = false := by
        rw [← hLeaders (ring.rightNeighbor v)]
        exact hFollower
      have hBack :
          grantDrainEntranceAheadFuel ring N
            (ring.rightNeighbor v) n := by
        by_cases hy : ring.rightNeighbor v = ring.rightNeighbor e
        · have hvSource : v = e := hInjective hy
          subst v
          exact False.elim (hBullet hSourceEmpty)
        · by_cases he : ring.rightNeighbor v = e
          · rw [he] at hFollower hAhead
            rw [he]
            exact hSourceScan n hFollower hAhead
          · exact hOutsideScan n (ring.rightNeighbor v)
              he hy hAhead
      exact (hOld.2.1 v hOldBullet hOldFollower) hBack
  · intro v hAhead
    by_cases he : v = e
    · subst v
      exact hSourceZero
    · by_cases hy : v = ring.rightNeighbor e
      · subst v
        exact hTargetZero
      · have hOldAhead := hOutsideScan n v he hy hAhead
        rw [hOtherSignal v he hy]
        exact hOld.2.2 v hOldAhead


/-- Any non-ready source bullet, including a DUMMY resident at a
quiet source leader, moves to an empty follower. Both endpoint
signals are zero; the initiator's own bullet disappears. -/
theorem grantDrainEntranceLiteralEBulletToFollower
    (x y : CertNative)
    (hxBullet : x.b ≠ (0 : Fin 3))
    (hxZero : x.sg = false)
    (hyFollower : y.l = false)
    (hyEmpty : y.b = (0 : Fin 3)) :
    (certLiteralEPair x y).1.b = (0 : Fin 3) ∧
    (certLiteralEPair x y).1.sg = false ∧
    (certLiteralEPair x y).2.b = x.b ∧
    (certLiteralEPair x y).2.sg = false := by
  rcases grantDrainEntranceNonzeroBulletKind
    x.b hxBullet with hb | hb
  · simp [certLiteralEPair, certFinThree,
      hb, hxZero, hyFollower, hyEmpty]
  · simp [certLiteralEPair, certFinThree,
      hb, hxZero, hyFollower, hyEmpty]

/-- Full ILocal closure when an old source bullet moves into the
next follower. The source may itself be a quiet leader; its bullet
cannot be ready because old ILocal requires signal zero at a bullet. -/
theorem grantDrainEntranceILocalNativeEMovingBullet
    {n : Nat} (ring : DirectedRing n) (hn : 3 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hLocal : GrantDrainEntranceILocal ring N)
    (hyFollower : (N (ring.rightNeighbor e)).l = false)
    (hxBullet : HasBullet N e) :
    GrantDrainEntranceILocal ring (nativeE ring N e) := by
  have hDistinct := grantDrainEntranceRightNeighborDistinct
    ring (by omega : 2 ≤ n) e
  have hxZero :=
    grantDrainEntranceILocalBulletSignalZero
      ring N hLocal e hxBullet
  have hyEmpty :=
    grantDrainEntranceILocalFollowerBulletNextEmpty
      ring N e hLocal hxBullet hyFollower
  have hRow := grantDrainEntranceLiteralEBulletToFollower
    (N e) (N (ring.rightNeighbor e))
    hxBullet hxZero hyFollower hyEmpty
  have hSourceEmpty :
      (nativeE ring N e e).b = (0 : Fin 3) :=
    grantDrainEntranceNativeESourceBulletZero ring N e
  have hSourceZero :
      (nativeE ring N e e).sg = false := by
    simpa [nativeE] using hRow.2.1
  have hTargetZero :
      (nativeE ring N e (ring.rightNeighbor e)).sg = false := by
    simpa [nativeE, hDistinct] using hRow.2.2.2
  have hTargetFollower :
      (nativeE ring N e (ring.rightNeighbor e)).l =
        (N (ring.rightNeighbor e)).l := by
    have hFollower :
        (nativeE ring N e (ring.rightNeighbor e)).l = false := by
      simpa [nativeE, hDistinct] using
        grantDrainEntranceLiteralEFollowerResponderRemains
          (N e) (N (ring.rightNeighbor e)) hyFollower
    exact hFollower.trans hyFollower.symm
  have hLeaders :=
    grantDrainEntranceNativeELeadersFixed
      ring (by omega : 2 ≤ n) N e hTargetFollower
  have hFollowerBack :
      ∀ i : Fin n, (nativeE ring N e i).l = false →
        (N i).l = false := by
    intro i hi
    rw [hLeaders i] at hi
    exact hi
  have hBulletBack :
      ∀ i : Fin n, i ≠ ring.rightNeighbor e →
        HasBullet (nativeE ring N e) i →
          HasBullet N i := by
    intro i hy hb
    by_cases he : i = e
    · subst i
      exact False.elim (hb hSourceEmpty)
    · have hFrame := grantDrainEntranceNativeEFrame
        ring N e i he hy
      change (nativeE ring N e i).b ≠ (0 : Fin 3) at hb
      rw [hFrame] at hb
      exact hb
  have hBackward := grantDrainEntranceAheadBackwardMovedBullet
    ring (by omega : 2 ≤ n)
      N (nativeE ring N e) e hxBullet hBulletBack hFollowerBack
  have hOtherSignal :
      ∀ i : Fin n, i ≠ e →
        i ≠ ring.rightNeighbor e →
          (nativeE ring N e i).sg = (N i).sg := by
    intro i he hy
    rw [grantDrainEntranceNativeEFrame ring N e i he hy]
  exact grantDrainEntranceILocalRightBulletPrinciple
    ring hn N (nativeE ring N e) e hLocal
    (nativeE_preserves_PPlus hn ring N e hLocal.1)
    hLeaders hSourceEmpty hSourceZero hyEmpty hTargetZero
    hBulletBack
    (fun fuel v he hy h => hBackward fuel v hy h)
    (fun fuel _ h => hBackward fuel e hDistinct.symm h)
    hOtherSignal (hLocal.2.1 e hxBullet hyFollower)

/-- Full ILocal closure when a READY source leader emits a fresh
clean LIVE into its immediate follower. The victim sector already
has no old ahead bullet by the ready-no-ahead invariant. -/
theorem grantDrainEntranceILocalNativeEReadySource
    {n : Nat} (ring : DirectedRing n) (hn : 3 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hLocal : GrantDrainEntranceILocal ring N)
    (hxLeader : (N e).l = true)
    (hxReady : (N e).sg = true)
    (hyFollower : (N (ring.rightNeighbor e)).l = false) :
    GrantDrainEntranceILocal ring (nativeE ring N e) := by
  have hDistinct := grantDrainEntranceRightNeighborDistinct
    ring (by omega : 2 ≤ n) e
  have hRows := grantDrainEntranceILocalReadySourceNativeE
    ring hn N e hLocal hxLeader hxReady hyFollower
  have hSourceEmpty :=
    grantDrainEntranceNativeESourceBulletZero ring N e
  have hTargetFollower :
      (nativeE ring N e (ring.rightNeighbor e)).l =
        (N (ring.rightNeighbor e)).l := by
    have hFollower :
        (nativeE ring N e (ring.rightNeighbor e)).l = false := by
      simpa [nativeE, hDistinct] using
        grantDrainEntranceLiteralEFollowerResponderRemains
          (N e) (N (ring.rightNeighbor e)) hyFollower
    exact hFollower.trans hyFollower.symm
  have hLeaders :=
    grantDrainEntranceNativeELeadersFixed
      ring (by omega : 2 ≤ n) N e hTargetFollower
  have hNewSourceLeader :
      (nativeE ring N e e).l = true := by
    rw [hLeaders e]
    exact hxLeader
  have hFollowerBack :
      ∀ i : Fin n, (nativeE ring N e i).l = false →
        (N i).l = false := by
    intro i hi
    rw [hLeaders i] at hi
    exact hi
  have hBulletBack :
      ∀ i : Fin n, i ≠ ring.rightNeighbor e →
        HasBullet (nativeE ring N e) i →
          HasBullet N i := by
    intro i hy hb
    by_cases he : i = e
    · subst i
      exact False.elim (hb hSourceEmpty)
    · have hFrame := grantDrainEntranceNativeEFrame
        ring N e i he hy
      change (nativeE ring N e i).b ≠ (0 : Fin 3) at hb
      rw [hFrame] at hb
      exact hb
  have hBackAway : ∀ i : Fin n, i ≠ e →
      i ≠ ring.rightNeighbor e →
        HasBullet (nativeE ring N e) i →
          HasBullet N i := by
    intro i he hy hb
    exact hBulletBack i hy hb
  have hOutside := grantDrainEntranceAheadBackwardReadySource
    ring (by omega : 2 ≤ n) N (nativeE ring N e)
      e hNewSourceLeader hBackAway hFollowerBack
  have hOtherSignal :
      ∀ i : Fin n, i ≠ e →
        i ≠ ring.rightNeighbor e →
          (nativeE ring N e i).sg = (N i).sg := by
    intro i he hy
    rw [grantDrainEntranceNativeEFrame ring N e i he hy]
  have hNoAheadSource :=
    grantDrainEntranceILocalReadyNoAhead ring N hLocal e hxReady
  have hNoAheadTarget :=
    grantDrainEntranceAheadNextEmptyNoAhead ring N e
      hRows.1 hyFollower hNoAheadSource
  exact grantDrainEntranceILocalRightBulletPrinciple
    ring hn N (nativeE ring N e) e hLocal
    (nativeE_preserves_PPlus hn ring N e hLocal.1)
    hLeaders hSourceEmpty hRows.2.2.1
    hRows.2.1 hRows.2.2.2.2
    hBulletBack hOutside
    (fun fuel hFollower _ =>
      False.elim ((by
        have hFalse : true = false :=
          hNewSourceLeader.symm.trans hFollower
        cases hFalse) : False))
    hOtherSignal hNoAheadTarget

/-- When a ready OLD responder leader survives E, it emits a DUMMY
at its own leader site and clears its signal. No other site can
see that new bullet through a leader barrier; the previous
victim sector was bullet-free by the ready-no-ahead certificate. -/
theorem grantDrainEntranceILocalNativeEReadyLeaderSurvives
    {n : Nat} (ring : DirectedRing n) (hn : 3 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hLocal : GrantDrainEntranceILocal ring N)
    (hyLeader : (N (ring.rightNeighbor e)).l = true)
    (hyReady : (N (ring.rightNeighbor e)).sg = true)
    (hSurvive :
      (nativeE ring N e (ring.rightNeighbor e)).l = true) :
    GrantDrainEntranceILocal ring (nativeE ring N e) := by
  have hDistinct := grantDrainEntranceRightNeighborDistinct
    ring (by omega : 2 ≤ n) e
  have hSourceEmpty :=
    grantDrainEntranceNativeESourceBulletZero ring N e
  have hDestRow := grantDrainEntranceNativeELeaderBulletAfter
    ring (by omega : 2 ≤ n) N e hyLeader
  have hTargetZero := hDestRow.2
  have hResponderFixed :
      (nativeE ring N e (ring.rightNeighbor e)).l =
        (N (ring.rightNeighbor e)).l :=
    hSurvive.trans hyLeader.symm
  have hLeaders := grantDrainEntranceNativeELeadersFixed
    ring (by omega : 2 ≤ n) N e hResponderFixed
  have hFollowerBack :
      ∀ i : Fin n, (nativeE ring N e i).l = false →
        (N i).l = false := by
    intro i hi
    rw [hLeaders i] at hi
    exact hi
  have hBulletBack :
      ∀ i : Fin n, i ≠ ring.rightNeighbor e →
        HasBullet (nativeE ring N e) i →
          HasBullet N i := by
    intro i hy hb
    by_cases he : i = e
    · subst i
      exact False.elim (hb hSourceEmpty)
    · have hFrame := grantDrainEntranceNativeEFrame
        ring N e i he hy
      change (nativeE ring N e i).b ≠ (0 : Fin 3) at hb
      rw [hFrame] at hb
      exact hb
  have hBackward := grantDrainEntranceAheadBackwardExceptLeader
    ring N (nativeE ring N e)
      (ring.rightNeighbor e) hSurvive hBulletBack hFollowerBack
  have hReadyNoAhead :=
    grantDrainEntranceILocalReadyNoAhead
      ring N hLocal (ring.rightNeighbor e) hyReady
  have hOldTargetEmpty :
      (N (ring.rightNeighbor e)).b = (0 : Fin 3) := by
    by_cases hEmpty :
        (N (ring.rightNeighbor e)).b = (0 : Fin 3)
    · exact hEmpty
    · have hShort : grantDrainEntranceAheadFuel ring N
          (ring.rightNeighbor e) 1 :=
        grantDrainEntranceAheadFuelBullet ring N
          (ring.rightNeighbor e) 0 hEmpty
      have hFull := grantDrainEntranceAheadFuelMonotone
        ring N 1 n (ring.rightNeighbor e)
        (by omega) hShort
      exact False.elim (hReadyNoAhead hFull)
  have hNoAheadSource :
      ¬ grantDrainEntranceAheadFuel ring
          (nativeE ring N e) e n := by
    have hEmpty : ¬ HasBullet (nativeE ring N e) e := by
      intro hb
      exact hb hSourceEmpty
    have hBarrier := grantDrainEntranceAheadFuelLeaderBarrier
      ring (nativeE ring N e) e (n - 1)
      hEmpty hSurvive
    have hEq : n - 1 + 1 = n := by omega
    simpa only [hEq] using hBarrier
  refine ⟨nativeE_preserves_PPlus hn ring N e hLocal.1,
    ?_, ?_⟩
  · intro v hBullet hNextFollower hNextAhead
    by_cases hv : v = ring.rightNeighbor e
    · subst v
      have hOldFollower :
          (N (ring.rightNeighbor (ring.rightNeighbor e))).l =
            false := by
        rw [← hLeaders (ring.rightNeighbor (ring.rightNeighbor e))]
        exact hNextFollower
      have hNoOldNext :=
        grantDrainEntranceAheadNextEmptyNoAhead
          ring N (ring.rightNeighbor e) hOldTargetEmpty
          hOldFollower hReadyNoAhead
      have hNextDistinct :
          ring.rightNeighbor (ring.rightNeighbor e) ≠
            ring.rightNeighbor e :=
        grantDrainEntranceRightNeighborDistinct
          ring (by omega : 2 ≤ n) (ring.rightNeighbor e)
      exact False.elim
        (hNoOldNext
          (hBackward n
            (ring.rightNeighbor (ring.rightNeighbor e))
            hNextDistinct hNextAhead))
    · have hOldBullet := hBulletBack v hv hBullet
      have hOldFollower :
          (N (ring.rightNeighbor v)).l = false := by
        rw [← hLeaders (ring.rightNeighbor v)]
        exact hNextFollower
      have hNextDistinct :
          ring.rightNeighbor v ≠ ring.rightNeighbor e := by
        intro he
        have hFalse : true = false := by
          rw [he, hSurvive] at hNextFollower
          exact hNextFollower
        cases hFalse
      exact (hLocal.2.1 v hOldBullet hOldFollower)
        (hBackward n (ring.rightNeighbor v)
          hNextDistinct hNextAhead)
  · intro v hAhead
    by_cases hy : v = ring.rightNeighbor e
    · subst v
      exact hTargetZero
    · by_cases he : v = e
      · subst v
        exact False.elim (hNoAheadSource hAhead)
      · have hOldAhead := hBackward n v hy hAhead
        have hOldZero := hLocal.2.2 v hOldAhead
        rw [grantDrainEntranceNativeEFrame ring N e v he hy]
        exact hOldZero

/-- Exhaustive native-E ILocal closure on a ring with at least three
sites. Source and responder readiness, bullets and leader death
are split using the literal E rows; FIRE is not part of this theorem. -/
theorem grantDrainEntranceILocalNativeEAll
    {n : Nat} (ring : DirectedRing n) (hn : 3 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hLocal : GrantDrainEntranceILocal ring N) :
    GrantDrainEntranceILocal ring (nativeE ring N e) := by
  by_cases hyLeader :
      (N (ring.rightNeighbor e)).l = true
  · by_cases hSurvive :
        (nativeE ring N e (ring.rightNeighbor e)).l = true
    · by_cases hyReady :
          (N (ring.rightNeighbor e)).sg = true
      · exact grantDrainEntranceILocalNativeEReadyLeaderSurvives
          ring hn N e hLocal hyLeader hyReady hSurvive
      · have hyQuiet :
            (N (ring.rightNeighbor e)).sg = false := by
          cases hsg : (N (ring.rightNeighbor e)).sg with
          | false => rfl
          | true => exact False.elim (hyReady hsg)
        exact grantDrainEntranceILocalNativeEQuietLeaderSurvives
          ring hn N e hLocal hyLeader hyQuiet hSurvive
    · have hDeath :
          (nativeE ring N e (ring.rightNeighbor e)).l = false := by
        cases hl :
            (nativeE ring N e (ring.rightNeighbor e)).l with
        | false => rfl
        | true => exact False.elim (hSurvive hl)
      exact grantDrainEntranceILocalNativeELeaderDeath
        ring hn N e hLocal hyLeader hDeath
  · have hyFollower :
        (N (ring.rightNeighbor e)).l = false := by
      cases hl : (N (ring.rightNeighbor e)).l with
      | false => rfl
      | true => exact False.elim (hyLeader hl)
    by_cases hxEmpty : (N e).b = (0 : Fin 3)
    · by_cases hxLeader : (N e).l = true
      · by_cases hxReady : (N e).sg = true
        · exact grantDrainEntranceILocalNativeEReadySource
            ring hn N e hLocal hxLeader hxReady hyFollower
        · have hxQuiet : (N e).sg = false := by
            cases hs : (N e).sg with
            | false => rfl
            | true => exact False.elim (hxReady hs)
          exact grantDrainEntranceILocalNativeEQuietEmptySource
            ring hn N e hLocal
            (Or.inr hxQuiet) hxEmpty hyFollower
      · have hxFollower : (N e).l = false := by
          cases hl : (N e).l with
          | false => rfl
          | true => exact False.elim (hxLeader hl)
        exact grantDrainEntranceILocalNativeEQuietEmptySource
          ring hn N e hLocal
          (Or.inl hxFollower) hxEmpty hyFollower
    · exact grantDrainEntranceILocalNativeEMovingBullet
        ring hn N e hLocal hyFollower hxEmpty

/-- Unconditional all-edge physical entrance closure: the native E
step is covered by the exhaustive case theorem, F0/F1/F2 births
are handled by canonicalBirth closure, and the no-bad-LIVE factor
was already proven on every actual grant-drain edge. -/
theorem grantDrainEntranceIntermediateZNext
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hz : GrantDrainEntranceIntermediateZ ring s) :
    GrantDrainEntranceIntermediateZ ring
      (grantDrainStep ring fresh update s e) := by
  exact grantDrainEntranceIntermediateZNextOfNativeEILocal
    ring hn fresh update s e
    (fun N edge hLocal _ =>
      grantDrainEntranceILocalNativeEAll
        ring (by omega : 3 ≤ n) N edge hLocal)
    hz


/-- Remaining R8e obligation: the physical scalar defect potential
does not rise on any edge while the intermediate class holds.
This is a specification, NOT an asserted theorem. -/
def GrantDrainEntranceR8ePotentialNonincrease
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) : Prop :=
  ∀ (s : GrantDrainState n Scratch) (e : Fin n),
    GrantDrainEntranceIntermediateZ ring s →
    grantDrainEntranceSignalCleanupPotential ring
      (grantDrainStep ring fresh update s e).native ≤
    grantDrainEntranceSignalCleanupPotential ring s.native

/-- Remaining R8e obligation: a strictly positive defect has an
outgoing scheduler edge that strictly lowers the physical potential.
Nominated-edge selection must be proved, not assumed. -/
def GrantDrainEntranceR8ePotentialNominatedDrop
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) : Prop :=
  ∀ s : GrantDrainState n Scratch,
    GrantDrainEntranceIntermediateZ ring s →
    0 < grantDrainEntranceSignalCleanupPotential ring s.native →
    ∃ e : Fin n,
      grantDrainEntranceSignalCleanupPotential ring
        (grantDrainStep ring fresh update s e).native <
      grantDrainEntranceSignalCleanupPotential ring s.native

/-- Remaining R8e obligation: zero defects already certify the
existing exact clean-sector class, on the intermediate domain.
The reverse direction for C_native is already proved. -/
def GrantDrainEntranceR8eZeroImpliesClean
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) : Prop :=
  ∀ s : GrantDrainState n Scratch,
    GrantDrainEntranceIntermediateZ ring s →
    grantDrainEntranceSignalCleanupPotential ring s.native = 0 →
    C_native ring s.native

/-- Remaining R8e quantitative obligation: sharpen the universal
n bound to n-2 while the intermediate invariant holds. -/
def GrantDrainEntranceR8ePotentialSharpCap
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) : Prop :=
  ∀ s : GrantDrainState n Scratch,
    GrantDrainEntranceIntermediateZ ring s →
    grantDrainEntranceSignalCleanupPotential ring s.native ≤ n - 2

end L3.GrantDrainEntrance

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-- A zero nonnegative finite defect count excludes each defect.
This uses the actual List.ofFn sum, not a replacement potential. -/
private theorem grantDrainEntranceR8eZeroExcludesDefect
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (hZero : grantDrainEntranceSignalCleanupPotential ring N = 0)
    (v : Fin n) :
    ¬ GrantDrainEntranceSignalDefect ring N v := by
  classical
  have hSum :
      (List.ofFn (fun w : Fin n =>
        if GrantDrainEntranceSignalDefect ring N w
        then 1 else 0)).sum = 0 := by
    simpa [grantDrainEntranceSignalCleanupPotential] using hZero
  have hPoint :
      (if GrantDrainEntranceSignalDefect ring N v
        then (1 : Nat) else 0) = 0 :=
    (List.sum_eq_zero_iff_forall_eq_nat.mp hSum)
      _ (by rw [List.mem_ofFn]; exact ⟨v, rfl⟩)
  intro hDefect
  simp [hDefect] at hPoint

/-- A finite Boolean suffix without a 1-before-0 inversion admits
a 0*1* cut, without Nat.find or a finite-set package. -/
private theorem grantDrainEntranceR8ePatternOfMonotoneSignals
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
      refine ⟨⟨start, by omega⟩, ?_, ?_, ?_, ?_⟩
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
      · refine ⟨⟨start, by omega⟩, ?_, ?_, ?_, ?_⟩
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

/-- Every signal suffix after all possible bullets is monotone
when the actual counted-zero defect is absent at every site. -/
private theorem grantDrainEntranceR8eSuffixFromNoDefects
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
  have hPattern :=
    grantDrainEntranceR8ePatternOfMonotoneSignals
      ring N p (d.val - lo) lo hFuelBound
      (by
        intro r k hr hrk hk hOne
        exact hMonotone r k hr hrk (by omega) hOne)
  have hSame : lo + (d.val - lo) = d.val := by omega
  rw [hSame] at hPattern
  exact hPattern

/-- The exact zero-potential criterion closes the C_native suffix
part of every I sector. No generated-state or historical hypotheses
are imposed on the inherited native configuration. -/
theorem grantDrainEntranceR8eZeroImpliesCleanProved
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) :
    GrantDrainEntranceR8eZeroImpliesClean (Scratch := Scratch) ring := by
  intro s hz hZero
  have hOldI : I ring s.native := hz.2
  have hNoDefect : ∀ v : Fin n,
      ¬ GrantDrainEntranceSignalDefect ring s.native v := by
    intro v
    exact grantDrainEntranceR8eZeroExcludesDefect
      ring s.native hZero v
  refine ⟨hOldI, ?_⟩
  intro p d hSector
  have hOldSector := hOldI.2 p d hSector
  by_cases hBullet :
      ∃ a : Fin n, a.val < d.val ∧
        HasBullet s.native (PPL.shiftRight ring p a.val)
  · rcases hBullet with ⟨a, ha, hOccupied⟩
    have hAfter :
        ∀ j : Fin n, j.val < d.val →
          HasBullet s.native (PPL.shiftRight ring p j.val) →
          j.val < a.val + 1 := by
      intro j hj hJ
      have hSame := hOldSector.1 a j ha hj hOccupied hJ
      have hVal := congrArg Fin.val hSame
      omega
    have hPattern :=
      grantDrainEntranceR8eSuffixFromNoDefects
        ring s.native hNoDefect p d hSector
        (a.val + 1) (by omega) (by omega) hAfter
    exact Or.inl
      ⟨a, ha, hOccupied,
        hOldSector.2 a ha hOccupied, hPattern⟩
  · have hEmpty :
        ∀ a : Fin n, a.val < d.val →
          ¬ HasBullet s.native
            (PPL.shiftRight ring p a.val) := by
      intro a ha hb
      exact hBullet ⟨a, ha, hb⟩
    have hAfter :
        ∀ j : Fin n, j.val < d.val →
          HasBullet s.native (PPL.shiftRight ring p j.val) →
          j.val < 1 := by
      intro j hj hJ
      exact False.elim (hEmpty j hj hJ)
    have hdPositive : 0 < d.val := hSector.1
    have hOneBound : 1 ≤ d.val := by omega
    have hPattern :=
      grantDrainEntranceR8eSuffixFromNoDefects
        ring s.native hNoDefect p d hSector
        1 (Nat.le_refl 1) hOneBound hAfter
    have hReadyCondition :
        (s.native p).sg = true →
        ∀ k : Fin n, 1 ≤ k.val → k.val < d.val →
          (s.native (PPL.shiftRight ring p k.val)).sg =
            true := by
      intro hReady k hkFirst hkInside
      have hNoMismatch :
          ¬ GrantDrainEntranceReadyMismatch ring s.native
            (ring.rightNeighbor p) := by
        intro hm
        exact hNoDefect (ring.rightNeighbor p) (Or.inr hm)
      have hFirstTrue :
          (s.native (ring.rightNeighbor p)).sg = true := by
        cases hs : (s.native (ring.rightNeighbor p)).sg with
        | true => rfl
        | false =>
            have hMismatch :
                GrantDrainEntranceReadyMismatch ring s.native
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
              (s.native (PPL.shiftRight ring p 1)).sg =
                false :=
            hZeros (⟨1, hOneInRing⟩ : Fin n)
              (Nat.le_refl 1) hOneBefore
          have hRightSite :
              PPL.shiftRight ring p 1 = ring.rightNeighbor p := rfl
          rw [hRightSite, hFirstTrue] at hZeroFirst
          cases hZeroFirst
      exact hOnes k (by omega) hkInside
    exact Or.inr ⟨hEmpty, hPattern, hReadyCondition⟩

/-- Every counted-zero site and every ready-mismatch site is a
follower in its witnessing sector. Therefore every native leader
is excluded from the signal-defect count. -/
private theorem grantDrainEntranceR8eLeaderDefectFree
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (v : Fin n)
    (hv : (N v).l = true) :
    ¬ GrantDrainEntranceSignalDefect ring N v := by
  intro hDefect
  rcases hDefect with hCounted | hReady
  · rcases hCounted with
      ⟨p, d, r, k, hSuffix, hSite, hOrder, hKlt,
        hZero, hOne⟩
    have hPositive : 0 < k.val := by
      have hr := hSuffix.2.1
      omega
    have hFollower :=
      hSuffix.1.2.2.2 k hPositive hKlt
    rw [← hSite, hv] at hFollower
    cases hFollower
  · rcases hReady with
      ⟨p, d, hSector, hGap, hSite,
        hEmpty, hLeaderReady, hZero⟩
    have hOneInRing : 1 < n := by
      have hd := d.isLt
      omega
    have hFollower :=
      hSector.2.2.2 (⟨1, hOneInRing⟩ : Fin n)
        (Nat.zero_lt_one) hGap
    have hRight :
        ring.rightNeighbor p = PPL.shiftRight ring p 1 := rfl
    rw [← hRight, ← hSite, hv] at hFollower
    cases hFollower

/-- Any site carrying signal one cannot be a counted zero or
ready-mismatch defect, since both observers require signal zero. -/
private theorem grantDrainEntranceR8eSignalOneDefectFree
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (v : Fin n)
    (hOne : (N v).sg = true) :
    ¬ GrantDrainEntranceSignalDefect ring N v := by
  intro hDefect
  rcases hDefect with hCounted | hReady
  · rcases hCounted with
      ⟨p, d, r, k, hSuffix, hSite, hOrder, hKlt,
        hZero, hEarlier⟩
    rw [hSite] at hOne
    rw [hOne] at hZero
    cases hZero
  · rcases hReady with
      ⟨p, d, hSector, hGap, hSite, hEmpty, hLeaderReady, hZero⟩
    rw [hZero] at hOne
    cases hOne

/-- Given a unique leader p, a zero-signal first follower makes
the site two steps clockwise from p defect-free. Counted-zero
would need an earlier one at the first follower, and ready-mismatch
can only occur at that first follower itself. -/
private theorem grantDrainEntranceR8eSecondFollowerDefectFree
    {n : Nat} (ring : DirectedRing n) (hn : 3 ≤ n)
    (N : Fin n → CertNative) (p : Fin n)
    (hUnique : ∀ q : Fin n, (N q).l = true → q = p)
    (hFirstZero : (N (ring.rightNeighbor p)).sg = false) :
    ¬ GrantDrainEntranceSignalDefect ring N
      (PPL.shiftRight ring p 2) := by
  intro hDefect
  have hTwoOffset :
      PPL.cyclicOffset ring p
        (PPL.shiftRight ring p 2) = 2 :=
    grantDrainEntranceDeathOffsetShift ring p 2 (by omega)
  have hOneOffset :
      PPL.cyclicOffset ring p (ring.rightNeighbor p) = 1 := by
    have hOneSite :
        PPL.shiftRight ring p 1 = ring.rightNeighbor p := rfl
    rw [← hOneSite]
    exact grantDrainEntranceDeathOffsetShift ring p 1 (by omega)
  rcases hDefect with hCounted | hReady
  · rcases hCounted with
      ⟨q, d, r, k, hSuffix, hSite, hOrder, hKlt,
        hZero, hOne⟩
    have hQ : q = p := hUnique q hSuffix.1.2.1
    subst q
    have hKOffset :=
      grantDrainEntranceDeathOffsetIndex ring p
        (PPL.shiftRight ring p 2) k.val k.isLt hSite.symm
    have hkTwo : k.val = 2 := by omega
    have hrOne : r.val = 1 := by
      have hrPositive := hSuffix.2.1
      omega
    have hFirstSite :
        PPL.shiftRight ring p 1 = ring.rightNeighbor p := rfl
    rw [hrOne, hFirstSite, hFirstZero] at hOne
    cases hOne
  · rcases hReady with
      ⟨q, d, hSector, hGap, hSite,
        hEmpty, hReadySignal, hZero⟩
    have hQ : q = p := hUnique q hSector.2.1
    subst q
    rw [hSite] at hTwoOffset
    omega

/-- At least two different sites are defect-free on a rooted
ring of size at least three. Two leaders suffice; with a unique
leader, use the first signal-one follower, or the second follower
when the first signal is zero. -/
private theorem grantDrainEntranceR8eTwoDefectFreeSites
    {n : Nat} (ring : DirectedRing n) (hn : 3 ≤ n)
    (N : Fin n → CertNative) (hPB : PPlus ring N) :
    ∃ a b : Fin n, a ≠ b ∧
      ¬ GrantDrainEntranceSignalDefect ring N a ∧
      ¬ GrantDrainEntranceSignalDefect ring N b := by
  obtain ⟨p, hp⟩ := hPB.1
  have hPFree :=
    grantDrainEntranceR8eLeaderDefectFree ring N p hp
  by_cases hAnother :
      ∃ q : Fin n, q ≠ p ∧ (N q).l = true
  · obtain ⟨q, hqp, hq⟩ := hAnother
    exact ⟨p, q, Ne.symm hqp, hPFree,
      grantDrainEntranceR8eLeaderDefectFree ring N q hq⟩
  · have hUnique : ∀ q : Fin n,
        (N q).l = true → q = p := by
      intro q hq
      by_cases heq : q = p
      · exact heq
      · exact False.elim (hAnother ⟨q, heq, hq⟩)
    by_cases hFirst :
        (N (ring.rightNeighbor p)).sg = true
    · exact ⟨p, ring.rightNeighbor p,
        Ne.symm (grantDrainEntranceRightNeighborDistinct
          ring (by omega : 2 ≤ n) p),
        hPFree,
        grantDrainEntranceR8eSignalOneDefectFree
          ring N (ring.rightNeighbor p) hFirst⟩
    · have hFirstZero :
          (N (ring.rightNeighbor p)).sg = false := by
        cases hs : (N (ring.rightNeighbor p)).sg with
        | false => rfl
        | true => exact False.elim (hFirst hs)
      have hTwoNotP : PPL.shiftRight ring p 2 ≠ p := by
        intro he
        have hTwoOffset :=
          grantDrainEntranceDeathOffsetShift
            ring p 2 (by omega : 2 < n)
        rw [he] at hTwoOffset
        have hZeroOffset : PPL.cyclicOffset ring p p = 0 := by
          unfold PPL.cyclicOffset
          have hSum : p.val + n - p.val = n := by omega
          rw [hSum, Nat.mod_self]
        omega
      exact ⟨p, PPL.shiftRight ring p 2, Ne.symm hTwoNotP,
        hPFree,
        grantDrainEntranceR8eSecondFollowerDefectFree
          ring hn N p hUnique hFirstZero⟩

/-- Pointwise comparison of two List.ofFn sums away from a single
index. The proof is purely core Lean, without Nat.find or Finset. -/
private theorem grantDrainEntranceR8eOfFnSumSplit
    {m : Nat} (f g : Fin m → Nat) (a : Fin m)
    (hLe : ∀ i : Fin m, i ≠ a → f i ≤ g i) :
    (List.ofFn f).sum + g a ≤
      (List.ofFn g).sum + f a := by
  induction m with
  | zero =>
      exact Fin.elim0 a
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      by_cases hz : a = 0
      · subst a
        have hTail := FiniteUniformStoppingTree.ofFn_sum_le
          (fun i : Fin m => f i.succ)
          (fun i : Fin m => g i.succ)
          (fun i => hLe i.succ (Fin.succ_ne_zero i))
        omega
      · have hNZ : a.val ≠ 0 := by
          intro hv
          exact hz (Fin.ext hv)
        have hPred : ∃ p : Fin m, p.succ = a := by
          refine ⟨⟨a.val - 1, ?_⟩, ?_⟩
          · have ha := a.isLt
            omega
          · apply Fin.ext
            change a.val - 1 + 1 = a.val
            omega
        obtain ⟨p, hSucc⟩ := hPred
        have hTail := ih
          (fun i : Fin m => f i.succ)
          (fun i : Fin m => g i.succ) p
          (fun i hi =>
            hLe i.succ (by
              intro h
              apply hi
              rw [← hSucc] at h
              exact Fin.succ_inj.mp h))
        have hHead := hLe 0 (Ne.symm hz)
        simp only [hSucc] at hTail
        omega

/-- Two distinct zero coordinates save two units from the naive
n-site capacity bound for a pointwise {0,1}-valued potential. -/
private theorem grantDrainEntranceR8eSumLeWithTwoZeros
    {n : Nat} (f : Fin n → Nat)
    (a b : Fin n) (hab : a ≠ b)
    (ha : f a = 0) (hb : f b = 0)
    (hOne : ∀ i : Fin n, f i ≤ 1) :
    (List.ofFn f).sum ≤ n - 2 := by
  have hForward := grantDrainEntranceR8eOfFnSumSplit
    f (fun i => if i = a then 1 else f i) a
    (by
      intro i hi
      simp [hi])
  have hReverse := grantDrainEntranceR8eOfFnSumSplit
    (fun i => if i = a then 1 else f i) f a
    (by
      intro i hi
      simp [hi])
  simp [ha] at hForward hReverse
  have hSumAtA :
      (List.ofFn (fun i : Fin n =>
        if i = a then 1 else f i)).sum =
        (List.ofFn f).sum + 1 := by omega
  have hPointwise :
      ∀ i : Fin n,
        (if i = a then 1 else f i) ≤ 1 := by
    intro i
    by_cases hi : i = a
    · simp [hi]
    · simpa [hi] using hOne i
  have hSecond := grantDrainEntranceR8eOfFnSumSplit
    (fun i : Fin n => if i = a then 1 else f i)
    (fun _ : Fin n => 1) b
    (by intro i hi; exact hPointwise i)
  have hAtB :
      (if b = a then 1 else f b) = 0 := by
    simp [Ne.symm hab, hb]
  have hConst :
      (List.ofFn (fun _ : Fin n => (1 : Nat))).sum = n := by
    simp [FiniteUniformStoppingTree.ofFn_sum_const]
  rw [hAtB, hConst] at hSecond
  have hDifferent : a.val ≠ b.val := by
    intro heq
    exact hab (Fin.ext heq)
  have hSize : 2 ≤ n := by
    have haBound := a.isLt
    have hbBound := b.isLt
    omega
  omega

/-- Universal n-2 bound for the actual scalar signal potential
on the intermediate domain, independent of request/grant choices.
Only the existence of a PB root and the per-site defect definition
are needed; n>=3 supplies two distinct defect-free sites. -/
theorem grantDrainEntranceR8ePotentialSharpCapProved
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 3 ≤ n) :
    GrantDrainEntranceR8ePotentialSharpCap (Scratch := Scratch) ring := by
  intro s hz
  have hPB := grantDrainEntranceIntermediateZHasPPlus ring s hz
  obtain ⟨a, b, hab, ha, hb⟩ :=
    grantDrainEntranceR8eTwoDefectFreeSites
      ring hn s.native hPB
  classical
  have hOne :
      ∀ i : Fin n,
        (if GrantDrainEntranceSignalDefect ring s.native i
          then (1 : Nat) else 0) ≤ 1 := by
    intro i
    split <;> omega
  have hZeroA :
      (if GrantDrainEntranceSignalDefect ring s.native a
        then (1 : Nat) else 0) = 0 := by
    simp [ha]
  have hZeroB :
      (if GrantDrainEntranceSignalDefect ring s.native b
        then (1 : Nat) else 0) = 0 := by
    simp [hb]
  have hBound := grantDrainEntranceR8eSumLeWithTwoZeros
    (fun i : Fin n =>
      if GrantDrainEntranceSignalDefect ring s.native i
      then 1 else 0)
    a b hab hZeroA hZeroB hOne
  simpa [grantDrainEntranceSignalCleanupPotential] using hBound

end L3.GrantDrainEntrance

/-!
Arithmetic and native-outcome
reductions for R8e. These lemmas do not assert the two open
unconditional R8e propositions. They isolate the native
defect-transport and explicit-nominated-edge producers.
-/

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- A pointwise backward implication for the exact physical
defect predicate is sufficient for scalar nonincrease. -/
theorem grantDrainEntranceR8ePotentialLeOfDefectBackward
    {n : Nat} (ring : DirectedRing n)
    (before after : Fin n → CertNative)
    (hback : ∀ v : Fin n,
      GrantDrainEntranceSignalDefect ring after v →
      GrantDrainEntranceSignalDefect ring before v) :
    grantDrainEntranceSignalCleanupPotential ring after ≤
      grantDrainEntranceSignalCleanupPotential ring before := by
  classical
  unfold grantDrainEntranceSignalCleanupPotential
  exact FiniteUniformStoppingTree.ofFn_sum_le
    (fun v : Fin n =>
      if GrantDrainEntranceSignalDefect ring after v
      then 1 else 0)
    (fun v : Fin n =>
      if GrantDrainEntranceSignalDefect ring before v
      then 1 else 0)
    (fun v => by
      by_cases hnew :
          GrantDrainEntranceSignalDefect ring after v
      · have hold := hback v hnew
        simp [hnew, hold]
      · simp [hnew])

/-- If no new defect appears and one old defect disappears,
the exact List.ofFn cardinality strictly decreases. The
already-proved ofFnSumSplit lemma supplies the arithmetic. -/
theorem grantDrainEntranceR8ePotentialLtOfDefectLoss
    {n : Nat} (ring : DirectedRing n)
    (before after : Fin n → CertNative)
    (hback : ∀ v : Fin n,
      GrantDrainEntranceSignalDefect ring after v →
      GrantDrainEntranceSignalDefect ring before v)
    (v : Fin n)
    (hold : GrantDrainEntranceSignalDefect ring before v)
    (hgone : ¬ GrantDrainEntranceSignalDefect ring after v) :
    grantDrainEntranceSignalCleanupPotential ring after <
      grantDrainEntranceSignalCleanupPotential ring before := by
  classical
  have hpoint :
      ∀ i : Fin n, i ≠ v →
        (if GrantDrainEntranceSignalDefect ring after i
          then (1 : Nat) else 0) ≤
        (if GrantDrainEntranceSignalDefect ring before i
          then (1 : Nat) else 0) := by
    intro i _
    by_cases hnew :
        GrantDrainEntranceSignalDefect ring after i
    · have hprior := hback i hnew
      simp [hnew, hprior]
    · simp [hnew]
  have hsplit := grantDrainEntranceR8eOfFnSumSplit
    (fun i : Fin n =>
      if GrantDrainEntranceSignalDefect ring after i
      then (1 : Nat) else 0)
    (fun i : Fin n =>
      if GrantDrainEntranceSignalDefect ring before i
      then (1 : Nat) else 0)
    v hpoint
  have hnewZero :
      (if GrantDrainEntranceSignalDefect ring after v
        then (1 : Nat) else 0) = 0 := by
    simp [hgone]
  have holdOne :
      (if GrantDrainEntranceSignalDefect ring before v
        then (1 : Nat) else 0) = 1 := by
    simp [hold]
  rw [hnewZero, holdOne] at hsplit
  change grantDrainEntranceSignalCleanupPotential ring after + 1 ≤
    grantDrainEntranceSignalCleanupPotential ring before + 0 at hsplit
  omega

/-- Reduction to all three literal native outcomes. This theorem
uses the genuine grantDrainStep; the source-native premises have
NOT been proved here. No request/grant or scratch restriction is
introduced. -/
theorem grantDrainEntranceR8eNonincreaseOfNativeOutcomes
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (hNative :
      ∀ (N : Fin n → CertNative) (e : Fin n),
        I ring N →
        grantDrainEntranceSignalCleanupPotential ring
          (nativeE ring N e) ≤
          grantDrainEntranceSignalCleanupPotential ring N ∧
        grantDrainEntranceSignalCleanupPotential ring
          (canonicalBirth (nativeE ring N e) e) ≤
          grantDrainEntranceSignalCleanupPotential ring N ∧
        grantDrainEntranceSignalCleanupPotential ring
          (canonicalBirth (nativeE ring N e)
            (ring.rightNeighbor e)) ≤
          grantDrainEntranceSignalCleanupPotential ring N) :
    GrantDrainEntranceR8ePotentialNonincrease ring fresh update := by
  intro s e hz
  have hI : I ring s.native := hz.2
  obtain ⟨hPlain, hLeft, hRight⟩ :=
    hNative s.native e hI
  rcases grantDrainEntranceNativeOwnerCases
      ring fresh update s e with hstep | hstep | hstep
  · rw [hstep]
    exact hPlain
  · rw [hstep]
    exact hLeft
  · rw [hstep]
    exact hRight

/-- A single native-selected edge which strictly decreases
all three possible native outcomes also works against EVERY
old request/grant assignment of the actual physical step. -/
theorem grantDrainEntranceR8eNominatedDropOfNativeOutcomes
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (hNominate :
      ∀ N : Fin n → CertNative,
        I ring N →
        0 < grantDrainEntranceSignalCleanupPotential ring N →
        ∃ e : Fin n,
          grantDrainEntranceSignalCleanupPotential ring
            (nativeE ring N e) <
            grantDrainEntranceSignalCleanupPotential ring N ∧
          grantDrainEntranceSignalCleanupPotential ring
            (canonicalBirth (nativeE ring N e) e) <
            grantDrainEntranceSignalCleanupPotential ring N ∧
          grantDrainEntranceSignalCleanupPotential ring
            (canonicalBirth (nativeE ring N e)
              (ring.rightNeighbor e)) <
            grantDrainEntranceSignalCleanupPotential ring N) :
    GrantDrainEntranceR8ePotentialNominatedDrop ring fresh update := by
  intro s hz hpos
  have hI : I ring s.native := hz.2
  obtain ⟨e, hPlain, hLeft, hRight⟩ :=
    hNominate s.native hI hpos
  refine ⟨e, ?_⟩
  rcases grantDrainEntranceNativeOwnerCases
      ring fresh update s e with hstep | hstep | hstep
  · rw [hstep]
    exact hPlain
  · rw [hstep]
    exact hLeft
  · rw [hstep]
    exact hRight

end L3.GrantDrainEntrance

/-!
All-n native local progress.
The global backward transport through native-E sector merges and
canonical-birth sector splits is not established by these lemmas.
-/

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- Every counted-zero lies strictly after its own suffix
reference, so no such site can itself hold a bullet. The ready
mismatch case is bullet-free on its entire sector. Consequently
a bullet site is never one of the physical R8e defect sites. -/
theorem grantDrainEntranceR8eBulletDefectFree
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (v : Fin n)
    (hBullet : HasBullet N v) :
    ¬ GrantDrainEntranceSignalDefect ring N v := by
  intro hDefect
  rcases hDefect with hCounted | hReady
  · rcases hCounted with
      ⟨p, d, r, k, hSuffix, hSite,
        hOrder, hInside, hZero, hEarlier⟩
    have hAt : HasBullet N
        (PPL.shiftRight ring p k.val) := by
      rw [← hSite]
      exact hBullet
    have hBefore := hSuffix.2.2.2 k hInside hAt
    omega
  · rcases hReady with
      ⟨p, d, hSector, hGap, hSite,
        hEmpty, hReadySignal, hZero⟩
    have hOneInRing : 1 < n := by
      have hBound := d.isLt
      omega
    have hAt : HasBullet N
        (PPL.shiftRight ring p
          (⟨1, hOneInRing⟩ : Fin n).val) := by
      change HasBullet N (ring.rightNeighbor p)
      rw [← hSite]
      exact hBullet
    exact hEmpty (⟨1, hOneInRing⟩ : Fin n)
      (by omega) hAt

/-- A canonical birth itself cannot be a counted defect,
irrespective of the inherited configuration. -/
theorem grantDrainEntranceR8eBirthSiteDefectFree
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (z : Fin n) :
    ¬ GrantDrainEntranceSignalDefect ring
        (canonicalBirth N z) z := by
  apply grantDrainEntranceR8eLeaderDefectFree
    ring (canonicalBirth N z) z
  simp [canonicalBirth, firedNative]

/-- Exact E source signal: an empty zero-signal source
receives a one when the old responder is ready or is a leader.
The old responder leader bit is tested AFTER E's deletion,
but an empty source cannot cause that deletion. -/
theorem grantDrainEntranceR8eEmptySourceActivated
    (x y : CertNative)
    (hEmpty : x.b = (0 : Fin 3))
    (hZero : x.sg = false)
    (hRight : y.sg = true ∨ y.l = true) :
    (certLiteralEPair x y).1.sg = true := by
  cases hLeader : y.l <;>
    cases hSignal : y.sg <;>
    simp [certLiteralEPair, hEmpty, hZero,
      hLeader, hSignal] at hRight ⊢

/-- A counted zero, immediately followed by a signal-one
or a leader, is eliminated by E at its own source edge.
It stays eliminated if either endpoint is canonically born. -/
theorem grantDrainEntranceR8eCountedZeroExitRemoved
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (v : Fin n)
    (hCounted : GrantDrainEntranceCountedZero ring N v)
    (hRight :
      (N (ring.rightNeighbor v)).sg = true ∨
      (N (ring.rightNeighbor v)).l = true) :
    ¬ GrantDrainEntranceSignalDefect ring
        (nativeE ring N v) v ∧
    ¬ GrantDrainEntranceSignalDefect ring
        (canonicalBirth (nativeE ring N v) v) v ∧
    ¬ GrantDrainEntranceSignalDefect ring
        (canonicalBirth (nativeE ring N v)
          (ring.rightNeighbor v)) v := by
  have hEmpty : (N v).b = (0 : Fin 3) := by
    by_cases h : (N v).b = (0 : Fin 3)
    · exact h
    · exact False.elim
        ((grantDrainEntranceR8eBulletDefectFree
          ring N v h) (Or.inl hCounted))
  have hZero : (N v).sg = false := by
    rcases hCounted with
      ⟨p, d, r, k, hSuffix, hSite,
        hOrder, hInside, hAtZero, hEarlier⟩
    rw [hSite]
    exact hAtZero
  have hn : 2 ≤ n := by
    rcases hCounted with
      ⟨p, d, r, k, hSuffix, hSite,
        hOrder, hInside, hAtZero, hEarlier⟩
    have hPos : 1 ≤ r.val := hSuffix.2.1
    have hBound := k.isLt
    omega
  have hDistinct := grantDrainEntranceRightNeighborDistinct
    ring hn v
  have hSignal :
      (nativeE ring N v v).sg = true := by
    simpa [nativeE] using
      (grantDrainEntranceR8eEmptySourceActivated
        (N v) (N (ring.rightNeighbor v))
        hEmpty hZero hRight)
  refine ⟨?_, ?_, ?_⟩
  · exact grantDrainEntranceR8eSignalOneDefectFree
      ring (nativeE ring N v) v hSignal
  · exact grantDrainEntranceR8eBirthSiteDefectFree
      ring (nativeE ring N v) v
  · have hFramed :
        (canonicalBirth (nativeE ring N v)
          (ring.rightNeighbor v) v).sg = true := by
        simp [canonicalBirth, Ne.symm hDistinct, hSignal]
    exact grantDrainEntranceR8eSignalOneDefectFree
      ring
      (canonicalBirth (nativeE ring N v)
        (ring.rightNeighbor v))
      v hFramed

/-- An actual ready-mismatch witness nominates its sector
leader p. The E row places a live bullet at its first follower,
which cannot be a defect. Canonical birth at p preserves that
bullet, and canonical birth at the follower makes it a leader. -/
theorem grantDrainEntranceR8eReadyMismatchExitRemoved
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (v : Fin n)
    (hReady : GrantDrainEntranceReadyMismatch ring N v) :
    ∃ e : Fin n,
      ¬ GrantDrainEntranceSignalDefect ring
        (nativeE ring N e) v ∧
      ¬ GrantDrainEntranceSignalDefect ring
        (canonicalBirth (nativeE ring N e) e) v ∧
      ¬ GrantDrainEntranceSignalDefect ring
        (canonicalBirth (nativeE ring N e)
          (ring.rightNeighbor e)) v := by
  rcases hReady with
    ⟨p, d, hSector, hGap, hSite,
      hBulletFree, hRootReady, hZero⟩
  have hOneInRing : 1 < n := by
    have hd := d.isLt
    omega
  have hn : 2 ≤ n := by omega
  have hNextFollower :
      (N (ring.rightNeighbor p)).l = false := by
    have h := hSector.2.2.2
      (⟨1, hOneInRing⟩ : Fin n)
      (show 0 < 1 from Nat.zero_lt_one) (show 1 < d.val from hGap)
    change (N (ring.rightNeighbor p)).l = false at h
    exact h
  have hNextEmpty :
      (N (ring.rightNeighbor p)).b = (0 : Fin 3) := by
    by_cases h : (N (ring.rightNeighbor p)).b =
        (0 : Fin 3)
    · exact h
    · have hNo := hBulletFree
        (⟨1, hOneInRing⟩ : Fin n) (by omega)
      have hHas : HasBullet N (ring.rightNeighbor p) := h
      exact False.elim (hNo hHas)
  have hNextZero :
      (N (ring.rightNeighbor p)).sg = false := by
    rw [← hSite]
    exact hZero
  have hRow := grantDrainEntranceReadySourceLiteralERow
    (N p) (N (ring.rightNeighbor p))
    hSector.2.1 hRootReady hNextFollower
    hNextEmpty hNextZero
  have hDistinct := grantDrainEntranceRightNeighborDistinct
    ring hn p
  have hNewBullet :
      (nativeE ring N p (ring.rightNeighbor p)).b =
        (2 : Fin 3) := by
    simpa [nativeE, hDistinct] using hRow.2.2.1
  subst v
  refine ⟨p, ?_, ?_, ?_⟩
  · apply grantDrainEntranceR8eBulletDefectFree
      ring (nativeE ring N p) (ring.rightNeighbor p)
    change (nativeE ring N p (ring.rightNeighbor p)).b ≠
      (0 : Fin 3)
    rw [hNewBullet]
    decide
  · apply grantDrainEntranceR8eBulletDefectFree
      ring (canonicalBirth (nativeE ring N p) p)
      (ring.rightNeighbor p)
    change (canonicalBirth (nativeE ring N p)
      p (ring.rightNeighbor p)).b ≠ (0 : Fin 3)
    simp [canonicalBirth, hDistinct, hNewBullet]
  · exact grantDrainEntranceR8eBirthSiteDefectFree
      ring (nativeE ring N p) (ring.rightNeighbor p)

/-- A recursion over the finite run of consecutive zero signals:
from any zero at start, find the first zero whose next site is
one, or the final zero at the given right boundary. No Nat.find
or Finset is used. -/
private theorem grantDrainEntranceR8eFirstZeroExit
    (signal : Nat → Bool) :
    ∀ fuel start : Nat, signal start = false →
      ∃ j : Nat,
        start ≤ j ∧ j ≤ start + fuel ∧
        signal j = false ∧
        (j = start + fuel ∨ signal (j + 1) = true) := by
  intro fuel
  induction fuel with
  | zero =>
      intro start hZero
      exact ⟨start, (by omega), (by omega),
        hZero, Or.inl (by omega)⟩
  | succ fuel ih =>
      intro start hZero
      by_cases hNext : signal (start + 1) = true
      · exact ⟨start, (by omega), (by omega),
          hZero, Or.inr hNext⟩
      · have hNextZero : signal (start + 1) = false := by
          cases hs : signal (start + 1) with
          | false => rfl
          | true => exact False.elim (hNext hs)
        obtain ⟨j, hLo, hHi, hAtZero, hExit⟩ :=
          ih (start + 1) hNextZero
        refine ⟨j, (by omega), (by omega), hAtZero, ?_⟩
        rcases hExit with hEnd | hOne
        · exact Or.inl (by omega)
        · exact Or.inr hOne

/-- Every counted-zero witness has an explicitly nominated
clockwise zero-site edge with either a one or a leader immediately
to its right. This is a finite recursion, not an unchosen edge. -/
theorem grantDrainEntranceR8eCountedZeroExitNominee
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (v : Fin n)
    (hCounted : GrantDrainEntranceCountedZero ring N v) :
    ∃ e : Fin n,
      GrantDrainEntranceCountedZero ring N e ∧
      ((N (ring.rightNeighbor e)).sg = true ∨
       (N (ring.rightNeighbor e)).l = true) := by
  rcases hCounted with
    ⟨p, d, r, k, hSuffix, hSite,
      hOrder, hInside, hZero, hEarlier⟩
  have hFuel :
      k.val + (d.val - 1 - k.val) = d.val - 1 := by
    omega
  obtain ⟨j, hLo, hHi, hAtZero, hExit⟩ :=
    grantDrainEntranceR8eFirstZeroExit
      (fun t => (N (PPL.shiftRight ring p t)).sg)
      (d.val - 1 - k.val) k.val hZero
  have hJInside : j < d.val := by omega
  have hJInRing : j < n := by
    have hd := d.isLt
    omega
  have hNewCounted : GrantDrainEntranceCountedZero
      ring N (PPL.shiftRight ring p j) := by
    exact ⟨p, d, r, (⟨j, hJInRing⟩ : Fin n),
      hSuffix, rfl, (show r.val < j by omega), hJInside,
      hAtZero, hEarlier⟩
  have hRight :
      (N (ring.rightNeighbor
        (PPL.shiftRight ring p j))).sg = true ∨
      (N (ring.rightNeighbor
        (PPL.shiftRight ring p j))).l = true := by
    rw [grantDrainEntranceAheadShiftSucc ring p j]
    rcases hExit with hEnd | hOne
    · right
      have hEq : j + 1 = d.val := by omega
      rw [hEq]
      exact hSuffix.1.2.2.1
    · exact Or.inl hOne
  exact ⟨PPL.shiftRight ring p j, hNewCounted, hRight⟩

/-- The sum of a list of zeros built by `List.ofFn` is zero. -/
private theorem grantDrainEntranceR8eOfFnZeroSum :
    ∀ m : Nat, (List.ofFn (fun _ : Fin m => (0 : Nat))).sum = 0
  | 0 => rfl
  | m + 1 => by
      rw [List.ofFn_succ, List.sum_cons, Nat.zero_add]
      exact grantDrainEntranceR8eOfFnZeroSum m

/-- A positive physical R8e sum contains an actual counted site.
This uses the original List.ofFn scalar, not a replacement rank. -/
theorem grantDrainEntranceR8ePositiveHasDefect
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (hPositive : 0 <
      grantDrainEntranceSignalCleanupPotential ring N) :
    ∃ v : Fin n,
      GrantDrainEntranceSignalDefect ring N v := by
  classical
  by_cases hSome :
      ∃ v : Fin n, GrantDrainEntranceSignalDefect ring N v
  · exact hSome
  · have hNone : ∀ v : Fin n,
        ¬ GrantDrainEntranceSignalDefect ring N v := by
      intro v hv
      exact hSome ⟨v, hv⟩
    have hZero :
        grantDrainEntranceSignalCleanupPotential ring N = 0 := by
      simp [grantDrainEntranceSignalCleanupPotential, hNone]
      exact grantDrainEntranceR8eOfFnZeroSum n
    omega

/-- Genuine all-n progress at ONE named defect site. The source
edge is the leader of a ready-mismatch sector or a recursively
selected zero-exit edge. Every native outcome deletes this one
old defect; no monotonicity elsewhere is claimed here. -/
theorem grantDrainEntranceR8eNativeNomineeSiteLoss
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (hPositive : 0 <
      grantDrainEntranceSignalCleanupPotential ring N) :
    ∃ e v : Fin n,
      GrantDrainEntranceSignalDefect ring N v ∧
      ¬ GrantDrainEntranceSignalDefect ring
        (nativeE ring N e) v ∧
      ¬ GrantDrainEntranceSignalDefect ring
        (canonicalBirth (nativeE ring N e) e) v ∧
      ¬ GrantDrainEntranceSignalDefect ring
        (canonicalBirth (nativeE ring N e)
          (ring.rightNeighbor e)) v := by
  obtain ⟨v, hDefect⟩ :=
    grantDrainEntranceR8ePositiveHasDefect
      ring N hPositive
  rcases hDefect with hCounted | hReady
  · obtain ⟨e, hAt, hRight⟩ :=
      grantDrainEntranceR8eCountedZeroExitNominee
        ring N v hCounted
    obtain ⟨hPlain, hLeft, hRightBirth⟩ :=
      grantDrainEntranceR8eCountedZeroExitRemoved
        ring N e hAt hRight
    exact ⟨e, e, Or.inl hAt,
      hPlain, hLeft, hRightBirth⟩
  · obtain ⟨e, hPlain, hLeft, hRightBirth⟩ :=
      grantDrainEntranceR8eReadyMismatchExitRemoved
        ring N v hReady
    exact ⟨e, v, Or.inr hReady,
      hPlain, hLeft, hRightBirth⟩

end L3.GrantDrainEntrance

/-!
The framed-sector backward implication is proved below.
Native-E leader-death mergers and canonical-birth sector splits
remain unproved in the global defect-backward statement.
The final conditional bridge uses the nominee-site-loss
lemma.
-/

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- An OLD sector is recovered when every selected native record
in the new sector, including its terminal leader, is unchanged. -/
theorem grantDrainEntranceR8eSectorLengthBackwardOfFrame
    {n : Nat} (ring : DirectedRing n)
    (before after : Fin n → CertNative)
    (p : Fin n) (d : Fin (n + 1))
    (hSector : sectorLength ring after p d)
    (hFields : ∀ k : Nat, k ≤ d.val →
      before (PPL.shiftRight ring p k) =
        after (PPL.shiftRight ring p k)) :
    sectorLength ring before p d := by
  obtain ⟨hPos, hRoot, hTerminal, hInternal⟩ := hSector
  have hZeroShift : PPL.shiftRight ring p 0 = p := by
    apply Fin.ext
    simp [PPL.shiftRight, Nat.mod_eq_of_lt p.isLt]
  have hRootEq : before p = after p := by
    simpa only [hZeroShift] using hFields 0 (by omega)
  refine ⟨hPos, ?_, ?_, ?_⟩
  · rw [hRootEq]
    exact hRoot
  · rw [hFields d.val (by omega)]
    exact hTerminal
  · intro k hPositive hInside
    rw [hFields k.val (by omega)]
    exact hInternal k hPositive hInside

/-- A counted zero whose entire sector has identical OLD/NEW
bullet and signal fields was already counted in the OLD sector. -/
theorem grantDrainEntranceR8eCountedBackwardOnFramedSector
    {n : Nat} (ring : DirectedRing n)
    (before after : Fin n → CertNative)
    (p : Fin n) (d : Fin (n + 1))
    (r k v : Fin n)
    (hSuffix : GrantDrainEntranceSignalSuffixSite ring after p d r)
    (hSite : v = PPL.shiftRight ring p k.val)
    (hOrder : r.val < k.val)
    (hInside : k.val < d.val)
    (hZero : (after (PPL.shiftRight ring p k.val)).sg = false)
    (hOne : (after (PPL.shiftRight ring p r.val)).sg = true)
    (hOldSector : sectorLength ring before p d)
    (hFields : ∀ j : Fin n, j.val < d.val →
      before (PPL.shiftRight ring p j.val) =
        after (PPL.shiftRight ring p j.val)) :
    GrantDrainEntranceCountedZero ring before v := by
  have hOldSuffix :
      GrantDrainEntranceSignalSuffixSite ring before p d r := by
    obtain ⟨_, hLower, hUpper, hBulletSuffix⟩ := hSuffix
    refine ⟨hOldSector, hLower, hUpper, ?_⟩
    intro j hj hOldBullet
    have hField := congrArg CertNative.b (hFields j hj)
    have hNewBullet :
        HasBullet after (PPL.shiftRight ring p j.val) := by
      change (after (PPL.shiftRight ring p j.val)).b ≠
        (0 : Fin 3)
      rw [← hField]
      exact hOldBullet
    exact hBulletSuffix j hj hNewBullet
  refine ⟨p, d, r, k, hOldSuffix, hSite,
    hOrder, hInside, ?_, ?_⟩
  · rw [congrArg CertNative.sg (hFields k hInside)]
    exact hZero
  · rw [congrArg CertNative.sg
      (hFields r hOldSuffix.2.2.1)]
    exact hOne

/-- A ready-source anomaly also transports backwards through
an unchanged sector. Its root and first-follower signal bits
are part of the frame hypothesis. -/
theorem grantDrainEntranceR8eReadyBackwardOnFramedSector
    {n : Nat} (ring : DirectedRing n)
    (before after : Fin n → CertNative)
    (p : Fin n) (d : Fin (n + 1))
    (v : Fin n)
    (hSector : sectorLength ring after p d)
    (hGap : 1 < d.val)
    (hSite : v = ring.rightNeighbor p)
    (hNoBullet : ∀ j : Fin n, j.val < d.val →
      ¬ HasBullet after (PPL.shiftRight ring p j.val))
    (hReady : (after p).sg = true)
    (hZero : (after v).sg = false)
    (hOldSector : sectorLength ring before p d)
    (hFields : ∀ j : Fin n, j.val < d.val →
      before (PPL.shiftRight ring p j.val) =
        after (PPL.shiftRight ring p j.val)) :
    GrantDrainEntranceReadyMismatch ring before v := by
  have hZeroInRing : 0 < n := by
    have hd := d.isLt
    omega
  have hOneInRing : 1 < n := by
    have hd := d.isLt
    omega
  have hZeroShift : PPL.shiftRight ring p 0 = p := by
    apply Fin.ext
    simp [PPL.shiftRight, Nat.mod_eq_of_lt p.isLt]
  have hFirstShift :
      PPL.shiftRight ring p 1 = ring.rightNeighbor p := rfl
  have hRootEq : before p = after p := by
    have h := hFields (⟨0, hZeroInRing⟩ : Fin n) (show 0 < d.val by omega)
    simpa only [hZeroShift] using h
  have hFirstEq :
      before (ring.rightNeighbor p) =
        after (ring.rightNeighbor p) := by
    have h := hFields (⟨1, hOneInRing⟩ : Fin n) (by omega)
    simpa only [hFirstShift] using h
  refine ⟨p, d, hOldSector, hGap, hSite, ?_, ?_, ?_⟩
  · intro j hj hOldBullet
    have hField := congrArg CertNative.b (hFields j hj)
    apply hNoBullet j hj
    change (after (PPL.shiftRight ring p j.val)).b ≠
      (0 : Fin 3)
    rw [← hField]
    exact hOldBullet
  · rw [congrArg CertNative.sg hRootEq]
    exact hReady
  · rw [hSite]
    rw [congrArg CertNative.sg hFirstEq]
    rw [hSite] at hZero
    exact hZero

/-- All three exact native outcomes frame arbitrary sites outside
the actual source and responder. -/
theorem grantDrainEntranceR8eNativeOutcomesFrameAway
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (e i : Fin n)
    (he : i ≠ e)
    (hy : i ≠ ring.rightNeighbor e) :
    nativeE ring N e i = N i ∧
    canonicalBirth (nativeE ring N e) e i = N i ∧
    canonicalBirth (nativeE ring N e)
      (ring.rightNeighbor e) i = N i := by
  have hE := grantDrainEntranceNativeEFrame
    ring N e i he hy
  refine ⟨hE, ?_, ?_⟩
  · rw [grantDrainEntranceCanonicalBirthFrame
      (nativeE ring N e) e i he]
    exact hE
  · rw [grantDrainEntranceCanonicalBirthFrame
      (nativeE ring N e) (ring.rightNeighbor e) i hy]
    exact hE

/-- An after-step defect is inherited whenever its entire
witness sector, including the next root, misses both updated
sites. The missing global cases are precisely affected sectors. -/
theorem grantDrainEntranceR8eDefectBackwardOffSelectedSector
    {n : Nat} (ring : DirectedRing n)
    (N M : Fin n → CertNative)
    (e v : Fin n)
    (hOutcome :
      M = nativeE ring N e ∨
      M = canonicalBirth (nativeE ring N e) e ∨
      M = canonicalBirth (nativeE ring N e)
        (ring.rightNeighbor e))
    (hAway :
      ∀ (p : Fin n) (d : Fin (n + 1)),
        sectorLength ring M p d →
        (v = ring.rightNeighbor p ∨
          ∃ k : Fin n, k.val < d.val ∧
            v = PPL.shiftRight ring p k.val) →
        ∀ j : Nat, j ≤ d.val →
          PPL.shiftRight ring p j ≠ e ∧
          PPL.shiftRight ring p j ≠ ring.rightNeighbor e)
    (hDefect : GrantDrainEntranceSignalDefect ring M v) :
    GrantDrainEntranceSignalDefect ring N v := by
  have hFrame : ∀ i : Fin n,
      i ≠ e → i ≠ ring.rightNeighbor e →
      M i = N i := by
    intro i he hy
    obtain ⟨hE, hLeft, hRight⟩ :=
      grantDrainEntranceR8eNativeOutcomesFrameAway
        ring N e i he hy
    rcases hOutcome with hm | hm | hm
    · rw [hm]
      exact hE
    · rw [hm]
      exact hLeft
    · rw [hm]
      exact hRight
  rcases hDefect with hCounted | hReady
  · obtain ⟨p, d, r, k, hSuffix, hSite,
        hOrder, hInside, hZero, hOne⟩ := hCounted
    have hAvoid := hAway p d hSuffix.1
      (Or.inr ⟨k, hInside, hSite⟩)
    have hFields : ∀ j : Nat, j ≤ d.val →
        N (PPL.shiftRight ring p j) =
          M (PPL.shiftRight ring p j) := by
      intro j hj
      obtain ⟨he, hy⟩ := hAvoid j hj
      exact (hFrame _ he hy).symm
    have hOldSector :=
      grantDrainEntranceR8eSectorLengthBackwardOfFrame
        ring N M p d hSuffix.1 hFields
    have hOld := grantDrainEntranceR8eCountedBackwardOnFramedSector
      ring N M p d r k v hSuffix hSite
      hOrder hInside hZero hOne hOldSector
      (fun j hj => hFields j.val (by omega))
    exact Or.inl hOld
  · obtain ⟨p, d, hSector, hGap, hSite,
        hNoBullet, hSignal, hZero⟩ := hReady
    have hAvoid := hAway p d hSector
      (Or.inl hSite)
    have hFields : ∀ j : Nat, j ≤ d.val →
        N (PPL.shiftRight ring p j) =
          M (PPL.shiftRight ring p j) := by
      intro j hj
      obtain ⟨he, hy⟩ := hAvoid j hj
      exact (hFrame _ he hy).symm
    have hOldSector :=
      grantDrainEntranceR8eSectorLengthBackwardOfFrame
        ring N M p d hSector hFields
    have hOld := grantDrainEntranceR8eReadyBackwardOnFramedSector
      ring N M p d v hSector hGap hSite hNoBullet
      hSignal hZero hOldSector
      (fun j hj => hFields j.val (by omega))
    exact Or.inr hOld

/-- Once the all-n global defect-backward producer is supplied,
the sum lemmas and the actual nominee-site loss prove
BOTH physical R8e properties. The producer is a hypothesis, not
an axiom, and is not discharged by this file. -/
theorem grantDrainEntranceR8ePotentialClaimsOfBackward
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (hBackward :
      ∀ (N : Fin n → CertNative) (e : Fin n),
        I ring N →
        ∀ v : Fin n,
          (GrantDrainEntranceSignalDefect ring
            (nativeE ring N e) v →
            GrantDrainEntranceSignalDefect ring N v) ∧
          (GrantDrainEntranceSignalDefect ring
            (canonicalBirth (nativeE ring N e) e) v →
            GrantDrainEntranceSignalDefect ring N v) ∧
          (GrantDrainEntranceSignalDefect ring
            (canonicalBirth (nativeE ring N e)
              (ring.rightNeighbor e)) v →
            GrantDrainEntranceSignalDefect ring N v)) :
    GrantDrainEntranceR8ePotentialNonincrease ring fresh update ∧
    GrantDrainEntranceR8ePotentialNominatedDrop ring fresh update := by
  have hNative :
      ∀ (N : Fin n → CertNative) (e : Fin n),
        I ring N →
        grantDrainEntranceSignalCleanupPotential ring
          (nativeE ring N e) ≤
          grantDrainEntranceSignalCleanupPotential ring N ∧
        grantDrainEntranceSignalCleanupPotential ring
          (canonicalBirth (nativeE ring N e) e) ≤
          grantDrainEntranceSignalCleanupPotential ring N ∧
        grantDrainEntranceSignalCleanupPotential ring
          (canonicalBirth (nativeE ring N e)
            (ring.rightNeighbor e)) ≤
          grantDrainEntranceSignalCleanupPotential ring N := by
    intro N e hI
    have hb := hBackward N e hI
    exact ⟨
      grantDrainEntranceR8ePotentialLeOfDefectBackward
        ring N (nativeE ring N e)
        (fun v h => (hb v).1 h),
      grantDrainEntranceR8ePotentialLeOfDefectBackward
        ring N (canonicalBirth (nativeE ring N e) e)
        (fun v h => (hb v).2.1 h),
      grantDrainEntranceR8ePotentialLeOfDefectBackward
        ring N
        (canonicalBirth (nativeE ring N e)
          (ring.rightNeighbor e))
        (fun v h => (hb v).2.2 h)⟩
  have hNominated :
      ∀ N : Fin n → CertNative,
        I ring N →
        0 < grantDrainEntranceSignalCleanupPotential ring N →
        ∃ e : Fin n,
          grantDrainEntranceSignalCleanupPotential ring
            (nativeE ring N e) <
            grantDrainEntranceSignalCleanupPotential ring N ∧
          grantDrainEntranceSignalCleanupPotential ring
            (canonicalBirth (nativeE ring N e) e) <
            grantDrainEntranceSignalCleanupPotential ring N ∧
          grantDrainEntranceSignalCleanupPotential ring
            (canonicalBirth (nativeE ring N e)
              (ring.rightNeighbor e)) <
            grantDrainEntranceSignalCleanupPotential ring N := by
    intro N hI hPos
    obtain ⟨e, v, hOld, hGoneE, hGoneX, hGoneY⟩ :=
      grantDrainEntranceR8eNativeNomineeSiteLoss
        ring N hPos
    have hb := hBackward N e hI
    refine ⟨e, ?_, ?_, ?_⟩
    · exact grantDrainEntranceR8ePotentialLtOfDefectLoss
        ring N (nativeE ring N e)
        (fun i h => (hb i).1 h) v hOld hGoneE
    · exact grantDrainEntranceR8ePotentialLtOfDefectLoss
        ring N (canonicalBirth (nativeE ring N e) e)
        (fun i h => (hb i).2.1 h) v hOld hGoneX
    · exact grantDrainEntranceR8ePotentialLtOfDefectLoss
        ring N
        (canonicalBirth (nativeE ring N e)
          (ring.rightNeighbor e))
        (fun i h => (hb i).2.2 h) v hOld hGoneY
  exact ⟨
    grantDrainEntranceR8eNonincreaseOfNativeOutcomes
      ring fresh update hNative,
    grantDrainEntranceR8eNominatedDropOfNativeOutcomes
      ring fresh update hNominated⟩

end L3.GrantDrainEntrance

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- Exact finite-site matching interface. Only post-defect sites
must be mapped injectively into old-defect sites; unrelated sites
do not require distinct images. -/
def GrantDrainEntranceR8eDefectInjection
    {n : Nat} (ring : DirectedRing n)
    (before after : Fin n → CertNative) : Prop :=
  ∃ f : Fin n → Fin n,
    (∀ v : Fin n,
      GrantDrainEntranceSignalDefect ring after v →
      GrantDrainEntranceSignalDefect ring before (f v)) ∧
    (∀ v w : Fin n,
      GrantDrainEntranceSignalDefect ring after v →
      GrantDrainEntranceSignalDefect ring after w →
      f v = f w → v = w)

/-- The identity is an injection whenever the stronger
pointwise-backward property holds. This is valid at every n. -/
theorem grantDrainEntranceR8eInjectionOfBackward
    {n : Nat} (ring : DirectedRing n)
    (before after : Fin n → CertNative)
    (hback : ∀ v : Fin n,
      GrantDrainEntranceSignalDefect ring after v →
      GrantDrainEntranceSignalDefect ring before v) :
    GrantDrainEntranceR8eDefectInjection ring before after := by
  refine ⟨fun v => v, ?_, ?_⟩
  · intro v hdef
    exact hback v hdef
  · intro v w _ _ heq
    exact heq

/-- A strictly weaker matching-capacity statement than
pointwise-backward: newly created defect sites may be paid by
old sites whose defect disappears. It is equivalent to scalar
nonincrease, but its gain/loss accounting is locally explicit. -/
noncomputable def GrantDrainEntranceR8eDefectExchange
    {n : Nat} (ring : DirectedRing n)
    (before after : Fin n → CertNative) : Prop := by
  classical
  exact
    (List.ofFn (fun v : Fin n =>
      if (¬ GrantDrainEntranceSignalDefect ring before v) ∧
          GrantDrainEntranceSignalDefect ring after v
      then (1 : Nat) else 0)).sum ≤
    (List.ofFn (fun v : Fin n =>
      if GrantDrainEntranceSignalDefect ring before v ∧
          ¬ GrantDrainEntranceSignalDefect ring after v
      then (1 : Nat) else 0)).sum

/-- Pointwise backward gives zero gain, so it implies the
more flexible gain-versus-loss counting certificate. -/
theorem grantDrainEntranceR8eExchangeOfBackward
    {n : Nat} (ring : DirectedRing n)
    (before after : Fin n → CertNative)
    (hback : ∀ v : Fin n,
      GrantDrainEntranceSignalDefect ring after v →
      GrantDrainEntranceSignalDefect ring before v) :
    GrantDrainEntranceR8eDefectExchange ring before after := by
  classical
  have hnone : ∀ v : Fin n,
      ¬ ((¬ GrantDrainEntranceSignalDefect ring before v) ∧
        GrantDrainEntranceSignalDefect ring after v) := by
    intro v hv
    exact hv.1 (hback v hv.2)
  have hzero :
      (List.ofFn (fun v : Fin n =>
        if (¬ GrantDrainEntranceSignalDefect ring before v) ∧
            GrantDrainEntranceSignalDefect ring after v
        then (1 : Nat) else 0)).sum = 0 := by
    calc
      _ = (List.ofFn (fun _ : Fin n => 0)).sum := by
        apply ofFn_sum_eq
        intro v
        exact if_neg (hnone v)
      _ = 0 := by
        rw [ofFn_sum_const]
        exact Nat.mul_zero _
  unfold GrantDrainEntranceR8eDefectExchange
  rw [hzero]
  exact Nat.zero_le _

/-- An exact all-n balance of old-only, new-only and shared
defects proves scalar potential nonincrease without requiring
that every defect stay at its old physical site. -/
theorem grantDrainEntranceR8ePotentialLeOfExchange
    {n : Nat} (ring : DirectedRing n)
    (before after : Fin n → CertNative)
    (hexchange : GrantDrainEntranceR8eDefectExchange
      ring before after) :
    grantDrainEntranceSignalCleanupPotential ring after ≤
      grantDrainEntranceSignalCleanupPotential ring before := by
  classical
  have hpoint : ∀ v : Fin n,
      (if GrantDrainEntranceSignalDefect ring after v
       then (1 : Nat) else 0) +
      (if GrantDrainEntranceSignalDefect ring before v ∧
          ¬ GrantDrainEntranceSignalDefect ring after v
       then (1 : Nat) else 0) =
      (if GrantDrainEntranceSignalDefect ring before v
       then (1 : Nat) else 0) +
      (if (¬ GrantDrainEntranceSignalDefect ring before v) ∧
          GrantDrainEntranceSignalDefect ring after v
       then (1 : Nat) else 0) := by
    intro v
    by_cases hb : GrantDrainEntranceSignalDefect ring before v
    · by_cases ha : GrantDrainEntranceSignalDefect ring after v
      · simp [hb, ha]
      · simp [hb, ha]
    · by_cases ha : GrantDrainEntranceSignalDefect ring after v
      · simp [hb, ha]
      · simp [hb, ha]
  have hbalance :
      grantDrainEntranceSignalCleanupPotential ring after +
        (List.ofFn (fun v : Fin n =>
          if GrantDrainEntranceSignalDefect ring before v ∧
              ¬ GrantDrainEntranceSignalDefect ring after v
          then (1 : Nat) else 0)).sum =
      grantDrainEntranceSignalCleanupPotential ring before +
        (List.ofFn (fun v : Fin n =>
          if (¬ GrantDrainEntranceSignalDefect ring before v) ∧
              GrantDrainEntranceSignalDefect ring after v
          then (1 : Nat) else 0)).sum := by
    unfold grantDrainEntranceSignalCleanupPotential
    rw [← ofFn_sum_add, ← ofFn_sum_add]
    apply ofFn_sum_eq
    intro v
    exact hpoint v
  have hcredit :
      (List.ofFn (fun v : Fin n =>
        if (¬ GrantDrainEntranceSignalDefect ring before v) ∧
            GrantDrainEntranceSignalDefect ring after v
        then (1 : Nat) else 0)).sum ≤
      (List.ofFn (fun v : Fin n =>
        if GrantDrainEntranceSignalDefect ring before v ∧
            ¬ GrantDrainEntranceSignalDefect ring after v
        then (1 : Nat) else 0)).sum := by
    exact hexchange
  omega

/-- The three actual native projections frame every site that is
neither the selected source nor its responder, including FIRE. -/
theorem grantDrainEntranceR8eNativeOutcomeFrame
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (e v : Fin n)
    (hx : v ≠ e) (hy : v ≠ ring.rightNeighbor e) :
    nativeE ring N e v = N v ∧
    canonicalBirth (nativeE ring N e) e v = N v ∧
    canonicalBirth (nativeE ring N e)
      (ring.rightNeighbor e) v = N v := by
  have hframe := grantDrainEntranceNativeEFrame
    ring N e v hx hy
  refine ⟨hframe, ?_, ?_⟩
  · rw [grantDrainEntranceCanonicalBirthFrame
      (nativeE ring N e) e v hx]
    exact hframe
  · rw [grantDrainEntranceCanonicalBirthFrame
      (nativeE ring N e) (ring.rightNeighbor e) v hy]
    exact hframe

/-- This is the precise weaker source-producer interface:
a gain-versus-loss inequality for each of the three literal
native outcomes suffices for the actual grantDrainStep.
It does not assert the missing all-n native inequalities. -/
theorem grantDrainEntranceR8eNonincreaseOfExchange
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (hNativeExchange :
      ∀ (N : Fin n → CertNative) (e : Fin n),
        I ring N →
        GrantDrainEntranceR8eDefectExchange
          ring N (nativeE ring N e) ∧
        GrantDrainEntranceR8eDefectExchange
          ring N (canonicalBirth (nativeE ring N e) e) ∧
        GrantDrainEntranceR8eDefectExchange
          ring N
            (canonicalBirth (nativeE ring N e)
              (ring.rightNeighbor e))) :
    GrantDrainEntranceR8ePotentialNonincrease ring fresh update := by
  apply grantDrainEntranceR8eNonincreaseOfNativeOutcomes
    ring fresh update
  intro N e hI
  obtain ⟨hPlain, hSourceBirth, hTargetBirth⟩ :=
    hNativeExchange N e hI
  exact ⟨
    grantDrainEntranceR8ePotentialLeOfExchange
      ring N (nativeE ring N e) hPlain,
    grantDrainEntranceR8ePotentialLeOfExchange
      ring N (canonicalBirth (nativeE ring N e) e)
      hSourceBirth,
    grantDrainEntranceR8ePotentialLeOfExchange
      ring N
      (canonicalBirth (nativeE ring N e)
        (ring.rightNeighbor e)) hTargetBirth⟩

end L3.GrantDrainEntrance

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- Sector endpoints and every shiftRight interior position are
unchanged when the leader array is unchanged. -/
theorem grantDrainEntranceR8eSectorLengthOfLeaderArray
    {n : Nat} (ring : DirectedRing n)
    (N M : Fin n → CertNative)
    (hLeaders : ∀ i : Fin n, (M i).l = (N i).l)
    (p : Fin n) (d : Fin (n + 1)) :
    sectorLength ring M p d ↔ sectorLength ring N p d := by
  constructor
  · intro hSector
    obtain ⟨hPos, hRoot, hEnd, hInside⟩ := hSector
    refine ⟨hPos, ?_, ?_, ?_⟩
    · rw [← hLeaders p]
      exact hRoot
    · rw [← hLeaders (PPL.shiftRight ring p d.val)]
      exact hEnd
    · intro k hkPos hkLt
      rw [← hLeaders (PPL.shiftRight ring p k.val)]
      exact hInside k hkPos hkLt
  · intro hSector
    obtain ⟨hPos, hRoot, hEnd, hInside⟩ := hSector
    refine ⟨hPos, ?_, ?_, ?_⟩
    · rw [hLeaders p]
      exact hRoot
    · rw [hLeaders (PPL.shiftRight ring p d.val)]
      exact hEnd
    · intro k hkPos hkLt
      rw [hLeaders (PPL.shiftRight ring p k.val)]
      exact hInside k hkPos hkLt

/-- The ready-source, moving-bullet, and quiet-empty-source E rows
have exactly the old sector roots and lengths, with the same offsets. -/
theorem grantDrainEntranceR8eSectorRowFollowerResponder
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hyFollower : (N (ring.rightNeighbor e)).l = false)
    (p : Fin n) (d : Fin (n + 1)) :
    sectorLength ring (nativeE ring N e) p d ↔
      sectorLength ring N p d := by
  have hDistinct :=
    grantDrainEntranceRightNeighborDistinct ring hn e
  have hResponder :
      (nativeE ring N e (ring.rightNeighbor e)).l =
        (N (ring.rightNeighbor e)).l := by
    have hNew :
        (nativeE ring N e (ring.rightNeighbor e)).l = false := by
      simpa [nativeE, hDistinct] using
        grantDrainEntranceLiteralEFollowerResponderRemains
          (N e) (N (ring.rightNeighbor e)) hyFollower
    exact hNew.trans hyFollower.symm
  have hLeaders :=
    grantDrainEntranceNativeELeadersFixed ring hn N e hResponder
  exact grantDrainEntranceR8eSectorLengthOfLeaderArray
    ring N (nativeE ring N e) hLeaders p d

/-- Both surviving-responder E rows also keep the exact old
sector lengths. The killed-responder case is handled separately. -/
theorem grantDrainEntranceR8eSectorRowLeaderSurvives
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hyLeader : (N (ring.rightNeighbor e)).l = true)
    (hSurvive :
      (nativeE ring N e (ring.rightNeighbor e)).l = true)
    (p : Fin n) (d : Fin (n + 1)) :
    sectorLength ring (nativeE ring N e) p d ↔
      sectorLength ring N p d := by
  have hResponder :
      (nativeE ring N e (ring.rightNeighbor e)).l =
        (N (ring.rightNeighbor e)).l :=
    hSurvive.trans hyLeader.symm
  exact grantDrainEntranceR8eSectorLengthOfLeaderArray
    ring N (nativeE ring N e)
    (grantDrainEntranceNativeELeadersFixed
      ring hn N e hResponder) p d

/-- The death row has either an old unchanged sector or the merge
of precisely two old sectors. At offset t the killed leader is y,
and the immediately preceding offset t-1 is e. This exposes the
existing full merge geometry with an I rather than ILocal input. -/
theorem grantDrainEntranceR8eSectorRowLeaderDeath
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hI : I ring N)
    (hyLeader : (N (ring.rightNeighbor e)).l = true)
    (hDeath :
      (nativeE ring N e (ring.rightNeighbor e)).l = false)
    (p : Fin n) (d : Fin (n + 1))
    (hNew : sectorLength ring (nativeE ring N e) p d) :
    (sectorLength ring N p d ∧
      ∀ k : Nat, k < d.val →
        PPL.shiftRight ring p k ≠ e ∧
        PPL.shiftRight ring p k ≠ ring.rightNeighbor e) ∨
    (∃ t : Fin (n + 1), 0 < t.val ∧ t.val < d.val ∧
      PPL.shiftRight ring p t.val = ring.rightNeighbor e ∧
      PPL.shiftRight ring p (t.val - 1) = e ∧
      sectorLength ring N p t ∧
      sectorLength ring N (ring.rightNeighbor e)
        (⟨d.val - t.val, by omega⟩ : Fin (n + 1))) := by
  exact grantDrainEntranceDeathSectorPartition
    ring hn N e ((grantDrainEntranceIffILocal ring N).mp hI)
    hyLeader hDeath p d hNew

/-- A canonical birth on an EXISTING leader does not change the
leader array or sectorLength, even if the old root bullet/signal
fields are overwritten. -/
theorem grantDrainEntranceR8eSectorRowBirthOldLeader
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (z : Fin n)
    (hzLeader : (N z).l = true)
    (p : Fin n) (d : Fin (n + 1)) :
    sectorLength ring (canonicalBirth N z) p d ↔
      sectorLength ring N p d := by
  have hLeaders :
      ∀ i : Fin n, (canonicalBirth N z i).l = (N i).l := by
    intro i
    by_cases hi : i = z
    · subst i
      simp [canonicalBirth, firedNative, hzLeader]
    · rw [grantDrainEntranceCanonicalBirthFrame N z i hi]
  exact grantDrainEntranceR8eSectorLengthOfLeaderArray
    ring N (canonicalBirth N z) hLeaders p d

/-- A born leader cannot occur at an interior positive offset
of any NEW sector, whether the birth was source-side or
responder-side. -/
theorem grantDrainEntranceR8eBirthInteriorAvoidSite
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (z p : Fin n)
    (d : Fin (n + 1))
    (hSector : sectorLength ring (canonicalBirth N z) p d)
    (j : Fin n) (hjPos : 0 < j.val) (hjLt : j.val < d.val) :
    PPL.shiftRight ring p j.val ≠ z := by
  intro hj
  have hFollower := hSector.2.2.2 j hjPos hjLt
  rw [hj] at hFollower
  rw [(grantDrainEntranceCanonicalBirthAtSite N z).1] at hFollower
  cases hFollower

/-- An old sector not touching the birth site, even at its
terminal leader, remains exactly the same new sector. -/
theorem grantDrainEntranceR8eSectorRowBirthFramed
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (z p : Fin n)
    (d : Fin (n + 1))
    (hSector : sectorLength ring N p d)
    (hAway : ∀ k : Nat, k ≤ d.val →
      PPL.shiftRight ring p k ≠ z) :
    sectorLength ring (canonicalBirth N z) p d := by
  apply grantDrainEntranceR8eSectorLengthBackwardOfFrame
    ring (canonicalBirth N z) N p d hSector
  intro k hk
  exact grantDrainEntranceCanonicalBirthFrame
    N z (PPL.shiftRight ring p k) (hAway k hk)

/-- Exact birth split: an old sector p..next(p) cut at its
strict follower offset t becomes p..z of length t, and
z..next(p) of length d-t. Both shifts retain the old cyclic
offset coordinates; there is no modular-length guess. -/
theorem grantDrainEntranceR8eSectorRowBirthSplit
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (z p : Fin n)
    (d : Fin (n + 1)) (t : Fin n)
    (hOld : sectorLength ring N p d)
    (htPos : 0 < t.val) (htInside : t.val < d.val)
    (hz : PPL.shiftRight ring p t.val = z) :
    sectorLength ring (canonicalBirth N z) p
      (⟨t.val, by omega⟩ : Fin (n + 1)) ∧
    sectorLength ring (canonicalBirth N z) z
      (⟨d.val - t.val, by omega⟩ : Fin (n + 1)) := by
  have hZOldFollower : (N z).l = false := by
    rw [← hz]
    exact hOld.2.2.2 t htPos htInside
  have hpNe : p ≠ z := by
    intro hp
    have hLeaderZ : (N z).l = true := by
      rw [← hp]
      exact hOld.2.1
    rw [hZOldFollower] at hLeaderZ
    cases hLeaderZ
  have hTerminalNe :
      PPL.shiftRight ring p d.val ≠ z := by
    intro he
    have hLeaderZ : (N z).l = true := by
      rw [← he]
      exact hOld.2.2.1
    rw [hZOldFollower] at hLeaderZ
    cases hLeaderZ
  have hIndexUnique : ∀ k : Nat, k < n →
      PPL.shiftRight ring p k = z → k = t.val := by
    intro k hk hAt
    have hIndex :=
      grantDrainEntranceDeathOffsetIndex ring p z k hk hAt
    have hT :=
      grantDrainEntranceDeathOffsetIndex
        ring p z t.val t.isLt hz
    omega
  have hNotZ : ∀ k : Nat, k < n → k ≠ t.val →
      PPL.shiftRight ring p k ≠ z := by
    intro k hk hNe hAt
    exact hNe (hIndexUnique k hk hAt)
  have hRoot :
      (canonicalBirth N z p).l = true := by
    rw [grantDrainEntranceCanonicalBirthFrame N z p hpNe]
    exact hOld.2.1
  have hTerminal :
      (canonicalBirth N z (PPL.shiftRight ring p d.val)).l =
        true := by
    rw [grantDrainEntranceCanonicalBirthFrame N z
      (PPL.shiftRight ring p d.val) hTerminalNe]
    exact hOld.2.2.1
  constructor
  · refine ⟨htPos, hRoot, ?_, ?_⟩
    · rw [hz]
      exact (grantDrainEntranceCanonicalBirthAtSite N z).1
    · intro k hkPos hkLt
      change k.val < t.val at hkLt
      have hkNe := hNotZ k.val k.isLt (by omega)
      rw [grantDrainEntranceCanonicalBirthFrame N z
        (PPL.shiftRight ring p k.val) hkNe]
      exact hOld.2.2.2 k hkPos (by omega)
  · have hShift : ∀ k : Nat,
        PPL.shiftRight ring z k =
          PPL.shiftRight ring p (t.val + k) := by
      intro k
      rw [← hz]
      exact grantDrainEntranceArcShiftRightAdd ring p t.val k
    refine ⟨(show 0 < d.val - t.val by omega),
      (grantDrainEntranceCanonicalBirthAtSite N z).1, ?_, ?_⟩
    · rw [hShift (d.val - t.val),
        show t.val + (d.val - t.val) = d.val by omega]
      exact hTerminal
    · intro k hkPos hkLt
      change k.val < d.val - t.val at hkLt
      have hkIndex : t.val + k.val < d.val := by omega
      have hkNe : PPL.shiftRight ring z k.val ≠ z := by
        rw [hShift k.val]
        exact hNotZ (t.val + k.val) (by omega) (by omega)
      have hOldFollower :
          (N (PPL.shiftRight ring p (t.val + k.val))).l =
            false := by
        have hBound : t.val + k.val < n := by omega
        exact hOld.2.2.2
          (⟨t.val + k.val, hBound⟩ : Fin n)
          (show 0 < t.val + k.val by omega) hkIndex
      rw [grantDrainEntranceCanonicalBirthFrame
        N z (PPL.shiftRight ring z k.val) hkNe, hShift k.val]
      exact hOldFollower

/-- The full pointwise defect backward theorem for the unguarded
birth-at-an-OLD-leader row. It needs no I hypothesis. The changed
root may have had a bullet or a ready signal: a counted-zero
witness is strictly beyond the root, and a new ready mismatch
cannot originate at the now-zero-signal root. -/
theorem grantDrainEntranceR8eBackwardRowBirthOldLeader
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (z v : Fin n)
    (hzLeader : (N z).l = true)
    (hDef : GrantDrainEntranceSignalDefect
      ring (canonicalBirth N z) v) :
    GrantDrainEntranceSignalDefect ring N v := by
  rcases hDef with hCount | hReady
  · obtain ⟨p, d, r, k, hSuffix, hSite,
        hOrder, hInside, hZero, hOne⟩ := hCount
    have hOldSector : sectorLength ring N p d :=
      (grantDrainEntranceR8eSectorRowBirthOldLeader
        ring N z hzLeader p d).mp hSuffix.1
    have hOldSuffix :
        GrantDrainEntranceSignalSuffixSite ring N p d r := by
      refine ⟨hOldSector, hSuffix.2.1, hSuffix.2.2.1, ?_⟩
      intro j hj hOldBullet
      by_cases hjZero : j.val = 0
      · have hLower : 1 ≤ r.val := hSuffix.2.1
        omega
      · have hjAway :=
          grantDrainEntranceR8eBirthInteriorAvoidSite
            ring N z p d hSuffix.1 j (by omega) hj
        have hNewBullet :
            HasBullet (canonicalBirth N z)
              (PPL.shiftRight ring p j.val) := by
          change ((canonicalBirth N z
            (PPL.shiftRight ring p j.val)).b ≠ (0 : Fin 3))
          rw [grantDrainEntranceCanonicalBirthFrame
            N z (PPL.shiftRight ring p j.val) hjAway]
          exact hOldBullet
        exact hSuffix.2.2.2 j hj hNewBullet
    have hkAway :=
      grantDrainEntranceR8eBirthInteriorAvoidSite
        ring N z p d hSuffix.1 k (by omega) hInside
    have hrPos : 0 < r.val := by
      have hLower : 1 ≤ r.val := hSuffix.2.1
      omega
    have hrAway :=
      grantDrainEntranceR8eBirthInteriorAvoidSite
        ring N z p d hSuffix.1 r hrPos hSuffix.2.2.1
    have hOldZero :
        (N (PPL.shiftRight ring p k.val)).sg = false := by
      rw [← grantDrainEntranceCanonicalBirthFrame
        N z (PPL.shiftRight ring p k.val) hkAway]
      exact hZero
    have hOldOne :
        (N (PPL.shiftRight ring p r.val)).sg = true := by
      rw [← grantDrainEntranceCanonicalBirthFrame
        N z (PPL.shiftRight ring p r.val) hrAway]
      exact hOne
    exact Or.inl ⟨p, d, r, k, hOldSuffix, hSite,
      hOrder, hInside, hOldZero, hOldOne⟩
  · obtain ⟨p, d, hSector, hGap, hSite,
        hNoBullet, hReady, hZero⟩ := hReady
    have hOldSector : sectorLength ring N p d :=
      (grantDrainEntranceR8eSectorRowBirthOldLeader
        ring N z hzLeader p d).mp hSector
    have hpNe : p ≠ z := by
      intro hp
      have hImpossible :
          (canonicalBirth N z z).sg = true := by
        rw [hp] at hReady
        exact hReady
      rw [(grantDrainEntranceCanonicalBirthAtSite N z).2.2]
        at hImpossible
      cases hImpossible
    have hFields : ∀ j : Fin n, j.val < d.val →
        N (PPL.shiftRight ring p j.val) =
          canonicalBirth N z (PPL.shiftRight ring p j.val) := by
      intro j hj
      by_cases hjZero : j.val = 0
      · have hAtRoot :
            PPL.shiftRight ring p j.val = p := by
          rw [hjZero]
          apply Fin.ext
          simp [PPL.shiftRight, Nat.mod_eq_of_lt p.isLt]
        have hAway :
            PPL.shiftRight ring p j.val ≠ z := by
          rw [hAtRoot]
          exact hpNe
        exact (grantDrainEntranceCanonicalBirthFrame
          N z (PPL.shiftRight ring p j.val) hAway).symm
      · have hAway :=
          grantDrainEntranceR8eBirthInteriorAvoidSite
            ring N z p d hSector j (by omega) hj
        exact (grantDrainEntranceCanonicalBirthFrame
          N z (PPL.shiftRight ring p j.val) hAway).symm
    exact Or.inr
      (grantDrainEntranceR8eReadyBackwardOnFramedSector
        ring N (canonicalBirth N z) p d v hSector hGap
        hSite hNoBullet hReady hZero hOldSector hFields)

end L3.GrantDrainEntrance

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-- COMPLETE E ROW: non-ready empty source, follower responder.
The leader/bullet arrays are literally fixed. The only possible
new signal-one is at e, copied from y. If a NEW counted-zero
uses e as its first one, then old y is already a one and y
is strictly before that zero. The ready-mismatch case cannot
arise anew at e: when e is the ready root, y is its first
follower and must itself have signal one. No I is required. -/
theorem grantDrainEntranceR8eBackwardRowQuietEmpty
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (N : Fin n → CertNative) (e v : Fin n)
    (hxNotReady :
      (N e).l = false ∨ (N e).sg = false)
    (hxEmpty : (N e).b = (0 : Fin 3))
    (hyFollower : (N (ring.rightNeighbor e)).l = false)
    (hDef : GrantDrainEntranceSignalDefect
      ring (nativeE ring N e) v) :
    GrantDrainEntranceSignalDefect ring N v := by
  have hRows :=
    grantDrainEntranceQuietEmptySourceNativeERows
      ring hn N e hxNotReady hxEmpty hyFollower
  have hSectors :
      ∀ (p : Fin n) (d : Fin (n + 1)),
        sectorLength ring (nativeE ring N e) p d ↔
          sectorLength ring N p d := by
    intro p d
    exact grantDrainEntranceR8eSectorLengthOfLeaderArray
      ring N (nativeE ring N e)
      (fun i => (hRows.1 i).1) p d
  have hSignalAway :
      ∀ i : Fin n, i ≠ e →
        (nativeE ring N e i).sg = (N i).sg := by
    intro i hi
    by_cases hy : i = ring.rightNeighbor e
    · subst i
      exact hRows.2.2
    · rw [grantDrainEntranceNativeEFrame ring N e i hi hy]
  have hZeroBack :
      ∀ i : Fin n, (nativeE ring N e i).sg = false →
        (N i).sg = false := by
    intro i hNewZero
    by_cases hi : i = e
    · subst i
      rw [hRows.2.1] at hNewZero
      cases hOld : (N e).sg with
      | false => rfl
      | true =>
          rw [hOld] at hNewZero
          cases hNewZero
    · rw [hSignalAway i hi] at hNewZero
      exact hNewZero
  rcases hDef with hCount | hReady
  · obtain ⟨p, d, r, k, hSuffix, hSite,
        hOrder, hInside, hZero, hOne⟩ := hCount
    have hOldSector : sectorLength ring N p d :=
      (hSectors p d).mp hSuffix.1
    have hOldSuffix :
        GrantDrainEntranceSignalSuffixSite ring N p d r := by
      refine ⟨hOldSector, hSuffix.2.1, hSuffix.2.2.1, ?_⟩
      intro j hj hOldBullet
      have hNewBullet :
          HasBullet (nativeE ring N e)
            (PPL.shiftRight ring p j.val) := by
        change (nativeE ring N e
          (PPL.shiftRight ring p j.val)).b ≠ (0 : Fin 3)
        rw [(hRows.1 (PPL.shiftRight ring p j.val)).2]
        exact hOldBullet
      exact hSuffix.2.2.2 j hj hNewBullet
    have hOldZero :
        (N (PPL.shiftRight ring p k.val)).sg = false :=
      hZeroBack (PPL.shiftRight ring p k.val) hZero
    by_cases hrAtSource : PPL.shiftRight ring p r.val = e
    · by_cases hOldOneAtSource : (N e).sg = true
      · have hOldOne :
            (N (PPL.shiftRight ring p r.val)).sg = true := by
          rw [hrAtSource]
          exact hOldOneAtSource
        exact Or.inl ⟨p, d, r, k, hOldSuffix, hSite,
          hOrder, hInside, hOldZero, hOldOne⟩
      · have hxZero : (N e).sg = false := by
          cases hx : (N e).sg with
          | false => rfl
          | true => exact False.elim (hOldOneAtSource hx)
        have hAtSource :
            (nativeE ring N e e).sg = true := by
          rw [hrAtSource] at hOne
          exact hOne
        rw [hRows.2.1, hxZero] at hAtSource
        have hyOne :
            (N (ring.rightNeighbor e)).sg = true := by
          cases hy : (N (ring.rightNeighbor e)).sg with
          | false =>
              rw [hy] at hAtSource
              cases hAtSource
          | true => rfl
        have hNextShift :
            PPL.shiftRight ring p (r.val + 1) =
              ring.rightNeighbor e := by
          calc
            PPL.shiftRight ring p (r.val + 1) =
                ring.rightNeighbor
                  (PPL.shiftRight ring p r.val) :=
              (grantDrainEntranceAheadShiftSucc ring p r.val).symm
            _ = ring.rightNeighbor e := by rw [hrAtSource]
        have hNextNotK : r.val + 1 ≠ k.val := by
          intro heq
          have hKAtY :
              PPL.shiftRight ring p k.val =
                ring.rightNeighbor e := by
            rw [← heq]
            exact hNextShift
          have hContradiction := hZero
          rw [hKAtY, hRows.2.2, hyOne] at hContradiction
          cases hContradiction
        have hNextBound : r.val + 1 < n := by omega
        have hOldSuffixNext :
            GrantDrainEntranceSignalSuffixSite ring N p d
              (⟨r.val + 1, hNextBound⟩ : Fin n) := by
          refine ⟨hOldSector,
            (show 1 ≤ r.val + 1 by omega),
            (show r.val + 1 < d.val by omega), ?_⟩
          intro j hj hOldBullet
          have hNewBullet :
              HasBullet (nativeE ring N e)
                (PPL.shiftRight ring p j.val) := by
            change (nativeE ring N e
              (PPL.shiftRight ring p j.val)).b ≠ (0 : Fin 3)
            rw [(hRows.1 (PPL.shiftRight ring p j.val)).2]
            exact hOldBullet
          have hBefore := hSuffix.2.2.2 j hj hNewBullet
          change j.val < r.val at hBefore
          change j.val < r.val + 1
          omega
        have hNextOne :
            (N (PPL.shiftRight ring p
              (⟨r.val + 1, hNextBound⟩ : Fin n).val)).sg =
                true := by
          change (N (PPL.shiftRight ring p (r.val + 1))).sg = true
          rw [hNextShift]
          exact hyOne
        exact Or.inl ⟨p, d,
          (⟨r.val + 1, hNextBound⟩ : Fin n), k,
          hOldSuffixNext, hSite,
          (show r.val + 1 < k.val by omega),
          hInside, hOldZero, hNextOne⟩
    · have hOldOne :
          (N (PPL.shiftRight ring p r.val)).sg = true := by
        rw [← hSignalAway
          (PPL.shiftRight ring p r.val) hrAtSource]
        exact hOne
      exact Or.inl ⟨p, d, r, k, hOldSuffix, hSite,
        hOrder, hInside, hOldZero, hOldOne⟩
  · obtain ⟨p, d, hSector, hGap, hSite,
        hNoBullet, hReady, hZero⟩ := hReady
    have hOldSector : sectorLength ring N p d :=
      (hSectors p d).mp hSector
    have hOldNoBullet : ∀ j : Fin n, j.val < d.val →
        ¬ HasBullet N (PPL.shiftRight ring p j.val) := by
      intro j hj hOldBullet
      apply hNoBullet j hj
      change (nativeE ring N e
        (PPL.shiftRight ring p j.val)).b ≠ (0 : Fin 3)
      rw [(hRows.1 (PPL.shiftRight ring p j.val)).2]
      exact hOldBullet
    have hOldReady : (N p).sg = true := by
      by_cases hp : p = e
      · have hYZero :
            (N (ring.rightNeighbor e)).sg = false := by
          have hz := hZero
          rw [hSite, hp, hRows.2.2] at hz
          exact hz
        have hNewAtE :
            (nativeE ring N e e).sg = true := by
          rw [hp] at hReady
          exact hReady
        rw [hRows.2.1, hYZero] at hNewAtE
        rw [hp]
        simpa using hNewAtE
      · have hAt := hSignalAway p hp
        rw [hAt] at hReady
        exact hReady
    have hOldZero : (N v).sg = false :=
      hZeroBack v hZero
    exact Or.inr ⟨p, d, hOldSector, hGap, hSite,
      hOldNoBullet, hOldReady, hOldZero⟩

end L3.GrantDrainEntrance

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-- A second exact E subrow: a signal-one empty follower immediately
before a quiet leader is an E fixed point, even if that leader
already has a DUMMY or LIVE bullet. -/
theorem grantDrainEntranceR8eQuietLeaderSilentPair
    (x y : CertNative)
    (hxFollower : x.l = false)
    (hxEmpty : x.b = (0 : Fin 3))
    (hxOne : x.sg = true)
    (hyLeader : y.l = true)
    (hyQuiet : y.sg = false) :
    certLiteralEPair x y = (x, y) := by
  rcases x with ⟨xl, xb, xsh, xsg⟩
  rcases y with ⟨yl, yb, ysh, ysg⟩
  change xl = false at hxFollower
  change xb = (0 : Fin 3) at hxEmpty
  change xsg = true at hxOne
  change yl = true at hyLeader
  change ysg = false at hyQuiet
  subst xl
  subst xb
  subst xsg
  subst yl
  subst ysg
  rcases grantDrainEntranceLocalFinThreeCases yb with hb | hb | hb <;>
    subst yb <;>
    simp [certLiteralEPair, certFinThree]

theorem grantDrainEntranceR8eQuietLeaderSilentNativeIdentity
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hxFollower : (N e).l = false)
    (hxEmpty : (N e).b = (0 : Fin 3))
    (hxOne : (N e).sg = true)
    (hyLeader : (N (ring.rightNeighbor e)).l = true)
    (hyQuiet : (N (ring.rightNeighbor e)).sg = false) :
    nativeE ring N e = N := by
  have hPair := grantDrainEntranceR8eQuietLeaderSilentPair
    (N e) (N (ring.rightNeighbor e))
    hxFollower hxEmpty hxOne hyLeader hyQuiet
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

/-- COMPLETE E SUBROW, quiet surviving leader, silent interaction. -/
theorem grantDrainEntranceR8eBackwardRowQuietLeaderSilent
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (N : Fin n → CertNative) (e v : Fin n)
    (hxFollower : (N e).l = false)
    (hxEmpty : (N e).b = (0 : Fin 3))
    (hxOne : (N e).sg = true)
    (hyLeader : (N (ring.rightNeighbor e)).l = true)
    (hyQuiet : (N (ring.rightNeighbor e)).sg = false)
    (hDef : GrantDrainEntranceSignalDefect
      ring (nativeE ring N e) v) :
    GrantDrainEntranceSignalDefect ring N v := by
  rw [grantDrainEntranceR8eQuietLeaderSilentNativeIdentity
    ring hn N e hxFollower hxEmpty hxOne hyLeader hyQuiet] at hDef
  exact hDef

/-- COMPLETE two-stage source-birth subrow: an old quiet leader
with an empty bullet register serves a follower, then an
unguarded canonicalBirth overwrites that same leader.
The E backward part is the full quiet-empty theorem above,
and birth at an old leader was proved independently. -/
theorem grantDrainEntranceR8eBackwardRowQuietSourceBirth
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (N : Fin n → CertNative) (e v : Fin n)
    (hxLeader : (N e).l = true)
    (hxQuiet : (N e).sg = false)
    (hxEmpty : (N e).b = (0 : Fin 3))
    (hyFollower : (N (ring.rightNeighbor e)).l = false)
    (hDef : GrantDrainEntranceSignalDefect
      ring (canonicalBirth (nativeE ring N e) e) v) :
    GrantDrainEntranceSignalDefect ring N v := by
  have hSourceLeader :
      (nativeE ring N e e).l = true := by
    have hPair :=
      grantDrainEntranceLiteralESourceLeaderFixed
        (N e) (N (ring.rightNeighbor e))
    simpa [nativeE] using hPair.trans hxLeader
  have hMid :=
    grantDrainEntranceR8eBackwardRowBirthOldLeader
      ring (nativeE ring N e) e v hSourceLeader hDef
  exact grantDrainEntranceR8eBackwardRowQuietEmpty
    ring hn N e v (Or.inr hxQuiet)
    hxEmpty hyFollower hMid

/-- COMPLETE two-stage responder-birth subrow: the exact E fixed
point above followed by an unguarded birth on the old quiet
responder leader. This covers a genuine branch of the stronger
unguarded right-birth producer, not merely an eligible FIRE. -/
theorem grantDrainEntranceR8eBackwardRowQuietLeaderBirth
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (N : Fin n → CertNative) (e v : Fin n)
    (hxFollower : (N e).l = false)
    (hxEmpty : (N e).b = (0 : Fin 3))
    (hxOne : (N e).sg = true)
    (hyLeader : (N (ring.rightNeighbor e)).l = true)
    (hyQuiet : (N (ring.rightNeighbor e)).sg = false)
    (hDef : GrantDrainEntranceSignalDefect
      ring (canonicalBirth (nativeE ring N e)
        (ring.rightNeighbor e)) v) :
    GrantDrainEntranceSignalDefect ring N v := by
  have hIdentity :=
    grantDrainEntranceR8eQuietLeaderSilentNativeIdentity
      ring hn N e hxFollower hxEmpty hxOne hyLeader hyQuiet
  have hOldLeader :
      (nativeE ring N e (ring.rightNeighbor e)).l = true := by
    rw [hIdentity]
    exact hyLeader
  have hMid :=
    grantDrainEntranceR8eBackwardRowBirthOldLeader
      ring (nativeE ring N e) (ring.rightNeighbor e)
      v hOldLeader hDef
  rw [hIdentity] at hMid
  exact hMid

end L3.GrantDrainEntrance

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-- If e is in a sector and its successor y is a follower, y is
at the strictly next offset IN that same sector. In particular,
e cannot be its last follower. -/
theorem grantDrainEntranceR8eFollowerSuccessorInside
    {n : Nat} (ring : DirectedRing n)
    (M : Fin n → CertNative)
    (p : Fin n) (d : Fin (n + 1))
    (hSector : sectorLength ring M p d)
    (e : Fin n)
    (hyFollower : (M (ring.rightNeighbor e)).l = false)
    (j : Fin n) (hjInside : j.val < d.val)
    (hjAt : PPL.shiftRight ring p j.val = e) :
    j.val + 1 < d.val ∧
      PPL.shiftRight ring p (j.val + 1) =
        ring.rightNeighbor e := by
  have hNext :
      PPL.shiftRight ring p (j.val + 1) =
        ring.rightNeighbor e := by
    calc
      PPL.shiftRight ring p (j.val + 1) =
          ring.rightNeighbor (PPL.shiftRight ring p j.val) :=
        (grantDrainEntranceAheadShiftSucc ring p j.val).symm
      _ = ring.rightNeighbor e := by rw [hjAt]
  by_cases hLt : j.val + 1 < d.val
  · exact ⟨hLt, hNext⟩
  · have hEq : j.val + 1 = d.val := by omega
    have hAtEnd :
        (M (ring.rightNeighbor e)).l = true := by
      rw [← hNext, hEq]
      exact hSector.2.2.1
    rw [hyFollower] at hAtEnd
    cases hAtEnd

/-- COMPLETE E ROW: an existing bullet moves from e to the
follower y. The new bullet is at the immediately later offset,
so any new suffix witness lies after the old bullet as well.
The new e/y signals are both zero; neither can newly witness a
counted inversion. A bullet-free new sector avoids both sites
entirely. The I hypothesis is only used for the literal E
endpoint row (empty y and zero old bullet signal). -/
theorem grantDrainEntranceR8eBackwardRowMovingBullet
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (N : Fin n → CertNative) (e v : Fin n)
    (hI : I ring N)
    (hyFollower : (N (ring.rightNeighbor e)).l = false)
    (hxBullet : HasBullet N e)
    (hDef : GrantDrainEntranceSignalDefect
      ring (nativeE ring N e) v) :
    GrantDrainEntranceSignalDefect ring N v := by
  have hLocal : GrantDrainEntranceILocal ring N :=
    (grantDrainEntranceIffILocal ring N).mp hI
  have hxZero :=
    grantDrainEntranceILocalBulletSignalZero
      ring N hLocal e hxBullet
  have hyEmpty :=
    grantDrainEntranceILocalFollowerBulletNextEmpty
      ring N e hLocal hxBullet hyFollower
  have hPair :=
    grantDrainEntranceLiteralEBulletToFollower
      (N e) (N (ring.rightNeighbor e))
      hxBullet hxZero hyFollower hyEmpty
  have hDistinct :=
    grantDrainEntranceRightNeighborDistinct ring hn e
  have hNewSourceZero :
      (nativeE ring N e e).sg = false := by
    simpa [nativeE] using hPair.2.1
  have hNewTargetZero :
      (nativeE ring N e (ring.rightNeighbor e)).sg = false := by
    simpa [nativeE, hDistinct] using hPair.2.2.2
  have hNewTargetBullet :
      HasBullet (nativeE ring N e) (ring.rightNeighbor e) := by
    have hTarget :
        (nativeE ring N e (ring.rightNeighbor e)).b =
          (N e).b := by
      simpa [nativeE, hDistinct] using hPair.2.2.1
    change (nativeE ring N e (ring.rightNeighbor e)).b ≠
      (0 : Fin 3)
    rw [hTarget]
    exact hxBullet
  have hNewTargetFollower :
      (nativeE ring N e (ring.rightNeighbor e)).l = false := by
    simpa [nativeE, hDistinct] using
      grantDrainEntranceLiteralEFollowerResponderRemains
        (N e) (N (ring.rightNeighbor e)) hyFollower
  have hSectorEq :
      ∀ (p : Fin n) (d : Fin (n + 1)),
        sectorLength ring (nativeE ring N e) p d ↔
          sectorLength ring N p d := by
    intro p d
    exact grantDrainEntranceR8eSectorRowFollowerResponder
      ring hn N e hyFollower p d
  rcases hDef with hCount | hReady
  · obtain ⟨p, d, r, k, hSuffix, hSite, hOrder,
        hInside, hZero, hOne⟩ := hCount
    have hOldSector : sectorLength ring N p d :=
      (hSectorEq p d).mp hSuffix.1
    have hOldSuffix :
        GrantDrainEntranceSignalSuffixSite ring N p d r := by
      refine ⟨hOldSector, hSuffix.2.1, hSuffix.2.2.1, ?_⟩
      intro j hj hOldBullet
      by_cases hAtSource :
          PPL.shiftRight ring p j.val = e
      · have hNext :=
          grantDrainEntranceR8eFollowerSuccessorInside
            ring (nativeE ring N e) p d hSuffix.1 e
            hNewTargetFollower j hj hAtSource
        have hBound : j.val + 1 < n := by omega
        have hBullet :
            HasBullet (nativeE ring N e)
              (PPL.shiftRight ring p (j.val + 1)) := by
          rw [hNext.2]
          exact hNewTargetBullet
        have hBefore := hSuffix.2.2.2
          (⟨j.val + 1, hBound⟩ : Fin n)
          (show j.val + 1 < d.val by exact hNext.1) hBullet
        change j.val + 1 < r.val at hBefore
        omega
      · by_cases hAtTarget :
            PPL.shiftRight ring p j.val = ring.rightNeighbor e
        · have hOldTargetBullet :
              HasBullet N (ring.rightNeighbor e) := by
            rw [← hAtTarget]
            exact hOldBullet
          exact False.elim (hOldTargetBullet hyEmpty)
        · have hNewBullet :
              HasBullet (nativeE ring N e)
                (PPL.shiftRight ring p j.val) := by
            change (nativeE ring N e
              (PPL.shiftRight ring p j.val)).b ≠
                (0 : Fin 3)
            rw [grantDrainEntranceNativeEFrame
              ring N e (PPL.shiftRight ring p j.val)
              hAtSource hAtTarget]
            exact hOldBullet
          exact hSuffix.2.2.2 j hj hNewBullet
    have hkNotSource :
        PPL.shiftRight ring p k.val ≠ e := by
      intro hkAtSource
      have hNext :=
        grantDrainEntranceR8eFollowerSuccessorInside
          ring (nativeE ring N e) p d hSuffix.1 e
          hNewTargetFollower k hInside hkAtSource
      have hBound : k.val + 1 < n := by omega
      have hBullet :
          HasBullet (nativeE ring N e)
            (PPL.shiftRight ring p (k.val + 1)) := by
        rw [hNext.2]
        exact hNewTargetBullet
      have hBefore := hSuffix.2.2.2
        (⟨k.val + 1, hBound⟩ : Fin n)
        (show k.val + 1 < d.val by exact hNext.1) hBullet
      change k.val + 1 < r.val at hBefore
      omega
    have hkNotTarget :
        PPL.shiftRight ring p k.val ≠
          ring.rightNeighbor e := by
      intro hkAtTarget
      have hBullet :
          HasBullet (nativeE ring N e)
            (PPL.shiftRight ring p k.val) := by
        rw [hkAtTarget]
        exact hNewTargetBullet
      have hBefore := hSuffix.2.2.2 k hInside hBullet
      omega
    have hrNotSource :
        PPL.shiftRight ring p r.val ≠ e := by
      intro hrAtSource
      have hContradiction := hOne
      rw [hrAtSource, hNewSourceZero] at hContradiction
      cases hContradiction
    have hrNotTarget :
        PPL.shiftRight ring p r.val ≠
          ring.rightNeighbor e := by
      intro hrAtTarget
      have hContradiction := hOne
      rw [hrAtTarget, hNewTargetZero] at hContradiction
      cases hContradiction
    have hOldZero :
        (N (PPL.shiftRight ring p k.val)).sg = false := by
      rw [← grantDrainEntranceNativeEFrame
        ring N e (PPL.shiftRight ring p k.val)
        hkNotSource hkNotTarget]
      exact hZero
    have hOldOne :
        (N (PPL.shiftRight ring p r.val)).sg = true := by
      rw [← grantDrainEntranceNativeEFrame
        ring N e (PPL.shiftRight ring p r.val)
        hrNotSource hrNotTarget]
      exact hOne
    exact Or.inl ⟨p, d, r, k, hOldSuffix, hSite,
      hOrder, hInside, hOldZero, hOldOne⟩
  · obtain ⟨p, d, hSector, hGap, hSite,
        hNoBullet, hSignal, hZero⟩ := hReady
    have hNoTarget :
        ∀ j : Fin n, j.val < d.val →
          PPL.shiftRight ring p j.val ≠ ring.rightNeighbor e := by
      intro j hj hAtTarget
      have hBullet :
          HasBullet (nativeE ring N e)
            (PPL.shiftRight ring p j.val) := by
        rw [hAtTarget]
        exact hNewTargetBullet
      exact (hNoBullet j hj) hBullet
    have hNoSource :
        ∀ j : Fin n, j.val < d.val →
          PPL.shiftRight ring p j.val ≠ e := by
      intro j hj hAtSource
      have hNext :=
        grantDrainEntranceR8eFollowerSuccessorInside
          ring (nativeE ring N e) p d hSector e
          hNewTargetFollower j hj hAtSource
      have hBound : j.val + 1 < n := by omega
      have hAtTarget := hNoTarget
        (⟨j.val + 1, hBound⟩ : Fin n)
        (show j.val + 1 < d.val by exact hNext.1)
      exact hAtTarget hNext.2
    have hFields : ∀ j : Fin n, j.val < d.val →
        N (PPL.shiftRight ring p j.val) =
          nativeE ring N e (PPL.shiftRight ring p j.val) := by
      intro j hj
      exact (grantDrainEntranceNativeEFrame
        ring N e (PPL.shiftRight ring p j.val)
        (hNoSource j hj) (hNoTarget j hj)).symm
    have hOldSector : sectorLength ring N p d :=
      (hSectorEq p d).mp hSector
    exact Or.inr
      (grantDrainEntranceR8eReadyBackwardOnFramedSector
        ring N (nativeE ring N e) p d v
        hSector hGap hSite hNoBullet hSignal hZero
        hOldSector hFields)

end L3.GrantDrainEntrance

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-- Clockwise offsets below n have unique sites, including a
wraparound at the physical zero position. -/
theorem grantDrainEntranceR8eShiftIndexInjective
    {n : Nat} (ring : DirectedRing n)
    (p : Fin n) (a b : Nat)
    (ha : a < n) (hb : b < n)
    (h : PPL.shiftRight ring p a = PPL.shiftRight ring p b) :
    a = b := by
  have hA := grantDrainEntranceDeathOffsetShift ring p a ha
  have hB := grantDrainEntranceDeathOffsetShift ring p b hb
  rw [h] at hA
  omega

theorem grantDrainEntranceR8eShiftZero
    {n : Nat} (ring : DirectedRing n) (p : Fin n) :
    PPL.shiftRight ring p 0 = p := by
  apply Fin.ext
  simp [PPL.shiftRight, Nat.mod_eq_of_lt p.isLt]

/-- No sector rooted at p != e can contain e OR its follower y
as a site before the terminal leader when e itself is a leader.
The y argument walks one step backward using successor
injectivity, even across wraparound. -/
theorem grantDrainEntranceR8eReadySourceOtherSectorFrame
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (M : Fin n → CertNative)
    (e p : Fin n) (d : Fin (n + 1))
    (hSector : sectorLength ring M p d)
    (heLeader : (M e).l = true)
    (hyFollower : (M (ring.rightNeighbor e)).l = false)
    (hpNe : p ≠ e) :
    ∀ j : Fin n, j.val < d.val →
      PPL.shiftRight ring p j.val ≠ e ∧
      PPL.shiftRight ring p j.val ≠ ring.rightNeighbor e := by
  intro j hj
  have hNoE : PPL.shiftRight ring p j.val ≠ e := by
    intro hAt
    by_cases hjZero : j.val = 0
    · have hpEq : p = e := by
        have hRoot := hAt
        rw [hjZero, grantDrainEntranceR8eShiftZero ring p] at hRoot
        exact hRoot
      exact hpNe hpEq
    · have hFollower := hSector.2.2.2 j (by omega) hj
      rw [hAt, heLeader] at hFollower
      cases hFollower
  have hNoY :
      PPL.shiftRight ring p j.val ≠ ring.rightNeighbor e := by
    intro hAt
    by_cases hjZero : j.val = 0
    · have hpEq : p = ring.rightNeighbor e := by
        have hRoot := hAt
        rw [hjZero, grantDrainEntranceR8eShiftZero ring p] at hRoot
        exact hRoot
      have hTrue : (M (ring.rightNeighbor e)).l = true := by
        rw [← hpEq]
        exact hSector.2.1
      rw [hyFollower] at hTrue
      cases hTrue
    · have hPrev :
          PPL.shiftRight ring p (j.val - 1) = e := by
        have hStep :=
          grantDrainEntranceAheadShiftSucc ring p (j.val - 1)
        have hIndex : j.val - 1 + 1 = j.val := by omega
        rw [hIndex, hAt] at hStep
        exact (grantDrainEntranceESuccessorInjective ring hn) hStep
      by_cases hjOne : j.val = 1
      · have hpEq : p = e := by
          have hPrevZero := hPrev
          rw [hjOne] at hPrevZero
          have hZero : 1 - 1 = 0 := by omega
          rw [hZero, grantDrainEntranceR8eShiftZero ring p]
            at hPrevZero
          exact hPrevZero
        exact hpNe hpEq
      · have hBound : j.val - 1 < n := by omega
        have hOldFollower :=
          hSector.2.2.2
            (⟨j.val - 1, hBound⟩ : Fin n)
            (show 0 < j.val - 1 by omega)
            (show j.val - 1 < d.val by omega)
        change (M (PPL.shiftRight ring p (j.val - 1))).l =
          false at hOldFollower
        rw [hPrev, heLeader] at hOldFollower
        cases hOldFollower
  exact ⟨hNoE, hNoY⟩

/-- COMPLETE E ROW: a ready source leader sends a LIVE bullet to
its first follower. Its old I sector is entirely bullet-free.
Every counted-zero witness in the new source sector is strictly
past the new first-follower bullet, so it was already counted
before. Other sectors are literally framed. A ready mismatch
at the source root is impossible after E (root signal becomes 0). -/
theorem grantDrainEntranceR8eBackwardRowReadySource
    {n : Nat} (ring : DirectedRing n) (hn : 3 ≤ n)
    (N : Fin n → CertNative) (e v : Fin n)
    (hI : I ring N)
    (hxLeader : (N e).l = true)
    (hxReady : (N e).sg = true)
    (hyFollower : (N (ring.rightNeighbor e)).l = false)
    (hDef : GrantDrainEntranceSignalDefect
      ring (nativeE ring N e) v) :
    GrantDrainEntranceSignalDefect ring N v := by
  have hLocal : GrantDrainEntranceILocal ring N :=
    (grantDrainEntranceIffILocal ring N).mp hI
  have hRow :=
    grantDrainEntranceILocalReadySourceNativeE
      ring hn N e hLocal hxLeader hxReady hyFollower
  have hDistinct :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  have hNewELeader :
      (nativeE ring N e e).l = true := by
    simpa [nativeE] using
      (grantDrainEntranceLiteralESourceLeaderFixed
        (N e) (N (ring.rightNeighbor e))).trans hxLeader
  have hNewYFollower :
      (nativeE ring N e (ring.rightNeighbor e)).l = false := by
    simpa [nativeE, hDistinct] using
      grantDrainEntranceLiteralEFollowerResponderRemains
        (N e) (N (ring.rightNeighbor e)) hyFollower
  have hNewYBullet :
      HasBullet (nativeE ring N e) (ring.rightNeighbor e) := by
    change (nativeE ring N e (ring.rightNeighbor e)).b ≠
      (0 : Fin 3)
    rw [hRow.2.2.2.1]
    decide
  have hNewEZero :
      (nativeE ring N e e).sg = false :=
    hRow.2.2.1
  have hSectorEq :
      ∀ (p : Fin n) (d : Fin (n + 1)),
        sectorLength ring (nativeE ring N e) p d ↔
          sectorLength ring N p d := by
    intro p d
    exact grantDrainEntranceR8eSectorRowFollowerResponder
      ring (by omega : 2 ≤ n) N e hyFollower p d
  rcases hDef with hCount | hReady
  · obtain ⟨p, d, r, k, hSuffix, hSite, hOrder,
        hInside, hZero, hOne⟩ := hCount
    have hOldSector : sectorLength ring N p d :=
      (hSectorEq p d).mp hSuffix.1
    by_cases hp : p = e
    · subst p
      have hFirstInside : 1 < d.val := by
        have hRPositive := hSuffix.2.1
        omega
      have hFirstBound : 1 < n := by omega
      have hFirstBullet :
          HasBullet (nativeE ring N e)
            (PPL.shiftRight ring e 1) := by
        change HasBullet (nativeE ring N e)
          (ring.rightNeighbor e)
        exact hNewYBullet
      have hFirstBefore : 1 < r.val :=
        hSuffix.2.2.2
          (⟨1, hFirstBound⟩ : Fin n)
          (show 1 < d.val by exact hFirstInside) hFirstBullet
      have hAway :
          ∀ j : Fin n, 1 < j.val → j.val < d.val →
            PPL.shiftRight ring e j.val ≠ e ∧
            PPL.shiftRight ring e j.val ≠
              ring.rightNeighbor e := by
        intro j hjPos hjInside
        constructor
        · intro he
          have hIndex :
              PPL.shiftRight ring e j.val =
                PPL.shiftRight ring e 0 := by
            rw [grantDrainEntranceR8eShiftZero ring e]
            exact he
          have hEq := grantDrainEntranceR8eShiftIndexInjective
            ring e j.val 0 j.isLt (by omega) hIndex
          omega
        · intro hy
          have hIndex :
              PPL.shiftRight ring e j.val =
                PPL.shiftRight ring e 1 := hy
          have hEq := grantDrainEntranceR8eShiftIndexInjective
            ring e j.val 1 j.isLt (by omega) hIndex
          omega
      have hrAway := hAway r hFirstBefore hSuffix.2.2.1
      have hkAway := hAway k (by omega) hInside
      have hOldSuffix :
          GrantDrainEntranceSignalSuffixSite ring N e d r := by
        refine ⟨hOldSector, hSuffix.2.1,
          hSuffix.2.2.1, ?_⟩
        intro j hj hOldBullet
        exact False.elim
          ((grantDrainEntranceReadyLeaderSectorBulletFree
            ring N e d hLocal hOldSector hxReady j hj) hOldBullet)
      have hOldZero :
          (N (PPL.shiftRight ring e k.val)).sg = false := by
        rw [← grantDrainEntranceNativeEFrame
          ring N e (PPL.shiftRight ring e k.val)
          hkAway.1 hkAway.2]
        exact hZero
      have hOldOne :
          (N (PPL.shiftRight ring e r.val)).sg = true := by
        rw [← grantDrainEntranceNativeEFrame
          ring N e (PPL.shiftRight ring e r.val)
          hrAway.1 hrAway.2]
        exact hOne
      exact Or.inl ⟨e, d, r, k, hOldSuffix, hSite,
        hOrder, hInside, hOldZero, hOldOne⟩
    · have hFields : ∀ j : Fin n, j.val < d.val →
          N (PPL.shiftRight ring p j.val) =
            nativeE ring N e (PPL.shiftRight ring p j.val) := by
        intro j hj
        have hAway :=
          grantDrainEntranceR8eReadySourceOtherSectorFrame
            ring (by omega : 2 ≤ n) (nativeE ring N e)
            e p d hSuffix.1 hNewELeader hNewYFollower hp j hj
        exact (grantDrainEntranceNativeEFrame
          ring N e (PPL.shiftRight ring p j.val)
          hAway.1 hAway.2).symm
      exact Or.inl
        (grantDrainEntranceR8eCountedBackwardOnFramedSector
          ring N (nativeE ring N e) p d r k v hSuffix
          hSite hOrder hInside hZero hOne hOldSector hFields)
  · obtain ⟨p, d, hSector, hGap, hSite,
        hNoBullet, hSignal, hZero⟩ := hReady
    have hOldSector : sectorLength ring N p d :=
      (hSectorEq p d).mp hSector
    have hpNe : p ≠ e := by
      intro hp
      have hSourceSignal := hSignal
      rw [hp, hNewEZero] at hSourceSignal
      cases hSourceSignal
    have hFields : ∀ j : Fin n, j.val < d.val →
        N (PPL.shiftRight ring p j.val) =
          nativeE ring N e (PPL.shiftRight ring p j.val) := by
      intro j hj
      have hAway :=
        grantDrainEntranceR8eReadySourceOtherSectorFrame
          ring (by omega : 2 ≤ n) (nativeE ring N e)
          e p d hSector hNewELeader hNewYFollower hpNe j hj
      exact (grantDrainEntranceNativeEFrame
        ring N e (PPL.shiftRight ring p j.val)
        hAway.1 hAway.2).symm
    exact Or.inr
      (grantDrainEntranceR8eReadyBackwardOnFramedSector
        ring N (nativeE ring N e) p d v
        hSector hGap hSite hNoBullet hSignal hZero
        hOldSector hFields)

end L3.GrantDrainEntrance

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- EXACT REMAINING ROW INTERFACE, UNPROVED. Each field is the
literal pointwise theorem for an unhandled E or canonical-birth
row; no field is populated by this declaration. They are not
axioms. The birth clauses go from birth(E) back to E, allowing
the proved six-way E assembler to compose them into birth(E)
back to OLD N. The unguarded births are intentional. -/
structure GrantDrainEntranceR8ePendingRows
    {n : Nat} (ring : DirectedRing n) : Prop where
  readyLeader :
    ∀ (N : Fin n → CertNative) (e v : Fin n),
      I ring N →
      (N (ring.rightNeighbor e)).l = true →
      (N (ring.rightNeighbor e)).sg = true →
      (nativeE ring N e (ring.rightNeighbor e)).l = true →
      GrantDrainEntranceSignalDefect ring (nativeE ring N e) v →
      GrantDrainEntranceSignalDefect ring N v
  quietLeader :
    ∀ (N : Fin n → CertNative) (e v : Fin n),
      I ring N →
      (N (ring.rightNeighbor e)).l = true →
      (N (ring.rightNeighbor e)).sg = false →
      (nativeE ring N e (ring.rightNeighbor e)).l = true →
      GrantDrainEntranceSignalDefect ring (nativeE ring N e) v →
      GrantDrainEntranceSignalDefect ring N v
  leaderDeath :
    ∀ (N : Fin n → CertNative) (e v : Fin n),
      I ring N →
      (N (ring.rightNeighbor e)).l = true →
      (nativeE ring N e (ring.rightNeighbor e)).l = false →
      GrantDrainEntranceSignalDefect ring (nativeE ring N e) v →
      GrantDrainEntranceSignalDefect ring N v
  sourceBirth :
    ∀ (N : Fin n → CertNative) (e v : Fin n),
      I ring N →
      GrantDrainEntranceSignalDefect ring
        (canonicalBirth (nativeE ring N e) e) v →
      GrantDrainEntranceSignalDefect ring (nativeE ring N e) v
  responderBirth :
    ∀ (N : Fin n → CertNative) (e v : Fin n),
      I ring N →
      GrantDrainEntranceSignalDefect ring
        (canonicalBirth (nativeE ring N e)
          (ring.rightNeighbor e)) v →
      GrantDrainEntranceSignalDefect ring (nativeE ring N e) v

/-- The six E cases are now a COMPLETE logical disjunction:
three completed row proofs and the three explicitly OPEN
surviving-leader/death propositions above. It remains conditional
because the PendingRows structure has not been constructed. -/
theorem grantDrainEntranceR8eNativeBackwardOfPendingRows
    {n : Nat} (ring : DirectedRing n) (hn : 3 ≤ n)
    (hRows : GrantDrainEntranceR8ePendingRows ring)
    (N : Fin n → CertNative) (e v : Fin n)
    (hI : I ring N)
    (hDef : GrantDrainEntranceSignalDefect
      ring (nativeE ring N e) v) :
    GrantDrainEntranceSignalDefect ring N v := by
  by_cases hyLeader :
      (N (ring.rightNeighbor e)).l = true
  · by_cases hSurvive :
        (nativeE ring N e (ring.rightNeighbor e)).l = true
    · by_cases hyReady :
          (N (ring.rightNeighbor e)).sg = true
      · exact hRows.readyLeader N e v hI
          hyLeader hyReady hSurvive hDef
      · have hyQuiet :
            (N (ring.rightNeighbor e)).sg = false := by
          cases hs : (N (ring.rightNeighbor e)).sg with
          | false => rfl
          | true => exact False.elim (hyReady hs)
        exact hRows.quietLeader N e v hI
          hyLeader hyQuiet hSurvive hDef
    · have hDeath :
          (nativeE ring N e (ring.rightNeighbor e)).l =
            false := by
        cases hl :
            (nativeE ring N e (ring.rightNeighbor e)).l with
        | false => rfl
        | true => exact False.elim (hSurvive hl)
      exact hRows.leaderDeath N e v hI
        hyLeader hDeath hDef
  · have hyFollower :
        (N (ring.rightNeighbor e)).l = false := by
      cases hl : (N (ring.rightNeighbor e)).l with
      | false => rfl
      | true => exact False.elim (hyLeader hl)
    by_cases hxEmpty : (N e).b = (0 : Fin 3)
    · by_cases hxLeader : (N e).l = true
      · by_cases hxReady : (N e).sg = true
        · exact grantDrainEntranceR8eBackwardRowReadySource
            ring hn N e v hI hxLeader hxReady hyFollower hDef
        · have hxQuiet : (N e).sg = false := by
            cases hs : (N e).sg with
            | false => rfl
            | true => exact False.elim (hxReady hs)
          exact grantDrainEntranceR8eBackwardRowQuietEmpty
            ring (by omega : 2 ≤ n) N e v
            (Or.inr hxQuiet) hxEmpty hyFollower hDef
      · have hxFollower : (N e).l = false := by
          cases hl : (N e).l with
          | false => rfl
          | true => exact False.elim (hxLeader hl)
        exact grantDrainEntranceR8eBackwardRowQuietEmpty
          ring (by omega : 2 ≤ n) N e v
          (Or.inl hxFollower) hxEmpty hyFollower hDef
    · have hxBullet : HasBullet N e := hxEmpty
      exact grantDrainEntranceR8eBackwardRowMovingBullet
        ring (by omega : 2 ≤ n) N e v hI
        hyFollower hxBullet hDef

/-- The exact THREE-OUTCOME backward producer follows as soon
as the five open row fields are established. The E part is
already reduced to six source/responder cases with no additional
hidden hypotheses. -/
theorem grantDrainEntranceR8eDefectBackwardOfPendingRows
    {n : Nat} (ring : DirectedRing n) (hn : 3 ≤ n)
    (hRows : GrantDrainEntranceR8ePendingRows ring) :
    ∀ (N : Fin n → CertNative) (e : Fin n),
      I ring N →
      ∀ v : Fin n,
        (GrantDrainEntranceSignalDefect
          ring (nativeE ring N e) v →
          GrantDrainEntranceSignalDefect ring N v) ∧
        (GrantDrainEntranceSignalDefect
          ring (canonicalBirth (nativeE ring N e) e) v →
          GrantDrainEntranceSignalDefect ring N v) ∧
        (GrantDrainEntranceSignalDefect
          ring (canonicalBirth (nativeE ring N e)
            (ring.rightNeighbor e)) v →
          GrantDrainEntranceSignalDefect ring N v) := by
  intro N e hI v
  have hE :
      GrantDrainEntranceSignalDefect
        ring (nativeE ring N e) v →
      GrantDrainEntranceSignalDefect ring N v :=
    grantDrainEntranceR8eNativeBackwardOfPendingRows
      ring hn hRows N e v hI
  exact ⟨hE,
    (fun hBirth => hE (hRows.sourceBirth N e v hI hBirth)),
    (fun hBirth => hE (hRows.responderBirth N e v hI hBirth))⟩

/-- CONDITIONAL endpoint: the already potential/loss
theorem consumes precisely the assembled three-outcome producer.
Without a proof of PendingRows this does not establish either
unconditional physical R8e headline. -/
theorem grantDrainEntranceR8ePotentialClaimsOfPendingRows
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 3 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (hRows : GrantDrainEntranceR8ePendingRows ring) :
    GrantDrainEntranceR8ePotentialNonincrease ring fresh update ∧
    GrantDrainEntranceR8ePotentialNominatedDrop ring fresh update := by
  exact grantDrainEntranceR8ePotentialClaimsOfBackward
    ring fresh update
    (grantDrainEntranceR8eDefectBackwardOfPendingRows
      ring hn hRows)

end L3.GrantDrainEntrance

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-- COMPLETE birth subrow: source-side canonical birth overwrites
an old leader. This is independent of old I and requires only
the E backward implication for the selected site. -/
theorem grantDrainEntranceR8eBackwardRowSourceLeaderBirthOfE
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (e v : Fin n)
    (hxLeader : (N e).l = true)
    (hNativeBackward :
      GrantDrainEntranceSignalDefect ring (nativeE ring N e) v →
      GrantDrainEntranceSignalDefect ring N v)
    (hDef :
      GrantDrainEntranceSignalDefect ring
        (canonicalBirth (nativeE ring N e) e) v) :
    GrantDrainEntranceSignalDefect ring N v := by
  have hNewLeader :
      (nativeE ring N e e).l = true := by
    simpa [nativeE] using
      (grantDrainEntranceLiteralESourceLeaderFixed
        (N e) (N (ring.rightNeighbor e))).trans hxLeader
  exact hNativeBackward
    (grantDrainEntranceR8eBackwardRowBirthOldLeader
      ring (nativeE ring N e) e v hNewLeader hDef)

/-- COMPLETE birth subrow: responder-side canonical birth
overwrites a leader that survived E. This includes both
ready and quiet surviving-responder rows. -/
theorem grantDrainEntranceR8eBackwardRowResponderLeaderBirthOfE
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (e v : Fin n)
    (hySurvive :
      (nativeE ring N e (ring.rightNeighbor e)).l = true)
    (hNativeBackward :
      GrantDrainEntranceSignalDefect ring (nativeE ring N e) v →
      GrantDrainEntranceSignalDefect ring N v)
    (hDef :
      GrantDrainEntranceSignalDefect ring
        (canonicalBirth (nativeE ring N e)
          (ring.rightNeighbor e)) v) :
    GrantDrainEntranceSignalDefect ring N v := by
  exact hNativeBackward
    (grantDrainEntranceR8eBackwardRowBirthOldLeader
      ring (nativeE ring N e) (ring.rightNeighbor e)
      v hySurvive hDef)

/-- STRICTLY SMALLER REMAINING ROW INTERFACE. After the
completed old-leader-birth lemmas, source/responder birth
transport needs proof only when the chosen post-E position
is a follower. The three surviving/death native rows remain
as before. No field is asserted by this structure. -/
structure GrantDrainEntranceR8eFollowerPendingRows
    {n : Nat} (ring : DirectedRing n) : Prop where
  readyLeader :
    ∀ (N : Fin n → CertNative) (e v : Fin n),
      I ring N →
      (N (ring.rightNeighbor e)).l = true →
      (N (ring.rightNeighbor e)).sg = true →
      (nativeE ring N e (ring.rightNeighbor e)).l = true →
      GrantDrainEntranceSignalDefect ring (nativeE ring N e) v →
      GrantDrainEntranceSignalDefect ring N v
  quietLeader :
    ∀ (N : Fin n → CertNative) (e v : Fin n),
      I ring N →
      (N (ring.rightNeighbor e)).l = true →
      (N (ring.rightNeighbor e)).sg = false →
      (nativeE ring N e (ring.rightNeighbor e)).l = true →
      GrantDrainEntranceSignalDefect ring (nativeE ring N e) v →
      GrantDrainEntranceSignalDefect ring N v
  leaderDeath :
    ∀ (N : Fin n → CertNative) (e v : Fin n),
      I ring N →
      (N (ring.rightNeighbor e)).l = true →
      (nativeE ring N e (ring.rightNeighbor e)).l = false →
      GrantDrainEntranceSignalDefect ring (nativeE ring N e) v →
      GrantDrainEntranceSignalDefect ring N v
  sourceFollowerBirth :
    ∀ (N : Fin n → CertNative) (e v : Fin n),
      I ring N →
      (nativeE ring N e e).l = false →
      GrantDrainEntranceSignalDefect ring
        (canonicalBirth (nativeE ring N e) e) v →
      GrantDrainEntranceSignalDefect ring (nativeE ring N e) v
  responderFollowerBirth :
    ∀ (N : Fin n → CertNative) (e v : Fin n),
      I ring N →
      (nativeE ring N e (ring.rightNeighbor e)).l = false →
      GrantDrainEntranceSignalDefect ring
        (canonicalBirth (nativeE ring N e)
          (ring.rightNeighbor e)) v →
      GrantDrainEntranceSignalDefect ring (nativeE ring N e) v

/-- Every arbitrary birth outcome is now discharged by a
proven old-leader-birth row OR by its exact remaining follower
birth case. Thus the preceding five-field pending contract is
logically weaker than the narrowed one. -/
theorem grantDrainEntranceR8ePendingRowsOfFollowerRows
    {n : Nat} (ring : DirectedRing n)
    (hRows : GrantDrainEntranceR8eFollowerPendingRows ring) :
    GrantDrainEntranceR8ePendingRows ring := by
  refine
    { readyLeader := hRows.readyLeader
      quietLeader := hRows.quietLeader
      leaderDeath := hRows.leaderDeath
      sourceBirth := ?_
      responderBirth := ?_ }
  · intro N e v hI hDef
    by_cases hxLeader : (nativeE ring N e e).l = true
    · exact grantDrainEntranceR8eBackwardRowBirthOldLeader
        ring (nativeE ring N e) e v hxLeader hDef
    · have hxFollower :
          (nativeE ring N e e).l = false := by
        cases hl : (nativeE ring N e e).l with
        | false => rfl
        | true => exact False.elim (hxLeader hl)
      exact hRows.sourceFollowerBirth N e v hI hxFollower hDef
  · intro N e v hI hDef
    by_cases hyLeader :
        (nativeE ring N e (ring.rightNeighbor e)).l = true
    · exact grantDrainEntranceR8eBackwardRowBirthOldLeader
        ring (nativeE ring N e) (ring.rightNeighbor e)
        v hyLeader hDef
    · have hyFollower :
          (nativeE ring N e (ring.rightNeighbor e)).l = false := by
        cases hl : (nativeE ring N e (ring.rightNeighbor e)).l with
        | false => rfl
        | true => exact False.elim (hyLeader hl)
      exact hRows.responderFollowerBirth
        N e v hI hyFollower hDef

theorem grantDrainEntranceR8eDefectBackwardOfFollowerPendingRows
    {n : Nat} (ring : DirectedRing n) (hn : 3 ≤ n)
    (hRows : GrantDrainEntranceR8eFollowerPendingRows ring) :
    ∀ (N : Fin n → CertNative) (e : Fin n),
      I ring N →
      ∀ v : Fin n,
        (GrantDrainEntranceSignalDefect
          ring (nativeE ring N e) v →
          GrantDrainEntranceSignalDefect ring N v) ∧
        (GrantDrainEntranceSignalDefect
          ring (canonicalBirth (nativeE ring N e) e) v →
          GrantDrainEntranceSignalDefect ring N v) ∧
        (GrantDrainEntranceSignalDefect
          ring (canonicalBirth (nativeE ring N e)
            (ring.rightNeighbor e)) v →
          GrantDrainEntranceSignalDefect ring N v) := by
  exact grantDrainEntranceR8eDefectBackwardOfPendingRows
    ring hn (grantDrainEntranceR8ePendingRowsOfFollowerRows
      ring hRows)

/-- Final exact conditional physical consequence. These
are NOT unconditional Proved theorems: the five named row
fields still have to be discharged. -/
theorem grantDrainEntranceR8ePotentialClaimsOfFollowerPendingRows
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 3 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (hRows : GrantDrainEntranceR8eFollowerPendingRows ring) :
    GrantDrainEntranceR8ePotentialNonincrease ring fresh update ∧
    GrantDrainEntranceR8ePotentialNominatedDrop ring fresh update := by
  exact grantDrainEntranceR8ePotentialClaimsOfBackward
    ring fresh update
    (grantDrainEntranceR8eDefectBackwardOfFollowerPendingRows
      ring hn hRows)

end L3.GrantDrainEntrance

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-- If y is a leader, its predecessor e can only occur as the
last site of a sector: any nonterminal successor of e would
otherwise be an internal leader. This is a precise offset
statement, even on the one-root wraparound sector. -/
theorem grantDrainEntranceR8eSourceLastBeforeLeader
    {n : Nat} (ring : DirectedRing n)
    (M : Fin n → CertNative)
    (e p : Fin n) (d : Fin (n + 1))
    (hSector : sectorLength ring M p d)
    (hyLeader : (M (ring.rightNeighbor e)).l = true)
    (j : Fin n)
    (hjInside : j.val < d.val)
    (hAt : PPL.shiftRight ring p j.val = e) :
    j.val + 1 = d.val := by
  have hNext :
      PPL.shiftRight ring p (j.val + 1) =
        ring.rightNeighbor e := by
    calc
      PPL.shiftRight ring p (j.val + 1) =
          ring.rightNeighbor
            (PPL.shiftRight ring p j.val) :=
        (grantDrainEntranceAheadShiftSucc ring p j.val).symm
      _ = ring.rightNeighbor e := by rw [hAt]
  by_cases hLt : j.val + 1 < d.val
  · have hBound : j.val + 1 < n := by omega
    have hFollower := hSector.2.2.2
      (⟨j.val + 1, hBound⟩ : Fin n)
      (show 0 < j.val + 1 by omega) hLt
    rw [hNext, hyLeader] at hFollower
    cases hFollower
  · omega

/-- Generic complete defect backward lemma for the *one-site
activation* geometry. The entire leader and bullet arrays are
unchanged; the source e becomes signal one; all other signals
are identical. Because right(e) is already a leader, e has no
later follower in its sector. This single monotone change cannot
create either kind of signal defect. -/
theorem grantDrainEntranceR8eBackwardOnLastSignalActivation
    {n : Nat} (ring : DirectedRing n)
    (N M : Fin n → CertNative)
    (e v : Fin n)
    (hLeaders : ∀ i : Fin n, (M i).l = (N i).l)
    (hBullets : ∀ i : Fin n, (M i).b = (N i).b)
    (hSourceOne : (M e).sg = true)
    (hSignalsAway : ∀ i : Fin n, i ≠ e →
      (M i).sg = (N i).sg)
    (hyLeader : (M (ring.rightNeighbor e)).l = true)
    (hDef : GrantDrainEntranceSignalDefect ring M v) :
    GrantDrainEntranceSignalDefect ring N v := by
  have hSectors :
      ∀ (p : Fin n) (d : Fin (n + 1)),
        sectorLength ring M p d ↔ sectorLength ring N p d := by
    intro p d
    exact grantDrainEntranceR8eSectorLengthOfLeaderArray
      ring N M hLeaders p d
  rcases hDef with hCount | hReady
  · obtain ⟨p, d, r, k, hSuffix, hSite,
        hOrder, hInside, hZero, hOne⟩ := hCount
    have hOldSector : sectorLength ring N p d :=
      (hSectors p d).mp hSuffix.1
    have hOldSuffix :
        GrantDrainEntranceSignalSuffixSite ring N p d r := by
      refine ⟨hOldSector, hSuffix.2.1, hSuffix.2.2.1, ?_⟩
      intro j hj hOldBullet
      have hNewBullet :
          HasBullet M (PPL.shiftRight ring p j.val) := by
        change (M (PPL.shiftRight ring p j.val)).b ≠
          (0 : Fin 3)
        rw [hBullets (PPL.shiftRight ring p j.val)]
        exact hOldBullet
      exact hSuffix.2.2.2 j hj hNewBullet
    have hkNe : PPL.shiftRight ring p k.val ≠ e := by
      intro he
      have hBad := hZero
      rw [he, hSourceOne] at hBad
      cases hBad
    have hrNe : PPL.shiftRight ring p r.val ≠ e := by
      intro he
      have hLast :=
        grantDrainEntranceR8eSourceLastBeforeLeader
          ring M e p d hSuffix.1 hyLeader r
          hSuffix.2.2.1 he
      omega
    have hOldZero :
        (N (PPL.shiftRight ring p k.val)).sg = false := by
      rw [← hSignalsAway
        (PPL.shiftRight ring p k.val) hkNe]
      exact hZero
    have hOldOne :
        (N (PPL.shiftRight ring p r.val)).sg = true := by
      rw [← hSignalsAway
        (PPL.shiftRight ring p r.val) hrNe]
      exact hOne
    exact Or.inl ⟨p, d, r, k, hOldSuffix,
      hSite, hOrder, hInside, hOldZero, hOldOne⟩
  · obtain ⟨p, d, hSector, hGap, hSite,
        hNoBullet, hReady, hZero⟩ := hReady
    have hpNe : p ≠ e := by
      intro hp
      have hAt : PPL.shiftRight ring p 0 = e := by
        rw [grantDrainEntranceR8eShiftZero ring p]
        exact hp
      have hZeroBound : 0 < n := ring.hn
      have hZeroInside :
          (⟨0, hZeroBound⟩ : Fin n).val < d.val := by
        change 0 < d.val
        omega
      have hLast :=
        grantDrainEntranceR8eSourceLastBeforeLeader
          ring M e p d hSector hyLeader
          (⟨0, hZeroBound⟩ : Fin n) hZeroInside hAt
      have hLastNat : 0 + 1 = d.val := by
        simpa only [Fin.val_mk] using hLast
      omega
    have hvNe : v ≠ e := by
      intro he
      have hBad := hZero
      rw [he, hSourceOne] at hBad
      cases hBad
    have hOldSector : sectorLength ring N p d :=
      (hSectors p d).mp hSector
    have hOldNoBullet : ∀ j : Fin n, j.val < d.val →
        ¬ HasBullet N (PPL.shiftRight ring p j.val) := by
      intro j hj hb
      apply hNoBullet j hj
      change (M (PPL.shiftRight ring p j.val)).b ≠
        (0 : Fin 3)
      rw [hBullets (PPL.shiftRight ring p j.val)]
      exact hb
    have hOldReady : (N p).sg = true := by
      rw [← hSignalsAway p hpNe]
      exact hReady
    have hOldZero : (N v).sg = false := by
      rw [← hSignalsAway v hvNe]
      exact hZero
    exact Or.inr ⟨p, d, hOldSector, hGap, hSite,
      hOldNoBullet, hOldReady, hOldZero⟩

/-- Quiet old responder leader, empty and quiet source: the
literal E pair leaves leader and bullet fields unchanged,
makes e signal one, and keeps all other signal bits unchanged.
No I assumption is necessary for this row. -/
theorem grantDrainEntranceR8eQuietLeaderEmptyPair
    (x y : CertNative)
    (hxEmpty : x.b = (0 : Fin 3))
    (hxQuiet : x.sg = false)
    (hyLeader : y.l = true)
    (hyQuiet : y.sg = false) :
    (certLiteralEPair x y).1.l = x.l ∧
    (certLiteralEPair x y).1.b = x.b ∧
    (certLiteralEPair x y).1.sg = true ∧
    (certLiteralEPair x y).2.l = y.l ∧
    (certLiteralEPair x y).2.b = y.b ∧
    (certLiteralEPair x y).2.sg = y.sg := by
  simp [certLiteralEPair, certFinThree,
    hxEmpty, hxQuiet, hyLeader, hyQuiet]

/-- COMPLETE QUIET-SURVIVING-LEADER E SUBROW with empty,
quiet source. This strictly extends the fixed-point subrow:
the old source signal zero is activated by the old y leader. -/
theorem grantDrainEntranceR8eBackwardRowQuietLeaderEmptySource
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (N : Fin n → CertNative) (e v : Fin n)
    (hxEmpty : (N e).b = (0 : Fin 3))
    (hxQuiet : (N e).sg = false)
    (hyLeader : (N (ring.rightNeighbor e)).l = true)
    (hyQuiet : (N (ring.rightNeighbor e)).sg = false)
    (hDef : GrantDrainEntranceSignalDefect
      ring (nativeE ring N e) v) :
    GrantDrainEntranceSignalDefect ring N v := by
  have hPair := grantDrainEntranceR8eQuietLeaderEmptyPair
    (N e) (N (ring.rightNeighbor e))
    hxEmpty hxQuiet hyLeader hyQuiet
  have hDistinct :=
    grantDrainEntranceRightNeighborDistinct ring hn e
  have hSourceLeader :
      (nativeE ring N e e).l = (N e).l := by
    simpa [nativeE] using hPair.1
  have hSourceBullet :
      (nativeE ring N e e).b = (N e).b := by
    simpa [nativeE] using hPair.2.1
  have hSourceSignal :
      (nativeE ring N e e).sg = true := by
    simpa [nativeE] using hPair.2.2.1
  have hTargetLeader :
      (nativeE ring N e (ring.rightNeighbor e)).l =
        (N (ring.rightNeighbor e)).l := by
    simpa [nativeE, hDistinct] using hPair.2.2.2.1
  have hTargetBullet :
      (nativeE ring N e (ring.rightNeighbor e)).b =
        (N (ring.rightNeighbor e)).b := by
    simpa [nativeE, hDistinct] using hPair.2.2.2.2.1
  have hTargetSignal :
      (nativeE ring N e (ring.rightNeighbor e)).sg =
        (N (ring.rightNeighbor e)).sg := by
    simpa [nativeE, hDistinct] using hPair.2.2.2.2.2
  have hLeaders :
      ∀ i : Fin n,
        (nativeE ring N e i).l = (N i).l := by
    intro i
    by_cases hi : i = e
    · subst i
      exact hSourceLeader
    · by_cases hj : i = ring.rightNeighbor e
      · subst i
        exact hTargetLeader
      · rw [grantDrainEntranceNativeEFrame ring N e i hi hj]
  have hBullets :
      ∀ i : Fin n,
        (nativeE ring N e i).b = (N i).b := by
    intro i
    by_cases hi : i = e
    · subst i
      exact hSourceBullet
    · by_cases hj : i = ring.rightNeighbor e
      · subst i
        exact hTargetBullet
      · rw [grantDrainEntranceNativeEFrame ring N e i hi hj]
  have hSignalAway :
      ∀ i : Fin n, i ≠ e →
        (nativeE ring N e i).sg = (N i).sg := by
    intro i hi
    by_cases hj : i = ring.rightNeighbor e
    · subst i
      exact hTargetSignal
    · rw [grantDrainEntranceNativeEFrame ring N e i hi hj]
  exact grantDrainEntranceR8eBackwardOnLastSignalActivation
    ring N (nativeE ring N e) e v
    hLeaders hBullets hSourceSignal hSignalAway
    (hTargetLeader.trans hyLeader) hDef

end L3.GrantDrainEntrance

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-- The literal E initiator sees signal one whenever the final
responder remains a leader, irrespective of bullet-kind and
shield cases. This is a finite pure native-row equality. -/
theorem grantDrainEntranceR8eSurvivingResponderSourceOne
    (x y : CertNative)
    (hSurvive : (certLiteralEPair x y).2.l = true) :
    (certLiteralEPair x y).1.sg = true := by
  rcases x with ⟨xl, xb, xsh, xsg⟩
  rcases y with ⟨yl, yb, ysh, ysg⟩
  rcases grantDrainEntranceLocalFinThreeCases xb with
    hxb | hxb | hxb <;>
  rcases grantDrainEntranceLocalFinThreeCases yb with
    hyb | hyb | hyb <;>
  subst xb <;> subst yb <;>
  cases xl <;> cases yl <;> cases xsh <;>
  cases ysh <;> cases xsg <;> cases ysg <;>
  simp [certLiteralEPair, certFinThree] at *

/-- The quiet-responder E row is fully backward-closed for
an OLD empty source, including an old READY source. Only
the post-E leader survival guard is needed in that case.
The source has b=0 before and after, so leader/bullet arrays
are unchanged; its signal can only be activated to 1. -/
theorem grantDrainEntranceR8eBackwardRowQuietLeaderEmpty
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (N : Fin n → CertNative) (e v : Fin n)
    (hxEmpty : (N e).b = (0 : Fin 3))
    (hyLeader : (N (ring.rightNeighbor e)).l = true)
    (hyQuiet : (N (ring.rightNeighbor e)).sg = false)
    (hSurvive :
      (nativeE ring N e (ring.rightNeighbor e)).l = true)
    (hDef : GrantDrainEntranceSignalDefect
      ring (nativeE ring N e) v) :
    GrantDrainEntranceSignalDefect ring N v := by
  have hDistinct :=
    grantDrainEntranceRightNeighborDistinct ring hn e
  have hSourceLeader :
      (nativeE ring N e e).l = (N e).l := by
    simpa [nativeE] using
      grantDrainEntranceLiteralESourceLeaderFixed
        (N e) (N (ring.rightNeighbor e))
  have hSourceBullet :
      (nativeE ring N e e).b = (N e).b := by
    rw [grantDrainEntranceNativeESourceBulletZero ring N e]
    exact hxEmpty.symm
  have hSourceOne :
      (nativeE ring N e e).sg = true := by
    have hPairSurvive :
        (certLiteralEPair (N e)
          (N (ring.rightNeighbor e))).2.l = true := by
      simpa [nativeE, hDistinct] using hSurvive
    simpa [nativeE] using
      grantDrainEntranceR8eSurvivingResponderSourceOne
        (N e) (N (ring.rightNeighbor e)) hPairSurvive
  have hTargetBullet :
      (nativeE ring N e (ring.rightNeighbor e)).b =
        (N (ring.rightNeighbor e)).b :=
    grantDrainEntranceNativeEQuietVictimBulletRetained
      ring hn N e hyLeader hyQuiet
  have hTargetSignal :
      (nativeE ring N e (ring.rightNeighbor e)).sg =
        (N (ring.rightNeighbor e)).sg := by
    rw [(grantDrainEntranceNativeELeaderBulletAfter
      ring hn N e hyLeader).2, hyQuiet]
  have hLeaders :=
    grantDrainEntranceNativeELeadersFixed
      ring hn N e (hSurvive.trans hyLeader.symm)
  have hBullets :
      ∀ i : Fin n,
        (nativeE ring N e i).b = (N i).b := by
    intro i
    by_cases he : i = e
    · subst i
      exact hSourceBullet
    · by_cases hy : i = ring.rightNeighbor e
      · subst i
        exact hTargetBullet
      · rw [grantDrainEntranceNativeEFrame ring N e i he hy]
  have hSignalAway :
      ∀ i : Fin n, i ≠ e →
        (nativeE ring N e i).sg = (N i).sg := by
    intro i he
    by_cases hy : i = ring.rightNeighbor e
    · subst i
      exact hTargetSignal
    · rw [grantDrainEntranceNativeEFrame ring N e i he hy]
  exact grantDrainEntranceR8eBackwardOnLastSignalActivation
    ring N (nativeE ring N e) e v
    hLeaders hBullets hSourceOne hSignalAway
    hSurvive hDef

end L3.GrantDrainEntrance

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-- A NEW leader z can occur at offset zero of its sector, but
never at a positive interior offset; if it is not the root,
it is absent from the whole half-open sector. -/
theorem grantDrainEntranceR8eOtherLeaderAbsentFromSector
    {n : Nat} (ring : DirectedRing n)
    (M : Fin n → CertNative)
    (p z : Fin n) (d : Fin (n + 1))
    (hSector : sectorLength ring M p d)
    (hzLeader : (M z).l = true)
    (hpNe : p ≠ z) :
    ∀ j : Fin n, j.val < d.val →
      PPL.shiftRight ring p j.val ≠ z := by
  intro j hj hAt
  by_cases hjZero : j.val = 0
  · have hRoot := hAt
    rw [hjZero, grantDrainEntranceR8eShiftZero ring p] at hRoot
    exact hpNe hRoot
  · have hFollower := hSector.2.2.2 j (by omega) hj
    rw [hAt, hzLeader] at hFollower
    cases hFollower

/-- COMPLETE READY-SURVIVING-RESPONDER E SUBROW with old empty
source. E inserts a DUMMY at the ready responder leader y and
clears its root signal. The OLD y sector was bullet-free by I,
and the inserted root bullet cannot create an inversion.
The source's newly copied one is at the last follower of the
preceding sector. Both defect kinds transport pointwise. -/
theorem grantDrainEntranceR8eBackwardRowReadyLeaderEmptySource
    {n : Nat} (ring : DirectedRing n) (hn : 3 ≤ n)
    (N : Fin n → CertNative) (e v : Fin n)
    (hI : I ring N)
    (hxEmpty : (N e).b = (0 : Fin 3))
    (hyLeader : (N (ring.rightNeighbor e)).l = true)
    (hyReady : (N (ring.rightNeighbor e)).sg = true)
    (hSurvive :
      (nativeE ring N e (ring.rightNeighbor e)).l = true)
    (hDef : GrantDrainEntranceSignalDefect
      ring (nativeE ring N e) v) :
    GrantDrainEntranceSignalDefect ring N v := by
  have hLocal : GrantDrainEntranceILocal ring N :=
    (grantDrainEntranceIffILocal ring N).mp hI
  have hDistinct :=
    grantDrainEntranceRightNeighborDistinct
      ring (by omega : 2 ≤ n) e
  have hNewEOne :
      (nativeE ring N e e).sg = true := by
    have hPairSurvive :
        (certLiteralEPair (N e)
          (N (ring.rightNeighbor e))).2.l = true := by
      simpa [nativeE, hDistinct] using hSurvive
    simpa [nativeE] using
      grantDrainEntranceR8eSurvivingResponderSourceOne
        (N e) (N (ring.rightNeighbor e)) hPairSurvive
  have hNewYZero :
      (nativeE ring N e (ring.rightNeighbor e)).sg = false :=
    (grantDrainEntranceNativeELeaderBulletAfter
      ring (by omega : 2 ≤ n) N e hyLeader).2
  have hNewYBullet :
      (nativeE ring N e (ring.rightNeighbor e)).b =
        (1 : Fin 3) :=
    grantDrainEntranceNativeEReadyVictimBulletDummy
      ring (by omega : 2 ≤ n) N e hyLeader hyReady
  have hNewEEmpty :
      (nativeE ring N e e).b = (0 : Fin 3) :=
    grantDrainEntranceNativeESourceBulletZero ring N e
  have hSectors :
      ∀ (p : Fin n) (d : Fin (n + 1)),
        sectorLength ring (nativeE ring N e) p d ↔
          sectorLength ring N p d := by
    intro p d
    exact grantDrainEntranceR8eSectorRowLeaderSurvives
      ring (by omega : 2 ≤ n) N e
      hyLeader hSurvive p d
  have hSignalsAway :
      ∀ i : Fin n, i ≠ e →
        i ≠ ring.rightNeighbor e →
        (nativeE ring N e i).sg = (N i).sg := by
    intro i he hy
    rw [grantDrainEntranceNativeEFrame ring N e i he hy]
  have hNewYLeader : (nativeE ring N e
      (ring.rightNeighbor e)).l = true := hSurvive
  have hOldEEmpty : ¬ HasBullet N e := by
    intro hb
    exact hb hxEmpty
  rcases hDef with hCount | hReady
  · obtain ⟨p, d, r, k, hSuffix, hSite,
        hOrder, hInside, hZero, hOne⟩ := hCount
    have hOldSector : sectorLength ring N p d :=
      (hSectors p d).mp hSuffix.1
    have hrNeE :
        PPL.shiftRight ring p r.val ≠ e := by
      intro hr
      have hLast := grantDrainEntranceR8eSourceLastBeforeLeader
        ring (nativeE ring N e) e p d hSuffix.1
        hNewYLeader r hSuffix.2.2.1 hr
      omega
    have hkNeE :
        PPL.shiftRight ring p k.val ≠ e := by
      intro hk
      have hFalse := hZero
      rw [hk, hNewEOne] at hFalse
      cases hFalse
    have hrNeY :
        PPL.shiftRight ring p r.val ≠ ring.rightNeighbor e := by
      intro hr
      have hrPositive : 0 < r.val := by
        have hrLower := hSuffix.2.1
        omega
      have hFalse := hSuffix.1.2.2.2 r
        hrPositive hSuffix.2.2.1
      rw [hr, hNewYLeader] at hFalse
      cases hFalse
    have hkNeY :
        PPL.shiftRight ring p k.val ≠ ring.rightNeighbor e := by
      intro hk
      have hFalse := hSuffix.1.2.2.2 k
        (show 0 < k.val by omega) hInside
      rw [hk, hNewYLeader] at hFalse
      cases hFalse
    have hOldOne :
        (N (PPL.shiftRight ring p r.val)).sg = true := by
      rw [← hSignalsAway
        (PPL.shiftRight ring p r.val) hrNeE hrNeY]
      exact hOne
    have hOldZero :
        (N (PPL.shiftRight ring p k.val)).sg = false := by
      rw [← hSignalsAway
        (PPL.shiftRight ring p k.val) hkNeE hkNeY]
      exact hZero
    have hOldSuffix :
        GrantDrainEntranceSignalSuffixSite ring N p d r := by
      refine ⟨hOldSector, hSuffix.2.1, hSuffix.2.2.1, ?_⟩
      intro j hj hOldBullet
      by_cases hpY : p = ring.rightNeighbor e
      · subst p
        exact False.elim
          ((grantDrainEntranceReadyLeaderSectorBulletFree
            ring N (ring.rightNeighbor e) d hLocal hOldSector
            hyReady j hj) hOldBullet)
      · have hNoY :=
          grantDrainEntranceR8eOtherLeaderAbsentFromSector
            ring (nativeE ring N e) p (ring.rightNeighbor e)
            d hSuffix.1 hNewYLeader hpY j hj
        by_cases hjE : PPL.shiftRight ring p j.val = e
        · have hBulletE : HasBullet N e := by
            rw [← hjE]
            exact hOldBullet
          exact False.elim (hOldEEmpty hBulletE)
        · have hNewBullet :
              HasBullet (nativeE ring N e)
                (PPL.shiftRight ring p j.val) := by
            change (nativeE ring N e
              (PPL.shiftRight ring p j.val)).b ≠ (0 : Fin 3)
            rw [grantDrainEntranceNativeEFrame ring N e
              (PPL.shiftRight ring p j.val) hjE hNoY]
            exact hOldBullet
          exact hSuffix.2.2.2 j hj hNewBullet
    exact Or.inl ⟨p, d, r, k, hOldSuffix,
      hSite, hOrder, hInside, hOldZero, hOldOne⟩
  · obtain ⟨p, d, hSector, hGap, hSite,
        hNoBullet, hNewReady, hNewZero⟩ := hReady
    have hpNeY : p ≠ ring.rightNeighbor e := by
      intro hp
      have hContradiction := hNewReady
      rw [hp, hNewYZero] at hContradiction
      cases hContradiction
    have hpNeE : p ≠ e := by
      intro hp
      have hAt : PPL.shiftRight ring p 0 = e := by
        rw [grantDrainEntranceR8eShiftZero ring p]
        exact hp
      have hZeroInside :
          (⟨0, ring.hn⟩ : Fin n).val < d.val := by
        change 0 < d.val
        omega
      have hLast := grantDrainEntranceR8eSourceLastBeforeLeader
        ring (nativeE ring N e) e p d hSector
        hNewYLeader
        (⟨0, ring.hn⟩ : Fin n) hZeroInside hAt
      have hLastNat : 0 + 1 = d.val := by
        simpa only [Fin.val_mk] using hLast
      omega
    have hvNeE : v ≠ e := by
      intro hv
      have hContradiction := hNewZero
      rw [hv, hNewEOne] at hContradiction
      cases hContradiction
    have hvNeY : v ≠ ring.rightNeighbor e := by
      intro hv
      have hRoot : v = ring.rightNeighbor p := hSite
      have hFirstShift :
          PPL.shiftRight ring p 1 = v := by
        change ring.rightNeighbor p = v
        exact hRoot.symm
      have hOneBound : 1 < n := by omega
      have hNotY :=
        grantDrainEntranceR8eOtherLeaderAbsentFromSector
          ring (nativeE ring N e) p (ring.rightNeighbor e)
          d hSector hNewYLeader hpNeY
          (⟨1, hOneBound⟩ : Fin n)
          (show 1 < d.val by omega)
      rw [hFirstShift, hv] at hNotY
      exact hNotY rfl
    have hOldSector : sectorLength ring N p d :=
      (hSectors p d).mp hSector
    have hNoY :=
      grantDrainEntranceR8eOtherLeaderAbsentFromSector
        ring (nativeE ring N e) p (ring.rightNeighbor e)
        d hSector hNewYLeader hpNeY
    have hOldNoBullet : ∀ j : Fin n, j.val < d.val →
        ¬ HasBullet N (PPL.shiftRight ring p j.val) := by
      intro j hj hb
      by_cases hjE : PPL.shiftRight ring p j.val = e
      · have hBulletE : HasBullet N e := by
          rw [← hjE]
          exact hb
        exact hOldEEmpty hBulletE
      · apply hNoBullet j hj
        change (nativeE ring N e
          (PPL.shiftRight ring p j.val)).b ≠ (0 : Fin 3)
        rw [grantDrainEntranceNativeEFrame ring N e
          (PPL.shiftRight ring p j.val) hjE (hNoY j hj)]
        exact hb
    have hOldReady : (N p).sg = true := by
      rw [← hSignalsAway p hpNeE hpNeY]
      exact hNewReady
    have hOldZero : (N v).sg = false := by
      rw [← hSignalsAway v hvNeE hvNeY]
      exact hNewZero
    exact Or.inr ⟨p, d, hOldSector, hGap, hSite,
      hOldNoBullet, hOldReady, hOldZero⟩

end L3.GrantDrainEntrance

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-- Two sectorLength certificates for the same leader have the same
strict clockwise length, including the unique-leader length n. -/
theorem grantDrainEntranceR8eSectorLengthUnique
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (p : Fin n) (d f : Fin (n + 1))
    (hd : sectorLength ring N p d)
    (hf : sectorLength ring N p f) : d = f := by
  apply Fin.ext
  by_cases hdf : d.val < f.val
  · have hBound : d.val < n := by
      have hfBound := f.isLt
      omega
    have hNotLeader := hf.2.2.2
      (⟨d.val, hBound⟩ : Fin n) hd.1 hdf
    change (N (PPL.shiftRight ring p d.val)).l = false
      at hNotLeader
    rw [hd.2.2.1] at hNotLeader
    cases hNotLeader
  · by_cases hfd : f.val < d.val
    · have hBound : f.val < n := by
        have hdBound := d.isLt
        omega
      have hNotLeader := hd.2.2.2
        (⟨f.val, hBound⟩ : Fin n) hf.1 hfd
      change (N (PPL.shiftRight ring p f.val)).l = false
        at hNotLeader
      rw [hf.2.2.1] at hNotLeader
      cases hNotLeader
    · omega

/-- Every old leader is the root of some exact sectorLength
interval, extracted from the all-site sector cover. -/
theorem grantDrainEntranceR8eSectorAtLeader
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (hRoot : ∃ q : Fin n, (N q).l = true)
    (p : Fin n) (hp : (N p).l = true) :
    ∃ d : Fin (n + 1), sectorLength ring N p d := by
  obtain ⟨q, d, a, hSector, ha, hAt⟩ :=
    grantDrainEntranceSectorCoverOfRoot ring N hRoot p
  have haZero : a.val = 0 := by
    by_cases hz : a.val = 0
    · exact hz
    · have hFollower := hSector.2.2.2 a
        (show 0 < a.val by omega) ha
      rw [← hAt, hp] at hFollower
      cases hFollower
  have hq : q = p := by
    have hShift : PPL.shiftRight ring q a.val = q := by
      rw [haZero]
      exact grantDrainEntranceR8eShiftZero ring q
    rw [hShift] at hAt
    exact hAt.symm
  refine ⟨d, ?_⟩
  rw [← hq]
  exact hSector

/-- Under literal I, an old signal one at a follower automatically
puts all bullets strictly before it: any bullet at or after it
would force its signal to be zero by I's inclusive trail clause. -/
theorem grantDrainEntranceR8eSuffixFromSignalOneI
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (hI : I ring N)
    (p : Fin n) (d : Fin (n + 1)) (r : Fin n)
    (hSector : sectorLength ring N p d)
    (hLower : 1 ≤ r.val) (hInside : r.val < d.val)
    (hOne : (N (PPL.shiftRight ring p r.val)).sg = true) :
    GrantDrainEntranceSignalSuffixSite ring N p d r := by
  refine ⟨hSector, hLower, hInside, ?_⟩
  intro j hj hBullet
  by_cases hjBefore : j.val < r.val
  · exact hjBefore
  · have hTrail := (hI.2 p d hSector).2
      j hj hBullet r (show r.val ≤ j.val by omega)
    rw [hOne] at hTrail
    cases hTrail

/-- The old I root cover places every old follower z at a positive
offset t in an old sector p,d. Birth at z then splits exactly
into lengths t and d-t, with literal PPL.shiftRight identities. -/
theorem grantDrainEntranceR8eFollowerBirthSplitFromI
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (hI : I ring N)
    (z : Fin n) (hzFollower : (N z).l = false) :
    ∃ (p : Fin n) (d : Fin (n + 1)) (t : Fin n),
      sectorLength ring N p d ∧
      0 < t.val ∧ t.val < d.val ∧
      PPL.shiftRight ring p t.val = z ∧
      sectorLength ring (canonicalBirth N z) p
        (⟨t.val, show t.val < n + 1 by omega⟩ : Fin (n + 1)) ∧
      sectorLength ring (canonicalBirth N z) z
        (⟨d.val - t.val, show d.val - t.val < n + 1 by omega⟩ : Fin (n + 1)) := by
  obtain ⟨p, d, t, hSector, htInside, hAt⟩ :=
    grantDrainEntranceSectorCoverOfRoot ring N hI.1.1 z
  have htPos : 0 < t.val := by
    by_cases htZero : t.val = 0
    · have hzAtRoot : z = p := by
        rw [htZero, grantDrainEntranceR8eShiftZero ring p] at hAt
        exact hAt
      have hzLeader : (N z).l = true := by
        rw [hzAtRoot]
        exact hSector.2.1
      rw [hzFollower] at hzLeader
      cases hzLeader
    · omega
  have hSplit := grantDrainEntranceR8eSectorRowBirthSplit
    ring N z p d t hSector htPos htInside hAt.symm
  exact ⟨p, d, t, hSector, htPos, htInside, hAt.symm,
    hSplit.1, hSplit.2⟩

/-- A canonical birth preserves each pre-existing leader bit.
The chosen position becomes a root regardless of its old value. -/
theorem grantDrainEntranceR8eBirthPreservesOldLeaders
    {n : Nat} (N : Fin n → CertNative) (z i : Fin n)
    (hOld : (N i).l = true) :
    (canonicalBirth N z i).l = true := by
  by_cases hi : i = z
  · subst i
    exact (grantDrainEntranceCanonicalBirthAtSite N z).1
  · rw [grantDrainEntranceCanonicalBirthFrame N z i hi]
    exact hOld

/-- The old next leader remains a leader after a canonical birth,
so a sector starting at an old root can only become shorter. -/
theorem grantDrainEntranceR8eBirthSectorLengthLe
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (z p : Fin n)
    (d D : Fin (n + 1))
    (hNew : sectorLength ring (canonicalBirth N z) p d)
    (hOld : sectorLength ring N p D) :
    d.val ≤ D.val := by
  by_cases hLe : d.val ≤ D.val
  · exact hLe
  · have hNewNext :
        (canonicalBirth N z
          (PPL.shiftRight ring p D.val)).l = true :=
      grantDrainEntranceR8eBirthPreservesOldLeaders
        N z (PPL.shiftRight ring p D.val) hOld.2.2.1
    have hBound : D.val < n := by
      have hdBound := d.isLt
      omega
    have hFollower := hNew.2.2.2
      (⟨D.val, hBound⟩ : Fin n)
      hOld.1 (show D.val < d.val by omega)
    change (canonicalBirth N z
      (PPL.shiftRight ring p D.val)).l = false at hFollower
    rw [hNewNext] at hFollower
    cases hFollower

/-- On I, an unconditional canonical birth cannot create a new
signal-cleanup defect at an old physical site. This covers both
kinds of defect, including a birth that erases a current bullet.
It does not require FIRE eligibility. -/
theorem grantDrainEntranceR8eBirthBackwardOfI
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (hI : I ring N)
    (z v : Fin n)
    (hDef : GrantDrainEntranceSignalDefect
      ring (canonicalBirth N z) v) :
    GrantDrainEntranceSignalDefect ring N v := by
  by_cases hzLeader : (N z).l = true
  · exact grantDrainEntranceR8eBackwardRowBirthOldLeader
      ring N z v hzLeader hDef
  · have hzFollower : (N z).l = false := by
      cases hz : (N z).l with
      | false => rfl
      | true => exact False.elim (hzLeader hz)
    rcases hDef with hCount | hReady
    · obtain ⟨p, d, r, k, hSuffix, hSite, hOrder,
          hInside, hZero, hOne⟩ := hCount
      have hrPos : 0 < r.val := by
        have hLower := hSuffix.2.1
        omega
      have hrAway :=
        grantDrainEntranceR8eBirthInteriorAvoidSite
          ring N z p d hSuffix.1 r hrPos hSuffix.2.2.1
      have hkAway :=
        grantDrainEntranceR8eBirthInteriorAvoidSite
          ring N z p d hSuffix.1 k
          (show 0 < k.val by omega) hInside
      have hOldOneAtR :
          (N (PPL.shiftRight ring p r.val)).sg = true := by
        rw [← grantDrainEntranceCanonicalBirthFrame
          N z (PPL.shiftRight ring p r.val) hrAway]
        exact hOne
      have hOldZeroAtK :
          (N (PPL.shiftRight ring p k.val)).sg = false := by
        rw [← grantDrainEntranceCanonicalBirthFrame
          N z (PPL.shiftRight ring p k.val) hkAway]
        exact hZero
      by_cases hpZ : p = z
      · subst p
        obtain ⟨q, D, t, hOldSector, htPos, htInside, hzAt,
            hBornHead, hBornTail⟩ :=
          grantDrainEntranceR8eFollowerBirthSplitFromI
            ring N hI z hzFollower
        have hLength : d.val = D.val - t.val := by
          have hUnique :=
            grantDrainEntranceR8eSectorLengthUnique
              ring (canonicalBirth N z) z d
              (⟨D.val - t.val, show D.val - t.val < n + 1 by omega⟩ : Fin (n + 1))
              hSuffix.1 hBornTail
          have hv := congrArg Fin.val hUnique
          simpa only [Fin.val_mk] using hv
        have hrOldInside : t.val + r.val < D.val := by
          have hrIn := hSuffix.2.2.1
          omega
        have hkOldInside : t.val + k.val < D.val := by
          omega
        have hrBound : t.val + r.val < n := by
          have hDBound := D.isLt
          omega
        have hkBound : t.val + k.val < n := by
          have hDBound := D.isLt
          omega
        have hShiftR :
            PPL.shiftRight ring q (t.val + r.val) =
              PPL.shiftRight ring z r.val := by
          calc
            PPL.shiftRight ring q (t.val + r.val) =
                PPL.shiftRight ring
                  (PPL.shiftRight ring q t.val) r.val :=
              (grantDrainEntranceArcShiftRightAdd
                ring q t.val r.val).symm
            _ = PPL.shiftRight ring z r.val := by rw [hzAt]
        have hShiftK :
            PPL.shiftRight ring q (t.val + k.val) =
              PPL.shiftRight ring z k.val := by
          calc
            PPL.shiftRight ring q (t.val + k.val) =
                PPL.shiftRight ring
                  (PPL.shiftRight ring q t.val) k.val :=
              (grantDrainEntranceArcShiftRightAdd
                ring q t.val k.val).symm
            _ = PPL.shiftRight ring z k.val := by rw [hzAt]
        have hOldOne :
            (N (PPL.shiftRight ring q (t.val + r.val))).sg =
              true := by
          rw [hShiftR]
          exact hOldOneAtR
        have hOldZero :
            (N (PPL.shiftRight ring q (t.val + k.val))).sg =
              false := by
          rw [hShiftK]
          exact hOldZeroAtK
        have hOldSuffix :
            GrantDrainEntranceSignalSuffixSite ring N q D
              (⟨t.val + r.val, hrBound⟩ : Fin n) := by
          apply grantDrainEntranceR8eSuffixFromSignalOneI
            ring N hI q D
            (⟨t.val + r.val, hrBound⟩ : Fin n)
            hOldSector
            (show 1 ≤ t.val + r.val by omega)
            hrOldInside
          simpa only [Fin.val_mk] using hOldOne
        refine Or.inl ⟨q, D,
          (⟨t.val + r.val, hrBound⟩ : Fin n),
          (⟨t.val + k.val, hkBound⟩ : Fin n),
          hOldSuffix, ?_, ?_, ?_, ?_, ?_⟩
        · exact hSite.trans hShiftK.symm
        · change t.val + r.val < t.val + k.val
          omega
        · change t.val + k.val < D.val
          exact hkOldInside
        · simpa only [Fin.val_mk] using hOldZero
        · simpa only [Fin.val_mk] using hOldOne
      · have hNewRoot : (canonicalBirth N z p).l = true :=
          hSuffix.1.2.1
        have hOldRoot : (N p).l = true := by
          rw [grantDrainEntranceCanonicalBirthFrame N z p hpZ]
            at hNewRoot
          exact hNewRoot
        obtain ⟨D, hOldSector⟩ :=
          grantDrainEntranceR8eSectorAtLeader
            ring N hI.1.1 p hOldRoot
        have hLength :=
          grantDrainEntranceR8eBirthSectorLengthLe
            ring N z p d D hSuffix.1 hOldSector
        have hrOldInside : r.val < D.val := by
          have hrIn := hSuffix.2.2.1
          omega
        have hkOldInside : k.val < D.val := by
          omega
        have hOldSuffix :=
          grantDrainEntranceR8eSuffixFromSignalOneI
            ring N hI p D r hOldSector hSuffix.2.1
            hrOldInside hOldOneAtR
        exact Or.inl ⟨p, D, r, k, hOldSuffix, hSite,
          hOrder, hkOldInside, hOldZeroAtK, hOldOneAtR⟩
    · obtain ⟨p, d, hNewSector, hGap, hSite,
          hNoBullet, hNewReady, hNewZero⟩ := hReady
      have hpNe : p ≠ z := by
        intro hp
        have hAtZ : (canonicalBirth N z z).sg = true := by
          rw [hp] at hNewReady
          exact hNewReady
        rw [(grantDrainEntranceCanonicalBirthAtSite N z).2.2]
          at hAtZ
        cases hAtZ
      have hOldRoot : (N p).l = true := by
        have hNewRoot := hNewSector.2.1
        rw [grantDrainEntranceCanonicalBirthFrame N z p hpNe]
          at hNewRoot
        exact hNewRoot
      obtain ⟨D, hOldSector⟩ :=
        grantDrainEntranceR8eSectorAtLeader
          ring N hI.1.1 p hOldRoot
      have hLength :=
        grantDrainEntranceR8eBirthSectorLengthLe
          ring N z p d D hNewSector hOldSector
      have hOldReady : (N p).sg = true := by
        rw [← grantDrainEntranceCanonicalBirthFrame N z p hpNe]
        exact hNewReady
      have hOneBound : 1 < n := by
        have hdBound := d.isLt
        omega
      have hFirstAway :=
        grantDrainEntranceR8eBirthInteriorAvoidSite
          ring N z p d hNewSector
          (⟨1, hOneBound⟩ : Fin n)
          (show 0 < 1 by omega) hGap
      have hvAway : v ≠ z := by
        rw [hSite]
        change ring.rightNeighbor p ≠ z at hFirstAway
        exact hFirstAway
      have hOldZero : (N v).sg = false := by
        rw [← grantDrainEntranceCanonicalBirthFrame
          N z v hvAway]
        exact hNewZero
      have hOldNoBullet : ∀ j : Fin n, j.val < D.val →
          ¬ HasBullet N (PPL.shiftRight ring p j.val) :=
        grantDrainEntranceReadyLeaderSectorBulletFree
          ring N p D ((grantDrainEntranceIffILocal ring N).mp hI)
          hOldSector hOldReady
      exact Or.inr ⟨p, D, hOldSector,
        (show 1 < D.val by omega), hSite,
        hOldNoBullet, hOldReady, hOldZero⟩

/-- Source-side birth-to-E backward transport, from old I and
size n >= 3. Unlike the five-field interface, this is still
stated with its explicit size premise. -/
theorem grantDrainEntranceR8eBackwardRowSourceFollowerBirthSized
    {n : Nat} (ring : DirectedRing n) (hn : 3 ≤ n)
    (N : Fin n → CertNative) (e v : Fin n)
    (hI : I ring N)
    (hDef : GrantDrainEntranceSignalDefect ring
      (canonicalBirth (nativeE ring N e) e) v) :
    GrantDrainEntranceSignalDefect ring
      (nativeE ring N e) v := by
  have hLocal : GrantDrainEntranceILocal ring N :=
    (grantDrainEntranceIffILocal ring N).mp hI
  have hAfterLocal :=
    grantDrainEntranceILocalNativeEAll ring hn N e hLocal
  have hAfterI : I ring (nativeE ring N e) :=
    (grantDrainEntranceIffILocal ring (nativeE ring N e)).mpr
      hAfterLocal
  exact grantDrainEntranceR8eBirthBackwardOfI
    ring (nativeE ring N e) hAfterI e v hDef

/-- Responder-side birth-to-E backward transport with n >= 3.
The proof does not use eligibility: source and responder births
are the same monotone canonical-birth construction under I. -/
theorem grantDrainEntranceR8eBackwardRowResponderFollowerBirthSized
    {n : Nat} (ring : DirectedRing n) (hn : 3 ≤ n)
    (N : Fin n → CertNative) (e v : Fin n)
    (hI : I ring N)
    (hDef : GrantDrainEntranceSignalDefect ring
      (canonicalBirth (nativeE ring N e)
        (ring.rightNeighbor e)) v) :
    GrantDrainEntranceSignalDefect ring
      (nativeE ring N e) v := by
  have hLocal : GrantDrainEntranceILocal ring N :=
    (grantDrainEntranceIffILocal ring N).mp hI
  have hAfterLocal :=
    grantDrainEntranceILocalNativeEAll ring hn N e hLocal
  have hAfterI : I ring (nativeE ring N e) :=
    (grantDrainEntranceIffILocal ring (nativeE ring N e)).mpr
      hAfterLocal
  exact grantDrainEntranceR8eBirthBackwardOfI
    ring (nativeE ring N e) hAfterI (ring.rightNeighbor e)
    v hDef

/-- A canonical birth on a ring with at most two sites has
no signal-cleanup defect at any site, regardless of old fields.
A counted zero needs two ordered followers, while the only
possible positive-length ready sector contains the born root. -/
theorem grantDrainEntranceR8eBirthNoDefectSmall
    {n : Nat} (ring : DirectedRing n) (hn : n ≤ 2)
    (N : Fin n → CertNative) (z v : Fin n) :
    ¬ GrantDrainEntranceSignalDefect ring
      (canonicalBirth N z) v := by
  intro hDef
  rcases hDef with hCount | hReady
  · obtain ⟨p, d, r, k, hSuffix, hSite,
        hOrder, hInside, hZero, hOne⟩ := hCount
    have hDBound := d.isLt
    have hRLower := hSuffix.2.1
    omega
  · obtain ⟨p, d, hSector, hGap, hSite,
        hNoBullet, hSignal, hZero⟩ := hReady
    have hDBound := d.isLt
    have hnEq : n = 2 := by omega
    have hOneBound : 1 < n := by omega
    by_cases hpZ : p = z
    · have hSignalZ : (canonicalBirth N z z).sg = true := by
        rw [hpZ] at hSignal
        exact hSignal
      rw [(grantDrainEntranceCanonicalBirthAtSite N z).2.2]
        at hSignalZ
      cases hSignalZ
    · have hFirstFollower := hSector.2.2.2
        (⟨1, hOneBound⟩ : Fin n)
        (show 0 < 1 by omega) hGap
      have hNext : PPL.shiftRight ring p 1 = z := by
        apply Fin.ext
        have hpBound := p.isLt
        have hzBound := z.isLt
        have hDifferent : p.val ≠ z.val := by
          intro hVal
          exact hpZ (Fin.ext hVal)
        change (p.val + 1) % n = z.val
        by_cases hp0 : p.val = 0
        · rw [hp0, Nat.zero_add, Nat.mod_eq_of_lt (by omega : 1 < n)]
          omega
        · have hpn : p.val + 1 = n := by omega
          rw [hpn, Nat.mod_self]
          omega
      rw [hNext,
        (grantDrainEntranceCanonicalBirthAtSite N z).1]
        at hFirstFollower
      cases hFirstFollower

/-- Exact source-follower birth-to-E obligation of the pending
row structure, now obtained without any size premise. For
n>=3 use native-E ILocal closure; for n<=2 the born
configuration has no signal defects. -/
theorem grantDrainEntranceR8eBackwardRowSourceFollowerBirth
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (e v : Fin n)
    (hI : I ring N)
    (hxFollower : (nativeE ring N e e).l = false)
    (hDef : GrantDrainEntranceSignalDefect ring
      (canonicalBirth (nativeE ring N e) e) v) :
    GrantDrainEntranceSignalDefect ring
      (nativeE ring N e) v := by
  by_cases hn : 3 ≤ n
  · exact grantDrainEntranceR8eBackwardRowSourceFollowerBirthSized
      ring hn N e v hI hDef
  · have hnSmall : n ≤ 2 := by omega
    exact False.elim
      ((grantDrainEntranceR8eBirthNoDefectSmall
        ring hnSmall (nativeE ring N e) e v) hDef)

/-- Exact responder-follower birth-to-E obligation of the
pending row structure, with arbitrary inherited I scratch
and arbitrary post-E right-birth overwrite eligibility. -/
theorem grantDrainEntranceR8eBackwardRowResponderFollowerBirth
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (e v : Fin n)
    (hI : I ring N)
    (hyFollower :
      (nativeE ring N e (ring.rightNeighbor e)).l = false)
    (hDef : GrantDrainEntranceSignalDefect ring
      (canonicalBirth (nativeE ring N e)
        (ring.rightNeighbor e)) v) :
    GrantDrainEntranceSignalDefect ring
      (nativeE ring N e) v := by
  by_cases hn : 3 ≤ n
  · exact grantDrainEntranceR8eBackwardRowResponderFollowerBirthSized
      ring hn N e v hI hDef
  · have hnSmall : n ≤ 2 := by omega
    exact False.elim
      ((grantDrainEntranceR8eBirthNoDefectSmall
        ring hnSmall (nativeE ring N e)
        (ring.rightNeighbor e) v) hDef)

/-- The only remaining three native-E row obligations are
ready surviving responder, quiet surviving responder, and
leader death. Source/responder birth rows are now constructed
independently from I and are not part of this hypothesis. -/
structure GrantDrainEntranceR8eSurvivingPendingRows
    {n : Nat} (ring : DirectedRing n) : Prop where
  readyLeader :
    ∀ (N : Fin n → CertNative) (e v : Fin n),
      I ring N →
      (N (ring.rightNeighbor e)).l = true →
      (N (ring.rightNeighbor e)).sg = true →
      (nativeE ring N e (ring.rightNeighbor e)).l = true →
      GrantDrainEntranceSignalDefect ring (nativeE ring N e) v →
      GrantDrainEntranceSignalDefect ring N v
  quietLeader :
    ∀ (N : Fin n → CertNative) (e v : Fin n),
      I ring N →
      (N (ring.rightNeighbor e)).l = true →
      (N (ring.rightNeighbor e)).sg = false →
      (nativeE ring N e (ring.rightNeighbor e)).l = true →
      GrantDrainEntranceSignalDefect ring (nativeE ring N e) v →
      GrantDrainEntranceSignalDefect ring N v
  leaderDeath :
    ∀ (N : Fin n → CertNative) (e v : Fin n),
      I ring N →
      (N (ring.rightNeighbor e)).l = true →
      (nativeE ring N e (ring.rightNeighbor e)).l = false →
      GrantDrainEntranceSignalDefect ring (nativeE ring N e) v →
      GrantDrainEntranceSignalDefect ring N v

/-- Two birth fields discharged; the remaining source interface
is exactly the three harder E rows, without reasserting them. -/
theorem grantDrainEntranceR8eFollowerPendingRowsOfSurviving
    {n : Nat} (ring : DirectedRing n)
    (hRows : GrantDrainEntranceR8eSurvivingPendingRows ring) :
    GrantDrainEntranceR8eFollowerPendingRows ring := by
  refine
    { readyLeader := hRows.readyLeader
      quietLeader := hRows.quietLeader
      leaderDeath := hRows.leaderDeath
      sourceFollowerBirth := ?_
      responderFollowerBirth := ?_ }
  · intro N e v hI hxFollower hDef
    exact grantDrainEntranceR8eBackwardRowSourceFollowerBirth
      ring N e v hI hxFollower hDef
  · intro N e v hI hyFollower hDef
    exact grantDrainEntranceR8eBackwardRowResponderFollowerBirth
      ring N e v hI hyFollower hDef

/-- A root-preserving E row is defect-backward whenever its
responder is still a leader, its old and new leader arrays agree,
its source is activated, its target is signal zero, and all other
signals are framed. No equality of bullet fields is needed:
the old I zero trail at any old signal-one witness supplies the
old suffix condition. -/
theorem grantDrainEntranceR8eBackwardOnSurvivingLeaderFields
    {n : Nat} (ring : DirectedRing n)
    (N M : Fin n → CertNative) (e v : Fin n)
    (hI : I ring N)
    (hLeaders : ∀ i : Fin n, (M i).l = (N i).l)
    (hyLeader : (M (ring.rightNeighbor e)).l = true)
    (hyZero : (M (ring.rightNeighbor e)).sg = false)
    (hxOne : (M e).sg = true)
    (hSignalsAway : ∀ i : Fin n,
      i ≠ e → i ≠ ring.rightNeighbor e →
      (M i).sg = (N i).sg)
    (hDef : GrantDrainEntranceSignalDefect ring M v) :
    GrantDrainEntranceSignalDefect ring N v := by
  have hSectors :
      ∀ (p : Fin n) (d : Fin (n + 1)),
        sectorLength ring M p d ↔ sectorLength ring N p d := by
    intro p d
    exact grantDrainEntranceR8eSectorLengthOfLeaderArray
      ring N M hLeaders p d
  rcases hDef with hCount | hReady
  · obtain ⟨p, d, r, k, hSuffix, hSite,
        hOrder, hInside, hZero, hOne⟩ := hCount
    have hOldSector : sectorLength ring N p d :=
      (hSectors p d).mp hSuffix.1
    have hrPositive : 0 < r.val := by
      have hLower := hSuffix.2.1
      omega
    have hrNeY :
        PPL.shiftRight ring p r.val ≠ ring.rightNeighbor e := by
      intro hrAt
      have hFollower := hSuffix.1.2.2.2 r
        hrPositive hSuffix.2.2.1
      rw [hrAt, hyLeader] at hFollower
      cases hFollower
    have hkNeY :
        PPL.shiftRight ring p k.val ≠ ring.rightNeighbor e := by
      intro hkAt
      have hFollower := hSuffix.1.2.2.2 k
        (show 0 < k.val by omega) hInside
      rw [hkAt, hyLeader] at hFollower
      cases hFollower
    have hrNeX : PPL.shiftRight ring p r.val ≠ e := by
      intro hrAt
      have hLast := grantDrainEntranceR8eSourceLastBeforeLeader
        ring M e p d hSuffix.1 hyLeader r hSuffix.2.2.1 hrAt
      omega
    have hkNeX : PPL.shiftRight ring p k.val ≠ e := by
      intro hkAt
      have hBad := hZero
      rw [hkAt, hxOne] at hBad
      cases hBad
    have hOldOne :
        (N (PPL.shiftRight ring p r.val)).sg = true := by
      rw [← hSignalsAway
        (PPL.shiftRight ring p r.val) hrNeX hrNeY]
      exact hOne
    have hOldZero :
        (N (PPL.shiftRight ring p k.val)).sg = false := by
      rw [← hSignalsAway
        (PPL.shiftRight ring p k.val) hkNeX hkNeY]
      exact hZero
    have hOldSuffix :=
      grantDrainEntranceR8eSuffixFromSignalOneI
        ring N hI p d r hOldSector hSuffix.2.1
        hSuffix.2.2.1 hOldOne
    exact Or.inl ⟨p, d, r, k, hOldSuffix, hSite,
      hOrder, hInside, hOldZero, hOldOne⟩
  · obtain ⟨p, d, hNewSector, hGap, hSite,
        hNoBullet, hReady, hZero⟩ := hReady
    have hOldSector : sectorLength ring N p d :=
      (hSectors p d).mp hNewSector
    have hpNeY : p ≠ ring.rightNeighbor e := by
      intro hp
      have hBad := hReady
      rw [hp, hyZero] at hBad
      cases hBad
    have hpNeX : p ≠ e := by
      intro hp
      have hAt : PPL.shiftRight ring p 0 = e := by
        rw [grantDrainEntranceR8eShiftZero ring p]
        exact hp
      have hZeroInside :
          (⟨0, ring.hn⟩ : Fin n).val < d.val := by
        change 0 < d.val
        exact hNewSector.1
      have hLast := grantDrainEntranceR8eSourceLastBeforeLeader
        ring M e p d hNewSector hyLeader
        (⟨0, ring.hn⟩ : Fin n) hZeroInside hAt
      have hLastNat : 0 + 1 = d.val := by
        simpa only [Fin.val_mk] using hLast
      omega
    have hvNeX : v ≠ e := by
      intro hv
      have hBad := hZero
      rw [hv, hxOne] at hBad
      cases hBad
    have hvNeY : v ≠ ring.rightNeighbor e := by
      intro hv
      have hOneBound : 1 < n := by
        have hdBound := d.isLt
        omega
      have hFollower := hNewSector.2.2.2
        (⟨1, hOneBound⟩ : Fin n)
        (show 0 < 1 by omega) hGap
      have hFirst : PPL.shiftRight ring p 1 = v := by
        change ring.rightNeighbor p = v
        exact hSite.symm
      rw [hFirst, hv, hyLeader] at hFollower
      cases hFollower
    have hOldReady : (N p).sg = true := by
      rw [← hSignalsAway p hpNeX hpNeY]
      exact hReady
    have hOldZero : (N v).sg = false := by
      rw [← hSignalsAway v hvNeX hvNeY]
      exact hZero
    have hOldNoBullet : ∀ j : Fin n, j.val < d.val →
        ¬ HasBullet N (PPL.shiftRight ring p j.val) :=
      grantDrainEntranceReadyLeaderSectorBulletFree
        ring N p d ((grantDrainEntranceIffILocal ring N).mp hI)
        hOldSector hOldReady
    exact Or.inr ⟨p, d, hOldSector, hGap,
      hSite, hOldNoBullet, hOldReady, hOldZero⟩

/-- Both surviving-responder E rows, including source bullets,
are covered by one exact field-level theorem. Native E's
responder sg is always zero when OLD Y is a leader, and its
source sg is one whenever final Y remains a leader. -/
theorem grantDrainEntranceR8eBackwardRowLeaderSurvivesSized
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (N : Fin n → CertNative) (e v : Fin n)
    (hI : I ring N)
    (hyOldLeader : (N (ring.rightNeighbor e)).l = true)
    (hySurvives :
      (nativeE ring N e (ring.rightNeighbor e)).l = true)
    (hDef : GrantDrainEntranceSignalDefect
      ring (nativeE ring N e) v) :
    GrantDrainEntranceSignalDefect ring N v := by
  have hLeaders :=
    grantDrainEntranceNativeELeadersFixed
      ring hn N e (hySurvives.trans hyOldLeader.symm)
  have hyZero :
      (nativeE ring N e (ring.rightNeighbor e)).sg = false :=
    (grantDrainEntranceNativeELeaderBulletAfter
      ring hn N e hyOldLeader).2
  have hDistinct :=
    grantDrainEntranceRightNeighborDistinct ring hn e
  have hPairSurvives :
      (certLiteralEPair (N e)
        (N (ring.rightNeighbor e))).2.l = true := by
    simpa [nativeE, hDistinct] using hySurvives
  have hxOne : (nativeE ring N e e).sg = true := by
    simpa [nativeE] using
      grantDrainEntranceR8eSurvivingResponderSourceOne
        (N e) (N (ring.rightNeighbor e)) hPairSurvives
  have hSignalsAway : ∀ i : Fin n,
      i ≠ e → i ≠ ring.rightNeighbor e →
      (nativeE ring N e i).sg = (N i).sg := by
    intro i he hy
    rw [grantDrainEntranceNativeEFrame ring N e i he hy]
  exact grantDrainEntranceR8eBackwardOnSurvivingLeaderFields
    ring N (nativeE ring N e) e v hI
    hLeaders hySurvives hyZero hxOne hSignalsAway hDef

/-- For a ring with only one site, neither counted zeros nor
ready mismatch defects have enough follower offsets to exist. -/
theorem grantDrainEntranceR8eNoDefectSingleton
    {n : Nat} (ring : DirectedRing n) (hn : n ≤ 1)
    (N : Fin n → CertNative) (v : Fin n) :
    ¬ GrantDrainEntranceSignalDefect ring N v := by
  intro hDef
  rcases hDef with hCount | hReady
  · obtain ⟨p, d, r, k, hSuffix, hSite,
        hOrder, hInside, hZero, hOne⟩ := hCount
    have hDBound := d.isLt
    have hLower := hSuffix.2.1
    omega
  · obtain ⟨p, d, hSector, hGap, hSite,
        hNoBullet, hReady, hZero⟩ := hReady
    have hDBound := d.isLt
    omega

/-- Full n version of the surviving-responder row. The
small n=1 case cannot contain a post-E signal defect. -/
theorem grantDrainEntranceR8eBackwardRowLeaderSurvives
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (e v : Fin n)
    (hI : I ring N)
    (hyOldLeader : (N (ring.rightNeighbor e)).l = true)
    (hySurvives :
      (nativeE ring N e (ring.rightNeighbor e)).l = true)
    (hDef : GrantDrainEntranceSignalDefect
      ring (nativeE ring N e) v) :
    GrantDrainEntranceSignalDefect ring N v := by
  by_cases hn : 2 ≤ n
  · exact grantDrainEntranceR8eBackwardRowLeaderSurvivesSized
      ring hn N e v hI hyOldLeader hySurvives hDef
  · have hnSmall : n ≤ 1 := by omega
    exact False.elim
      ((grantDrainEntranceR8eNoDefectSingleton
        ring hnSmall (nativeE ring N e) v) hDef)

/-- The sole remaining all-n native-E obligation is leader
death; source/responder birth and both surviving responder
rows have explicit implementations rather than assumptions. -/
structure GrantDrainEntranceR8eDeathPendingRow
    {n : Nat} (ring : DirectedRing n) : Prop where
  leaderDeath :
    ∀ (N : Fin n → CertNative) (e v : Fin n),
      I ring N →
      (N (ring.rightNeighbor e)).l = true →
      (nativeE ring N e (ring.rightNeighbor e)).l = false →
      GrantDrainEntranceSignalDefect ring (nativeE ring N e) v →
      GrantDrainEntranceSignalDefect ring N v

theorem grantDrainEntranceR8eSurvivingRowsOfDeath
    {n : Nat} (ring : DirectedRing n)
    (hDeath : GrantDrainEntranceR8eDeathPendingRow ring) :
    GrantDrainEntranceR8eSurvivingPendingRows ring := by
  refine
    { readyLeader := ?_
      quietLeader := ?_
      leaderDeath := hDeath.leaderDeath }
  · intro N e v hI hyLeader hyReady hySurvive hDef
    exact grantDrainEntranceR8eBackwardRowLeaderSurvives
      ring N e v hI hyLeader hySurvive hDef
  · intro N e v hI hyLeader hyQuiet hySurvive hDef
    exact grantDrainEntranceR8eBackwardRowLeaderSurvives
      ring N e v hI hyLeader hySurvive hDef

/-- The last native-E row, when a responder leader dies.
An after-sector is framed, or merges an old prefix ending
at the killed leader with its old victim suffix. In the
merge case the old prefix is entirely signal zero. Therefore
a new one-before-zero witness must be wholly inside the old
victim suffix, where its physical bits are framed. -/
theorem grantDrainEntranceR8eBackwardRowLeaderDeathSized
    {n : Nat} (ring : DirectedRing n) (hn : 3 ≤ n)
    (N : Fin n → CertNative) (e v : Fin n)
    (hI : I ring N)
    (hyLeader : (N (ring.rightNeighbor e)).l = true)
    (hDeath :
      (nativeE ring N e (ring.rightNeighbor e)).l = false)
    (hDef : GrantDrainEntranceSignalDefect
      ring (nativeE ring N e) v) :
    GrantDrainEntranceSignalDefect ring N v := by
  have hLocal : GrantDrainEntranceILocal ring N :=
    (grantDrainEntranceIffILocal ring N).mp hI
  have hFields :=
    grantDrainEntranceNativeEDeathFields
      ring (by omega : 2 ≤ n) N e hLocal hyLeader hDeath
  have hEnds :=
    grantDrainEntranceILocalNativeEDeathEndpointZeros
      ring (by omega : 2 ≤ n) N e hLocal hyLeader hDeath
  rcases hDef with hCount | hReady
  · obtain ⟨p, d, r, k, hSuffix, hSite, hOrder,
        hInside, hZero, hOne⟩ := hCount
    rcases grantDrainEntranceDeathSectorPartition
      ring (by omega : 2 ≤ n) N e hLocal hyLeader hDeath
      p d hSuffix.1 with hFramed | hSplit
    · obtain ⟨hOldSector, hAvoid⟩ := hFramed
      have hOldFields : ∀ j : Fin n, j.val < d.val →
          N (PPL.shiftRight ring p j.val) =
            nativeE ring N e (PPL.shiftRight ring p j.val) := by
        intro j hj
        obtain ⟨he, hy⟩ := hAvoid j.val hj
        exact (grantDrainEntranceNativeEFrame
          ring N e (PPL.shiftRight ring p j.val) he hy).symm
      exact Or.inl
        (grantDrainEntranceR8eCountedBackwardOnFramedSector
          ring N (nativeE ring N e) p d r k v
          hSuffix hSite hOrder hInside hZero hOne
          hOldSector hOldFields)
    · obtain ⟨t, htPos, htLt, hY, hE, hOldHead, hOldTail⟩ :=
        hSplit
      have htBound : t.val < n := by
        have hdBound := d.isLt
        omega
      have hPrefix :=
        grantDrainEntranceDeathSourcePrefixClean
          ring (by omega : 2 ≤ n) N e hLocal hyLeader
          hDeath p t htPos htBound hY hE hOldHead
      have hPrefixZero : ∀ j : Nat, j < t.val →
          (nativeE ring N e
            (PPL.shiftRight ring p j)).sg = false := by
        intro j hj
        exact ((hFields (PPL.shiftRight ring p j)).2.2).trans
          (hPrefix j hj).2
      have hAtY :
          (nativeE ring N e
            (PPL.shiftRight ring p t.val)).sg = false := by
        rw [hY]
        exact hEnds.2.2.2
      have hrAfter : t.val < r.val := by
        by_cases hrBefore : r.val < t.val
        · have hBad := hOne
          rw [hPrefixZero r.val hrBefore] at hBad
          cases hBad
        · by_cases hrEqual : r.val = t.val
          · have hBad := hOne
            rw [hrEqual, hAtY] at hBad
            cases hBad
          · omega
      have hkAfter : t.val < k.val := by omega
      have hNoY : ∀ j : Nat, t.val < j → j < d.val →
          PPL.shiftRight ring p j ≠ ring.rightNeighbor e := by
        intro j hj hjLt heq
        have hAtJ := grantDrainEntranceDeathOffsetIndex
          ring p (ring.rightNeighbor e) j (by omega) heq
        have hAtT := grantDrainEntranceDeathOffsetIndex
          ring p (ring.rightNeighbor e) t.val htBound hY
        omega
      have hNoE : ∀ j : Nat, t.val < j → j < d.val →
          PPL.shiftRight ring p j ≠ e := by
        intro j hj hjLt heq
        have hAtJ := grantDrainEntranceDeathOffsetIndex
          ring p e j (by omega) heq
        have hAtE := grantDrainEntranceDeathOffsetIndex
          ring p e (t.val - 1) (by omega) hE
        omega
      have hOldOneSite :
          (N (PPL.shiftRight ring p r.val)).sg = true := by
        rw [← grantDrainEntranceNativeEFrame
          ring N e (PPL.shiftRight ring p r.val)
          (hNoE r.val hrAfter hSuffix.2.2.1)
          (hNoY r.val hrAfter hSuffix.2.2.1)]
        exact hOne
      have hOldZeroSite :
          (N (PPL.shiftRight ring p k.val)).sg = false := by
        rw [← grantDrainEntranceNativeEFrame
          ring N e (PPL.shiftRight ring p k.val)
          (hNoE k.val hkAfter hInside)
          (hNoY k.val hkAfter hInside)]
        exact hZero
      have hTailShift : ∀ j : Nat, t.val ≤ j →
          PPL.shiftRight ring (ring.rightNeighbor e) (j - t.val) =
            PPL.shiftRight ring p j := by
        intro j hj
        calc
          PPL.shiftRight ring (ring.rightNeighbor e) (j - t.val) =
              PPL.shiftRight ring
                (PPL.shiftRight ring p t.val) (j - t.val) := by
              rw [hY]
          _ = PPL.shiftRight ring p (t.val + (j - t.val)) :=
            grantDrainEntranceArcShiftRightAdd
              ring p t.val (j - t.val)
          _ = PPL.shiftRight ring p j := by
            congr 1
            omega
      have hrBound : r.val - t.val < n := by omega
      have hkBound : k.val - t.val < n := by omega
      have hOldOne :
          (N (PPL.shiftRight ring (ring.rightNeighbor e)
            (r.val - t.val))).sg = true := by
        rw [hTailShift r.val (by omega)]
        exact hOldOneSite
      have hOldZero :
          (N (PPL.shiftRight ring (ring.rightNeighbor e)
            (k.val - t.val))).sg = false := by
        rw [hTailShift k.val (by omega)]
        exact hOldZeroSite
      have hOldSuffix :
          GrantDrainEntranceSignalSuffixSite ring N
            (ring.rightNeighbor e)
            (⟨d.val - t.val, show d.val - t.val < n + 1 by omega⟩ : Fin (n + 1))
            (⟨r.val - t.val, hrBound⟩ : Fin n) := by
        apply grantDrainEntranceR8eSuffixFromSignalOneI
          ring N hI (ring.rightNeighbor e)
          (⟨d.val - t.val, show d.val - t.val < n + 1 by omega⟩ : Fin (n + 1))
          (⟨r.val - t.val, hrBound⟩ : Fin n)
          hOldTail
          (show 1 ≤ r.val - t.val by omega)
          (show r.val - t.val < d.val - t.val by omega)
        simpa only [Fin.val_mk] using hOldOne
      refine Or.inl ⟨ring.rightNeighbor e,
        (⟨d.val - t.val, show d.val - t.val < n + 1 by omega⟩ : Fin (n + 1)),
        (⟨r.val - t.val, hrBound⟩ : Fin n),
        (⟨k.val - t.val, hkBound⟩ : Fin n),
        hOldSuffix, ?_, ?_, ?_, ?_, ?_⟩
      · exact hSite.trans (hTailShift k.val (by omega)).symm
      · change r.val - t.val < k.val - t.val
        omega
      · change k.val - t.val < d.val - t.val
        omega
      · simpa only [Fin.val_mk] using hOldZero
      · simpa only [Fin.val_mk] using hOldOne
  · obtain ⟨p, d, hSector, hGap, hSite,
        hNoBullet, hSignal, hZero⟩ := hReady
    rcases grantDrainEntranceDeathSectorPartition
      ring (by omega : 2 ≤ n) N e hLocal hyLeader hDeath
      p d hSector with hFramed | hSplit
    · obtain ⟨hOldSector, hAvoid⟩ := hFramed
      have hOldFields : ∀ j : Fin n, j.val < d.val →
          N (PPL.shiftRight ring p j.val) =
            nativeE ring N e (PPL.shiftRight ring p j.val) := by
        intro j hj
        obtain ⟨he, hy⟩ := hAvoid j.val hj
        exact (grantDrainEntranceNativeEFrame
          ring N e (PPL.shiftRight ring p j.val) he hy).symm
      exact Or.inr
        (grantDrainEntranceR8eReadyBackwardOnFramedSector
          ring N (nativeE ring N e) p d v hSector hGap
          hSite hNoBullet hSignal hZero hOldSector hOldFields)
    · obtain ⟨t, htPos, htLt, hY, hE, hOldHead, hOldTail⟩ :=
        hSplit
      have htBound : t.val < n := by
        have hdBound := d.isLt
        omega
      have hPrefix :=
        grantDrainEntranceDeathSourcePrefixClean
          ring (by omega : 2 ≤ n) N e hLocal hyLeader
          hDeath p t htPos htBound hY hE hOldHead
      have hRootZero :
          (nativeE ring N e p).sg = false := by
        have hAtZero := (hPrefix 0 htPos).2
        rw [grantDrainEntranceR8eShiftZero ring p] at hAtZero
        exact ((hFields p).2.2).trans hAtZero
      rw [hRootZero] at hSignal
      cases hSignal

/-- The two sites of a two-cycle are exactly e and its
clockwise responder; this uses the *literal* ring successor
rather than an invented second physical edge. -/
theorem grantDrainEntranceR8eTwoSiteExhaustive
    {n : Nat} (ring : DirectedRing n) (hn : n = 2)
    (e p : Fin n) :
    p = e ∨ p = ring.rightNeighbor e := by
  by_cases hp : p = e
  · exact Or.inl hp
  · right
    apply Fin.ext
    have hpBound := p.isLt
    have heBound := e.isLt
    have hDifferent : p.val ≠ e.val := by
      intro hVal
      exact hp (Fin.ext hVal)
    change p.val = (e.val + 1) % n
    by_cases he0 : e.val = 0
    · rw [he0, Nat.zero_add, Nat.mod_eq_of_lt (by omega : 1 < n)]
      omega
    · have hen : e.val + 1 = n := by omega
      rw [hen, Nat.mod_self]
      omega

/-- On at most two sites, a death-service signal defect is
impossible under I. Counted-zero needs at least three ordered
sites. A ready mismatch would need a surviving root, which in
the two-site death row is source e; the literal death row resets
that source signal to zero. -/
theorem grantDrainEntranceR8eBackwardRowLeaderDeathSmall
    {n : Nat} (ring : DirectedRing n) (hnSmall : n ≤ 2)
    (N : Fin n → CertNative) (e v : Fin n)
    (hI : I ring N)
    (hyLeader : (N (ring.rightNeighbor e)).l = true)
    (hDeath :
      (nativeE ring N e (ring.rightNeighbor e)).l = false)
    (hDef : GrantDrainEntranceSignalDefect
      ring (nativeE ring N e) v) :
    GrantDrainEntranceSignalDefect ring N v := by
  rcases hDef with hCount | hReady
  · obtain ⟨p, d, r, k, hSuffix, hSite,
        hOrder, hInside, hZero, hOne⟩ := hCount
    have hDBound := d.isLt
    have hLower := hSuffix.2.1
    omega
  · obtain ⟨p, d, hSector, hGap, hSite,
        hNoBullet, hSignal, hZero⟩ := hReady
    have hDBound := d.isLt
    have hnEq : n = 2 := by omega
    have hLocal : GrantDrainEntranceILocal ring N :=
      (grantDrainEntranceIffILocal ring N).mp hI
    have hEnds :=
      grantDrainEntranceILocalNativeEDeathEndpointZeros
        ring (show 2 ≤ n by omega) N e hLocal hyLeader hDeath
    rcases grantDrainEntranceR8eTwoSiteExhaustive
      ring hnEq e p with hpE | hpY
    · have hBad := hSignal
      rw [hpE, hEnds.2.1] at hBad
      cases hBad
    · have hBad := hSector.2.1
      rw [hpY, hDeath] at hBad
      cases hBad

/-- Exact all-n death row: n>=3 uses the source/victim
sector-merge proof; n<=2 has no possible new defect. -/
theorem grantDrainEntranceR8eBackwardRowLeaderDeath
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (e v : Fin n)
    (hI : I ring N)
    (hyLeader : (N (ring.rightNeighbor e)).l = true)
    (hDeath :
      (nativeE ring N e (ring.rightNeighbor e)).l = false)
    (hDef : GrantDrainEntranceSignalDefect
      ring (nativeE ring N e) v) :
    GrantDrainEntranceSignalDefect ring N v := by
  by_cases hn : 3 ≤ n
  · exact grantDrainEntranceR8eBackwardRowLeaderDeathSized
      ring hn N e v hI hyLeader hDeath hDef
  · have hnSmall : n ≤ 2 := by omega
    exact grantDrainEntranceR8eBackwardRowLeaderDeathSmall
      ring hnSmall N e v hI hyLeader hDeath hDef

/-- Every one of the three remaining E row obligations is
now discharged from literal native E and old I. -/
theorem grantDrainEntranceR8eDeathPendingRowProved
    {n : Nat} (ring : DirectedRing n) :
    GrantDrainEntranceR8eDeathPendingRow ring := by
  refine { leaderDeath := ?_ }
  intro N e v hI hyLeader hDeath hDef
  exact grantDrainEntranceR8eBackwardRowLeaderDeath
    ring N e v hI hyLeader hDeath hDef

/-- Assembled all-three-outcome pointwise backward producer.
Production rings have n>=5, so the n>=3 hypothesis is ample;
the source/responder birth rows and all six E classes are proved
separately above. -/
theorem grantDrainEntranceR8eDefectBackward
    {n : Nat} (ring : DirectedRing n) (hn : 3 ≤ n) :
    ∀ (N : Fin n → CertNative) (e : Fin n),
      I ring N →
      ∀ v : Fin n,
        (GrantDrainEntranceSignalDefect
          ring (nativeE ring N e) v →
          GrantDrainEntranceSignalDefect ring N v) ∧
        (GrantDrainEntranceSignalDefect
          ring (canonicalBirth (nativeE ring N e) e) v →
          GrantDrainEntranceSignalDefect ring N v) ∧
        (GrantDrainEntranceSignalDefect
          ring (canonicalBirth (nativeE ring N e)
            (ring.rightNeighbor e)) v →
          GrantDrainEntranceSignalDefect ring N v) := by
  exact grantDrainEntranceR8eDefectBackwardOfFollowerPendingRows
    ring hn
    (grantDrainEntranceR8eFollowerPendingRowsOfSurviving
      ring
      (grantDrainEntranceR8eSurvivingRowsOfDeath
        ring (grantDrainEntranceR8eDeathPendingRowProved ring)))

/-- Physical R8e nonincrease, consuming the assembled literal
native three-outcome backward producer and sum transfer. -/
theorem grantDrainEntranceR8ePotentialNonincreaseProved
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 3 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    GrantDrainEntranceR8ePotentialNonincrease ring fresh update := by
  exact (grantDrainEntranceR8ePotentialClaimsOfBackward
    ring fresh update
    (grantDrainEntranceR8eDefectBackward ring hn)).1

/-- Physical R8e nominated strict drop, consuming exactly
the same full native three-outcome backward producer. -/
theorem grantDrainEntranceR8ePotentialNominatedDropProved
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 3 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    GrantDrainEntranceR8ePotentialNominatedDrop
      ring fresh update := by
  exact (grantDrainEntranceR8ePotentialClaimsOfBackward
    ring fresh update
    (grantDrainEntranceR8eDefectBackward ring hn)).2

/-- Complete ready-leader-survives E row, including an
arbitrary source bullet. The uniform surviving-leader theorem
does not need the old responder's readiness bit. -/
theorem grantDrainEntranceR8eBackwardRowReadyLeaderSurvives
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (e v : Fin n)
    (hI : I ring N)
    (hyLeader : (N (ring.rightNeighbor e)).l = true)
    (hyReady : (N (ring.rightNeighbor e)).sg = true)
    (hSurvive :
      (nativeE ring N e (ring.rightNeighbor e)).l = true)
    (hDef : GrantDrainEntranceSignalDefect
      ring (nativeE ring N e) v) :
    GrantDrainEntranceSignalDefect ring N v := by
  exact grantDrainEntranceR8eBackwardRowLeaderSurvives
    ring N e v hI hyLeader hSurvive hDef

/-- Complete quiet-leader-survives E row, also with arbitrary
source bullet and arbitrary old resident responder bullet. -/
theorem grantDrainEntranceR8eBackwardRowQuietLeaderSurvives
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (e v : Fin n)
    (hI : I ring N)
    (hyLeader : (N (ring.rightNeighbor e)).l = true)
    (hyQuiet : (N (ring.rightNeighbor e)).sg = false)
    (hSurvive :
      (nativeE ring N e (ring.rightNeighbor e)).l = true)
    (hDef : GrantDrainEntranceSignalDefect
      ring (nativeE ring N e) v) :
    GrantDrainEntranceSignalDefect ring N v := by
  exact grantDrainEntranceR8eBackwardRowLeaderSurvives
    ring N e v hI hyLeader hSurvive hDef

end L3.GrantDrainEntrance

namespace L3.GrantDrainShared

open L3.HeadlineRenewal
open L3.SmallRenewal
open L3.GrantDrainEntrance

set_option autoImplicit false
set_option Elab.async false

/-- Actual physical native, request and grant projection of one SMALL
reference cut. The whole original SMALL Cartesian state is retained in
scratch; the already-revealed IID edge word is retained separately. -/
def sharedSmallSourceView {n : Nat}
    (z : RenewalSmallReference n) (past : List (Fin n)) :
    GrantDrainState n (RenewalSmallReference n) :=
  { native := nativeProjection z.1
    request := fun i => (z.1 i).req
    grant := fun i => (z.1 i).grant
    scratch := z
    history := past }

/-- Adapted responder DCC request from the OLD SMALL Cartesian pair.
The success-suppression bit affects grant production, not this DCC
request. No future scheduler edge is read. -/
def sharedSmallSourceFresh {n : Nat}
    (ring : DirectedRing n)
    (s : GrantDrainState n (RenewalSmallReference n))
    (e : Fin n) : Bool :=
  (dccStep
    (s.scratch.1 e)
    (s.scratch.1 (ring.rightNeighbor e))
    (certificateStep (compileAdvice (ceilLogTwo n))
      (s.scratch.1 e)
      (s.scratch.1 (ring.rightNeighbor e))).2.2).request

/-- The exact next SMALL reference, not a new independent scheduler.
The source history is updated by grantDrainStep itself. -/
def sharedSmallSourceScratchNext {n : Nat}
    (ring : DirectedRing n)
    (s : GrantDrainState n (RenewalSmallReference n))
    (e : Fin n) : RenewalSmallReference n :=
  renewalSmallNext ring s.scratch e

def SmallGrantDrainPostSeenFieldSquare {n : Nat}
    (ring : DirectedRing n) : Prop :=
  (compileAdvice (ceilLogTwo n)).useSmall = true →
    ∀ (z : RenewalSmallReference n)
      (past : List (Fin n)) (e : Fin n),
      smallReferenceSeenComplete z →
        (grantDrainStep ring
          (sharedSmallSourceFresh ring)
          (sharedSmallSourceScratchNext ring)
          (sharedSmallSourceView z past) e).native =
            nativeProjection (renewalSmallNext ring z e).1 ∧
        (grantDrainStep ring
          (sharedSmallSourceFresh ring)
          (sharedSmallSourceScratchNext ring)
          (sharedSmallSourceView z past) e).request =
            (fun i : Fin n => ((renewalSmallNext ring z e).1 i).req) ∧
        (grantDrainStep ring
          (sharedSmallSourceFresh ring)
          (sharedSmallSourceScratchNext ring)
          (sharedSmallSourceView z past) e).grant =
            (fun i : Fin n => ((renewalSmallNext ring z e).1 i).grant)

/-- Extensionality for *all five* source coordinates; in particular
we do not silently discard the SMALL scratch or adapted history. -/
private theorem sharedSmallSourceStateExt
    {n : Nat} {Scratch : Type}
    (s t : GrantDrainState n Scratch)
    (hnative : s.native = t.native)
    (hrequest : s.request = t.request)
    (hgrant : s.grant = t.grant)
    (hscratch : s.scratch = t.scratch)
    (hhistory : s.history = t.history) : s = t := by
  cases s with
  | mk ns rs gs ss hs =>
    cases t with
    | mk nt rt gt st ht =>
      cases hnative
      cases hrequest
      cases hgrant
      cases hscratch
      cases hhistory
      rfl

theorem sharedSmallCanonicalRefinementOfFieldSquare
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (hfields : SmallGrantDrainPostSeenFieldSquare ring) :
    SmallGrantDrainRefinement ring
      (grantDrainCanonicalModel ring hn
        (sharedSmallSourceFresh ring)
        (sharedSmallSourceScratchNext ring))
      sharedSmallSourceView := by
  constructor
  · intro z past _
    exact ⟨rfl, (fun _ => rfl), (fun _ => rfl)⟩
  · intro z past e hseen
    have hrow := hfields hsmall z past e hseen
    change grantDrainStep ring
      (sharedSmallSourceFresh ring)
      (sharedSmallSourceScratchNext ring)
      (sharedSmallSourceView z past) e =
        sharedSmallSourceView (renewalSmallNext ring z e) (e :: past)
    apply sharedSmallSourceStateExt
    · exact hrow.1
    · exact hrow.2.1
    · exact hrow.2.2
    · rfl
    · rfl

/-- A special case of the first missing native equation:
on a rooted, post-seen, grant-free SMALL cut the actual physical
SMALL next native is exactly the source's nativeE step. This is a
nontrivial row check, not the all-old-grant field-square theorem. -/
theorem sharedSmallGrantFreeNativeSquare
    {n : Nat} (ring : DirectedRing n) (hn : 3 ≤ n)
    (z : RenewalSmallReference n)
    (hroot : headlineRooted ring z.1)
    (hseen : smallReferenceSeenComplete z)
    (hfree : NativeLiftGrantFree z.1)
    (past : List (Fin n)) (e : Fin n) :
    (grantDrainStep ring
      (sharedSmallSourceFresh ring)
      (sharedSmallSourceScratchNext ring)
      (sharedSmallSourceView z past) e).native =
        nativeProjection (renewalSmallNext ring z e).1 := by
  have hsourceFree : GrantFree (sharedSmallSourceView z past) := by
    intro i
    exact hfree i
  have hreference :
      nativeProjection (renewalSmallNext ring z e).1 =
        nativeE ring (nativeProjection z.1) e :=
    smallReferenceGrantFreeNativeStep ring hn z
      ⟨hroot, hseen, hfree⟩ e
  change grantDrainNativeNext ring
    (sharedSmallSourceView z past) e =
      nativeProjection (renewalSmallNext ring z e).1
  rw [grantDrainNative_empty ring
    (sharedSmallSourceView z past) e hsourceFree]
  exact hreference.symm

/-- The grant coordinate of the field square also agrees on every
grant-free post-seen SMALL cut. This uses the actual suppressed SMALL
pair T2 and exact source grant-free closure, not merely noncloning. -/
theorem sharedSmallGrantFreeGrantSquare
    {n : Nat} (ring : DirectedRing n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (z : RenewalSmallReference n)
    (hseen : smallReferenceSeenComplete z)
    (hfree : NativeLiftGrantFree z.1)
    (past : List (Fin n)) (e : Fin n) :
    (grantDrainStep ring
      (sharedSmallSourceFresh ring)
      (sharedSmallSourceScratchNext ring)
      (sharedSmallSourceView z past) e).grant =
        (fun i : Fin n => ((renewalSmallNext ring z e).1 i).grant) := by
  have hsourceFree : GrantFree (sharedSmallSourceView z past) := by
    intro i
    exact hfree i
  have hnextSourceFree :=
    grantDrainStep_preserves_GrantFree
      ring (sharedSmallSourceFresh ring)
      (sharedSmallSourceScratchNext ring)
      (sharedSmallSourceView z past) e hsourceFree
  have hnextSmallFree :=
    smallReferenceGrantFreeStep ring hsmall z hseen hfree e
  funext i
  rw [hnextSourceFree i, hnextSmallFree i]

/-- Nonempty five-site post-seen Cartesian cut from the pre-existing
SmallRenewal witness. Every one-step actual SMALL native
successor of this cut passes the source-native square check.
This is a genuine one-edge *reachable successor from that cut*;
it does not claim the cut was generated from a globally blank seed,
nor test the still-missing request field or old-GRANT rows. -/
private def sharedSmallFiveRing : DirectedRing 5 := ⟨by decide⟩

theorem sharedSmallFiveNativeOneStepWitness :
    ∃ z : RenewalSmallReference 5,
      smallReferenceGrantFreeRootedSeen sharedSmallFiveRing z ∧
      ∀ e : Fin 5,
        (grantDrainStep sharedSmallFiveRing
          (sharedSmallSourceFresh sharedSmallFiveRing)
          (sharedSmallSourceScratchNext sharedSmallFiveRing)
          (sharedSmallSourceView z []) e).native =
        nativeProjection
          (renewalSmallNext sharedSmallFiveRing z e).1 := by
  obtain ⟨z, hz⟩ := smallReferenceClassNonempty
  have hclass : smallReferenceGrantFreeRootedSeen
      sharedSmallFiveRing z := hz
  refine ⟨z, hclass, ?_⟩
  intro e
  exact sharedSmallGrantFreeNativeSquare sharedSmallFiveRing
    (by omega : 3 ≤ 5) z hclass.1 hclass.2.1 hclass.2.2 [] e

theorem sharedSmallR8eNonincreaseOfFieldSquare
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (hfields : SmallGrantDrainPostSeenFieldSquare ring)
    (z : RenewalSmallReference n)
    (past : List (Fin n)) (e : Fin n)
    (hseen : smallReferenceSeenComplete z)
    (hintermediate : GrantDrainEntranceIntermediateZ ring
      (sharedSmallSourceView z past)) :
    grantDrainEntranceSignalCleanupPotential ring
        (nativeProjection (renewalSmallNext ring z e).1) ≤
      grantDrainEntranceSignalCleanupPotential ring
        (nativeProjection z.1) := by
  have hsource :=
    (grantDrainEntranceR8ePotentialNonincreaseProved ring
      (by omega : 3 ≤ n)
      (sharedSmallSourceFresh ring)
      (sharedSmallSourceScratchNext ring))
      (sharedSmallSourceView z past) e hintermediate
  have hnext := (hfields hsmall z past e hseen).1
  rw [hnext] at hsource
  exact hsource

theorem sharedSmallR8eNominatedDropOfFieldSquare
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (hfields : SmallGrantDrainPostSeenFieldSquare ring)
    (z : RenewalSmallReference n)
    (past : List (Fin n))
    (hseen : smallReferenceSeenComplete z)
    (hintermediate : GrantDrainEntranceIntermediateZ ring
      (sharedSmallSourceView z past))
    (hpositive : 0 <
      grantDrainEntranceSignalCleanupPotential ring
        (nativeProjection z.1)) :
    ∃ e : Fin n,
      grantDrainEntranceSignalCleanupPotential ring
          (nativeProjection (renewalSmallNext ring z e).1) <
        grantDrainEntranceSignalCleanupPotential ring
          (nativeProjection z.1) := by
  obtain ⟨e, hsource⟩ :=
    (grantDrainEntranceR8ePotentialNominatedDropProved ring
      (by omega : 3 ≤ n)
      (sharedSmallSourceFresh ring)
      (sharedSmallSourceScratchNext ring))
      (sharedSmallSourceView z past) hintermediate hpositive
  refine ⟨e, ?_⟩
  have hnext := (hfields hsmall z past e hseen).1
  rw [hnext] at hsource
  exact hsource

end L3.GrantDrainShared

namespace L3.GrantDrainShared

open L3.HeadlineRenewal
open L3.SmallRenewal
open L3.GrantDrainEntrance
open L3.RenewalReferenceClock

set_option autoImplicit false
set_option Elab.async false

/-!
The proof is for n ≥ 5, as required by grantDrainCanonicalModel.
The revised Prop itself assumes SMALL advice; all OLD requests and
grants and all private Cartesian records remain arbitrary.
-/

private def sharedSmallFireToBase : GrantDrainFire → Option FireSel
  | .none => none
  | .leftLocal =>
      some { kind := .F0, site := .siteX, reqX := true, grantX := true }
  | .rightLocal =>
      some { kind := .F1, site := .siteY, reqY := true, grantY := true }
  | .cross =>
      some { kind := .F2, site := .siteX, reqX := true, grantY := true }

private def sharedSmallNativeOutSource {c : Compiled}
    (x y : Agent c) : CertNative :=
  if fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2)
      .siteX = true then firedNative
  else (certLiteralEPair x.certNative y.certNative).1

private def sharedSmallNativeOutResponder {c : Compiled}
    (x y : Agent c) : CertNative :=
  if fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2)
      .siteY = true then firedNative
  else (certLiteralEPair x.certNative y.certNative).2

private theorem sharedSmallAgent_l_ite
    {c : Compiled} (p : Prop) [Decidable p] (a b : Agent c) :
    (if p then a else b).l =
      if p then a.l else b.l := by
  split <;> rfl

private theorem sharedSmallAgent_b_ite
    {c : Compiled} (p : Prop) [Decidable p] (a b : Agent c) :
    (if p then a else b).b =
      if p then a.b else b.b := by
  split <;> rfl

private theorem sharedSmallAgent_sh_ite
    {c : Compiled} (p : Prop) [Decidable p] (a b : Agent c) :
    (if p then a else b).sh =
      if p then a.sh else b.sh := by
  split <;> rfl

private theorem sharedSmallAgent_sg_ite
    {c : Compiled} (p : Prop) [Decidable p] (a b : Agent c) :
    (if p then a else b).sg =
      if p then a.sg else b.sg := by
  split <;> rfl

private theorem sharedSmallBaseSource_l
    (c : Compiled) (ev : CertEvent) (x y : Agent c) :
    (baseStep c ev x y).1.l =
      (sharedSmallNativeOutSource x y).l := by
  unfold baseStep
  by_cases hf : fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2)
      .siteX = true
  · simp [hf, sharedSmallNativeOutSource, Agent.setNative,
      Agent.setCPriv, sharedSmallAgent_l_ite]
  · simp [hf, sharedSmallNativeOutSource, Agent.setNative,
      Agent.setCPriv, sharedSmallAgent_l_ite]

private theorem sharedSmallBaseSource_b
    (c : Compiled) (ev : CertEvent) (x y : Agent c) :
    (baseStep c ev x y).1.b =
      (sharedSmallNativeOutSource x y).b := by
  unfold baseStep
  by_cases hf : fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2)
      .siteX = true
  · simp [hf, sharedSmallNativeOutSource, Agent.setNative,
      Agent.setCPriv, sharedSmallAgent_b_ite]
  · simp [hf, sharedSmallNativeOutSource, Agent.setNative,
      Agent.setCPriv, sharedSmallAgent_b_ite]

private theorem sharedSmallBaseSource_sh
    (c : Compiled) (ev : CertEvent) (x y : Agent c) :
    (baseStep c ev x y).1.sh =
      (sharedSmallNativeOutSource x y).sh := by
  unfold baseStep
  by_cases hf : fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2)
      .siteX = true
  · simp [hf, sharedSmallNativeOutSource, Agent.setNative,
      Agent.setCPriv, sharedSmallAgent_sh_ite]
  · simp [hf, sharedSmallNativeOutSource, Agent.setNative,
      Agent.setCPriv, sharedSmallAgent_sh_ite]

private theorem sharedSmallBaseSource_sg
    (c : Compiled) (ev : CertEvent) (x y : Agent c) :
    (baseStep c ev x y).1.sg =
      (sharedSmallNativeOutSource x y).sg := by
  unfold baseStep
  by_cases hf : fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2)
      .siteX = true
  · simp [hf, sharedSmallNativeOutSource, Agent.setNative,
      Agent.setCPriv, sharedSmallAgent_sg_ite]
  · simp [hf, sharedSmallNativeOutSource, Agent.setNative,
      Agent.setCPriv, sharedSmallAgent_sg_ite]

private theorem sharedSmallBaseResponder_l
    (c : Compiled) (ev : CertEvent) (x y : Agent c) :
    (baseStep c ev x y).2.l =
      (sharedSmallNativeOutResponder x y).l := by
  unfold baseStep
  by_cases hf : fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2)
      .siteY = true
  · simp [hf, sharedSmallNativeOutResponder, Agent.setNative,
      Agent.setCPriv, sharedSmallAgent_l_ite]
  · simp [hf, sharedSmallNativeOutResponder, Agent.setNative,
      Agent.setCPriv, sharedSmallAgent_l_ite]

private theorem sharedSmallBaseResponder_b
    (c : Compiled) (ev : CertEvent) (x y : Agent c) :
    (baseStep c ev x y).2.b =
      (sharedSmallNativeOutResponder x y).b := by
  unfold baseStep
  by_cases hf : fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2)
      .siteY = true
  · simp [hf, sharedSmallNativeOutResponder, Agent.setNative,
      Agent.setCPriv, sharedSmallAgent_b_ite]
  · simp [hf, sharedSmallNativeOutResponder, Agent.setNative,
      Agent.setCPriv, sharedSmallAgent_b_ite]

private theorem sharedSmallBaseResponder_sh
    (c : Compiled) (ev : CertEvent) (x y : Agent c) :
    (baseStep c ev x y).2.sh =
      (sharedSmallNativeOutResponder x y).sh := by
  unfold baseStep
  by_cases hf : fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2)
      .siteY = true
  · simp [hf, sharedSmallNativeOutResponder, Agent.setNative,
      Agent.setCPriv, sharedSmallAgent_sh_ite]
  · simp [hf, sharedSmallNativeOutResponder, Agent.setNative,
      Agent.setCPriv, sharedSmallAgent_sh_ite]

private theorem sharedSmallBaseResponder_sg
    (c : Compiled) (ev : CertEvent) (x y : Agent c) :
    (baseStep c ev x y).2.sg =
      (sharedSmallNativeOutResponder x y).sg := by
  unfold baseStep
  by_cases hf : fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2)
      .siteY = true
  · simp [hf, sharedSmallNativeOutResponder, Agent.setNative,
      Agent.setCPriv, sharedSmallAgent_sg_ite]
  · simp [hf, sharedSmallNativeOutResponder, Agent.setNative,
      Agent.setCPriv, sharedSmallAgent_sg_ite]

private theorem sharedSmallBaseNativePair
    (c : Compiled) (ev : CertEvent) (x y : Agent c) :
    (baseStep c ev x y).1.certNative =
      sharedSmallNativeOutSource x y ∧
    (baseStep c ev x y).2.certNative =
      sharedSmallNativeOutResponder x y := by
  constructor
  · change CertNative.mk (baseStep c ev x y).1.l
        (baseStep c ev x y).1.b (baseStep c ev x y).1.sh
        (baseStep c ev x y).1.sg = _
    rw [sharedSmallBaseSource_l, sharedSmallBaseSource_b,
      sharedSmallBaseSource_sh, sharedSmallBaseSource_sg]
  · change CertNative.mk (baseStep c ev x y).2.l
        (baseStep c ev x y).2.b (baseStep c ev x y).2.sh
        (baseStep c ev x y).2.sg = _
    rw [sharedSmallBaseResponder_l, sharedSmallBaseResponder_b,
      sharedSmallBaseResponder_sh, sharedSmallBaseResponder_sg]

private theorem sharedSmallTransitionNativePair
    (c : Compiled) (x y : Agent c) :
    (transition c x y).1.certNative =
      sharedSmallNativeOutSource x y ∧
    (transition c x y).2.certNative =
      sharedSmallNativeOutResponder x y := by
  have hx :
      (transition c x y).1.certNative =
        (baseStep c (certificateStep c x y).2.2 x y).1.certNative := rfl
  have hy :
      (transition c x y).2.certNative =
        (baseStep c (certificateStep c x y).2.2 x y).2.certNative := rfl
  have hb := sharedSmallBaseNativePair c
    (certificateStep c x y).2.2 x y
  exact ⟨hx.trans hb.1, hy.trans hb.2⟩

private theorem sharedSmallPostEEndpoints
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (z : RenewalSmallReference n) (e : Fin n) :
    (nativeE ring (nativeProjection z.1) e e) =
      (postEInfo (z.1 e) (z.1 (ring.rightNeighbor e))).eX ∧
    (nativeE ring (nativeProjection z.1) e
      (ring.rightNeighbor e)) =
      (postEInfo (z.1 e) (z.1 (ring.rightNeighbor e))).eY := by
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring hn e
  constructor
  · simp [nativeE, nativeProjection, postEInfo]
  · simp [nativeE, nativeProjection, postEInfo, hne]

private theorem sharedSmallFireExact
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (z : RenewalSmallReference n) (past : List (Fin n))
    (e : Fin n) :
    sharedSmallFireToBase
        (grantDrainSelect ring (sharedSmallSourceView z past) e) =
      fireSelect (z.1 e) (z.1 (ring.rightNeighbor e))
        (postEInfo (z.1 e) (z.1 (ring.rightNeighbor e))).eX
        (postEInfo (z.1 e) (z.1 (ring.rightNeighbor e))).eY := by
  have hp := sharedSmallPostEEndpoints ring hn z e
  have hleft :
      grantDrainEligible (nativeE ring (nativeProjection z.1) e) e =
        (!(postEInfo (z.1 e) (z.1 (ring.rightNeighbor e))).eX.l &&
          ((postEInfo (z.1 e)
            (z.1 (ring.rightNeighbor e))).eX.b.val == 0)) := by
    change
      (!(nativeE ring (nativeProjection z.1) e e).l &&
        ((nativeE ring (nativeProjection z.1) e e).b.val == 0)) = _
    rw [hp.1]
  have hright :
      grantDrainEligible (nativeE ring (nativeProjection z.1) e)
          (ring.rightNeighbor e) =
        (!(postEInfo (z.1 e) (z.1 (ring.rightNeighbor e))).eY.l &&
          ((postEInfo (z.1 e)
            (z.1 (ring.rightNeighbor e))).eY.b.val == 0)) := by
    change
      (!(nativeE ring (nativeProjection z.1) e
          (ring.rightNeighbor e)).l &&
        ((nativeE ring (nativeProjection z.1) e
          (ring.rightNeighbor e)).b.val == 0)) = _
    rw [hp.2]
  change
    sharedSmallFireToBase
      (if (z.1 e).req && (z.1 e).grant &&
          grantDrainEligible (nativeE ring (nativeProjection z.1) e) e
       then GrantDrainFire.leftLocal
       else if (z.1 (ring.rightNeighbor e)).req &&
          (z.1 (ring.rightNeighbor e)).grant &&
          grantDrainEligible (nativeE ring (nativeProjection z.1) e)
            (ring.rightNeighbor e)
       then GrantDrainFire.rightLocal
       else if (z.1 e).req && (z.1 (ring.rightNeighbor e)).grant &&
          grantDrainEligible (nativeE ring (nativeProjection z.1) e) e
       then GrantDrainFire.cross
       else GrantDrainFire.none) =
      fireSelect (z.1 e) (z.1 (ring.rightNeighbor e))
        (postEInfo (z.1 e) (z.1 (ring.rightNeighbor e))).eX
        (postEInfo (z.1 e) (z.1 (ring.rightNeighbor e))).eY
  simp only [hleft, hright]
  unfold fireSelect
  dsimp only
  by_cases hx :
      ((z.1 e).req && (z.1 e).grant &&
        (!(postEInfo (z.1 e)
          (z.1 (ring.rightNeighbor e))).eX.l &&
         (postEInfo (z.1 e)
          (z.1 (ring.rightNeighbor e))).eX.b.val == 0)) = true
  · simp only [if_pos hx, sharedSmallFireToBase]
  · simp only [if_neg hx]
    by_cases hy :
        ((z.1 (ring.rightNeighbor e)).req &&
          (z.1 (ring.rightNeighbor e)).grant &&
          (!(postEInfo (z.1 e)
            (z.1 (ring.rightNeighbor e))).eY.l &&
           (postEInfo (z.1 e)
            (z.1 (ring.rightNeighbor e))).eY.b.val == 0)) = true
    · simp only [if_pos hy, sharedSmallFireToBase]
    · simp only [if_neg hy]
      by_cases hc :
          ((z.1 e).req &&
            (z.1 (ring.rightNeighbor e)).grant &&
            (!(postEInfo (z.1 e)
              (z.1 (ring.rightNeighbor e))).eX.l &&
             (postEInfo (z.1 e)
              (z.1 (ring.rightNeighbor e))).eX.b.val == 0)) = true
      · simp only [if_pos hc, sharedSmallFireToBase]
      · simp only [if_neg hc, sharedSmallFireToBase]

private theorem sharedSmallSelectedNativePair
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (z : RenewalSmallReference n) (past : List (Fin n))
    (e : Fin n) :
    (grantDrainNativeNext ring
      (sharedSmallSourceView z past) e) e =
        (transition (compileAdvice (ceilLogTwo n))
          (z.1 e) (z.1 (ring.rightNeighbor e))).1.certNative ∧
    (grantDrainNativeNext ring
      (sharedSmallSourceView z past) e) (ring.rightNeighbor e) =
        (transition (compileAdvice (ceilLogTwo n))
          (z.1 e) (z.1 (ring.rightNeighbor e))).2.certNative := by
  have hp := sharedSmallPostEEndpoints ring hn z e
  have hpX :
      (nativeE ring (sharedSmallSourceView z past).native e e) =
        (postEInfo (z.1 e) (z.1 (ring.rightNeighbor e))).eX := by
    change (nativeE ring (nativeProjection z.1) e e) =
      (postEInfo (z.1 e) (z.1 (ring.rightNeighbor e))).eX
    exact hp.1
  have hpY :
      (nativeE ring (sharedSmallSourceView z past).native e
        (ring.rightNeighbor e)) =
        (postEInfo (z.1 e) (z.1 (ring.rightNeighbor e))).eY := by
    change (nativeE ring (nativeProjection z.1) e
      (ring.rightNeighbor e)) =
      (postEInfo (z.1 e) (z.1 (ring.rightNeighbor e))).eY
    exact hp.2
  have hf := sharedSmallFireExact ring hn z past e
  have ht := sharedSmallTransitionNativePair
    (compileAdvice (ceilLogTwo n))
    (z.1 e) (z.1 (ring.rightNeighbor e))
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring hn e
  have hrev : e ≠ ring.rightNeighbor e := by
    intro h
    exact hne h.symm
  have hx :
      (grantDrainNativeNext ring
        (sharedSmallSourceView z past) e) e =
      (if fireAtSite
        (sharedSmallFireToBase
          (grantDrainSelect ring (sharedSmallSourceView z past) e))
          .siteX then firedNative
       else (postEInfo (z.1 e)
         (z.1 (ring.rightNeighbor e))).eX) := by
    cases hs : grantDrainSelect ring (sharedSmallSourceView z past) e with
    | none =>
        simp only [grantDrainNativeNext, hs, sharedSmallFireToBase,
          fireAtSite]
        change
          (nativeE ring (sharedSmallSourceView z past).native e e) =
            (postEInfo (z.1 e) (z.1 (ring.rightNeighbor e))).eX
        exact hpX
    | leftLocal =>
        simp [grantDrainNativeNext, hs, sharedSmallFireToBase,
          fireAtSite, canonicalBirth]
    | rightLocal =>
        simp only [grantDrainNativeNext, hs, sharedSmallFireToBase,
          fireAtSite]
        change
          (canonicalBirth
            (nativeE ring (sharedSmallSourceView z past).native e)
            (ring.rightNeighbor e) e) =
              (postEInfo (z.1 e) (z.1 (ring.rightNeighbor e))).eX
        simp only [canonicalBirth, if_neg hrev]
        exact hpX
    | cross =>
        simp [grantDrainNativeNext, hs, sharedSmallFireToBase,
          fireAtSite, canonicalBirth]
  have hy :
      (grantDrainNativeNext ring
        (sharedSmallSourceView z past) e) (ring.rightNeighbor e) =
      (if fireAtSite
        (sharedSmallFireToBase
          (grantDrainSelect ring (sharedSmallSourceView z past) e))
          .siteY then firedNative
       else (postEInfo (z.1 e)
         (z.1 (ring.rightNeighbor e))).eY) := by
    cases hs : grantDrainSelect ring (sharedSmallSourceView z past) e with
    | none =>
        simp only [grantDrainNativeNext, hs, sharedSmallFireToBase,
          fireAtSite]
        change
          (nativeE ring (sharedSmallSourceView z past).native e
            (ring.rightNeighbor e)) =
              (postEInfo (z.1 e) (z.1 (ring.rightNeighbor e))).eY
        exact hpY
    | leftLocal =>
        simp only [grantDrainNativeNext, hs, sharedSmallFireToBase,
          fireAtSite]
        change
          (canonicalBirth
            (nativeE ring (sharedSmallSourceView z past).native e)
            e (ring.rightNeighbor e)) =
              (postEInfo (z.1 e) (z.1 (ring.rightNeighbor e))).eY
        simp only [canonicalBirth, if_neg hne]
        exact hpY
    | rightLocal =>
        simp [grantDrainNativeNext, hs, sharedSmallFireToBase,
          fireAtSite, canonicalBirth]
    | cross =>
        simp only [grantDrainNativeNext, hs, sharedSmallFireToBase,
          fireAtSite]
        change
          (canonicalBirth
            (nativeE ring (sharedSmallSourceView z past).native e)
            e (ring.rightNeighbor e)) =
              (postEInfo (z.1 e) (z.1 (ring.rightNeighbor e))).eY
        simp only [canonicalBirth, if_neg hne]
        exact hpY
  constructor
  · calc
      (grantDrainNativeNext ring
          (sharedSmallSourceView z past) e) e =
        (if fireAtSite
          (sharedSmallFireToBase
            (grantDrainSelect ring (sharedSmallSourceView z past) e))
            .siteX then firedNative
         else (postEInfo (z.1 e)
           (z.1 (ring.rightNeighbor e))).eX) := hx
      _ = sharedSmallNativeOutSource
          (z.1 e) (z.1 (ring.rightNeighbor e)) := by
        unfold sharedSmallNativeOutSource
        rw [hf]
        rfl
      _ = (transition (compileAdvice (ceilLogTwo n))
          (z.1 e) (z.1 (ring.rightNeighbor e))).1.certNative :=
        ht.1.symm
  · calc
      (grantDrainNativeNext ring
          (sharedSmallSourceView z past) e) (ring.rightNeighbor e) =
        (if fireAtSite
          (sharedSmallFireToBase
            (grantDrainSelect ring (sharedSmallSourceView z past) e))
            .siteY then firedNative
         else (postEInfo (z.1 e)
           (z.1 (ring.rightNeighbor e))).eY) := hy
      _ = sharedSmallNativeOutResponder
          (z.1 e) (z.1 (ring.rightNeighbor e)) := by
        unfold sharedSmallNativeOutResponder
        rw [hf]
        rfl
      _ = (transition (compileAdvice (ceilLogTwo n))
          (z.1 e) (z.1 (ring.rightNeighbor e))).2.certNative :=
        ht.2.symm

private theorem sharedSmallNativePhysicalSquare
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (z : RenewalSmallReference n) (past : List (Fin n))
    (e : Fin n) :
    grantDrainNativeNext ring
        (sharedSmallSourceView z past) e =
      nativeProjection (headlinePhysicalNext ring z.1 e) := by
  have hpair := sharedSmallSelectedNativePair ring hn z past e
  funext i
  by_cases he : i = e
  · subst i
    calc
      (grantDrainNativeNext ring
          (sharedSmallSourceView z past) e) e =
        (transition (compileAdvice (ceilLogTwo n))
          (z.1 e) (z.1 (ring.rightNeighbor e))).1.certNative :=
        hpair.1
      _ = nativeProjection (headlinePhysicalNext ring z.1 e) e :=
        (congrArg Agent.certNative
          (headlineRendezvousStepAtSource ring z.1 e)).symm
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      calc
        (grantDrainNativeNext ring
            (sharedSmallSourceView z past) e)
            (ring.rightNeighbor e) =
          (transition (compileAdvice (ceilLogTwo n))
            (z.1 e) (z.1 (ring.rightNeighbor e))).2.certNative :=
          hpair.2
        _ = nativeProjection (headlinePhysicalNext ring z.1 e)
            (ring.rightNeighbor e) :=
          (congrArg Agent.certNative
            (headlineRendezvousStepAtResponder ring hn z.1 e)).symm
    · have haway :
          (grantDrainNativeNext ring
            (sharedSmallSourceView z past) e) i =
            (z.1 i).certNative := by
        have hE :
            (nativeE ring (sharedSmallSourceView z past).native e i) =
              (z.1 i).certNative := by
          simp only [nativeE, if_neg he, if_neg hj]
          rfl
        cases hs : grantDrainSelect ring
            (sharedSmallSourceView z past) e with
        | none =>
            simp only [grantDrainNativeNext, hs]
            exact hE
        | leftLocal =>
            simp only [grantDrainNativeNext, hs, canonicalBirth,
              if_neg he]
            exact hE
        | rightLocal =>
            simp only [grantDrainNativeNext, hs, canonicalBirth,
              if_neg hj]
            exact hE
        | cross =>
            simp only [grantDrainNativeNext, hs, canonicalBirth,
              if_neg he]
            exact hE
      exact haway.trans
        (congrArg Agent.certNative
          (headlineRendezvousStepAway ring z.1 e i he hj)).symm

private theorem sharedSmallNativeMaskedSquare
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (z : RenewalSmallReference n) (past : List (Fin n))
    (e : Fin n) :
    (grantDrainStep ring (sharedSmallSourceFresh ring)
      (sharedSmallSourceScratchNext ring)
      (sharedSmallSourceView z past) e).native =
        nativeProjection (renewalSmallNext ring z e).1 := by
  change grantDrainNativeNext ring
    (sharedSmallSourceView z past) e =
      nativeProjection
        (renewalMaskedStep ring z.1 e
          (renewalSmallCut ring z.1 z.2 e))
  exact (sharedSmallNativePhysicalSquare ring hn z past e).trans
    (renewalBankMaskedNativeFrame ring z.1 e
      (renewalSmallCut ring z.1 z.2 e)).symm

private theorem sharedSmallLiteralTokenRow
    {c : Compiled} (x y : Agent c) (fx fy : CertNative)
    (fresh : Bool) (fire : GrantDrainFire) :
    ((tokenStep x y fx fy
        (sharedSmallFireToBase fire) fresh false).1,
     (tokenStep x y fx fy
        (sharedSmallFireToBase fire) fresh false).2.1) =
      grantDrainTokenRow x.req x.grant y.req y.grant
        fx.l fy.l fresh fire := by
  cases hrx : x.req <;>
    cases hgx : x.grant <;>
    cases hry : y.req <;>
    cases hgy : y.grant <;>
    cases hlx : fx.l <;>
    cases hly : fy.l <;>
    cases fresh <;>
    cases fire <;>
    simp [sharedSmallFireToBase, tokenStep,
      grantDrainTokenRow, fireAtSite,
      hrx, hgx, hry, hgy, hlx, hly] <;> decide

private theorem sharedSmallSuppressedTokenFidelity
    (c : Compiled) (x y : Agent c) (fire : GrantDrainFire)
    (hfire : fireSelect x y
      (postEInfo x y).eX (postEInfo x y).eY =
        sharedSmallFireToBase fire) :
    bankStagePairTokens (renewalMaskedPair c true x y) =
      grantDrainTokenRow x.req x.grant y.req y.grant
        (transition c x y).1.l (transition c x y).2.l
        (dccStep x y (certificateStep c x y).2.2).request
        fire := by
  change
    ((renewalNoNewGrantTokens c x y).1,
      (renewalNoNewGrantTokens c x y).2.1) =
      grantDrainTokenRow x.req x.grant y.req y.grant
        (transition c x y).1.l (transition c x y).2.l
        (dccStep x y (certificateStep c x y).2.2).request
        fire
  unfold renewalNoNewGrantTokens
  rw [hfire]
  exact sharedSmallLiteralTokenRow x y
    (transition c x y).1.certNative
    (transition c x y).2.certNative
    (dccStep x y (certificateStep c x y).2.2).request fire

private theorem sharedSmallMaskedTokenBranch
    (c : Compiled) (hsmall : c.useSmall = true)
    (x y : Agent c) :
    bankStagePairTokens
        (renewalMaskedPair c (smallPair x y c.K).2.2 x y) =
      bankStagePairTokens (renewalMaskedPair c true x y) := by
  cases hs : (smallPair x y c.K).2.2 with
  | true =>
      simp [hs, renewalMaskedPair]
  | false =>
      have hbit : baseBankSuccessBit c x y = false := by
        simp [baseBankSuccessBit, hsmall, hs]
      have hnative := sharedSmallTransitionNativePair c x y
      have htoken :
          baseTokenOutputs c (certificateStep c x y).2.2 x y =
            renewalNoNewGrantTokens c x y := by
        unfold baseTokenOutputs renewalNoNewGrantTokens
        rw [hnative.1, hnative.2, hbit]
        rfl
      have hf := headlineRendezvousTransitionTokenFrame c x y
      change
        (({ req := (transition c x y).1.req,
            grant := (transition c x y).1.grant } : TokPair),
         ({ req := (transition c x y).2.req,
            grant := (transition c x y).2.grant } : TokPair)) =
        (({ req := (renewalNoNewGrantTokens c x y).1.req,
            grant := (renewalNoNewGrantTokens c x y).1.grant } : TokPair),
         ({ req := (renewalNoNewGrantTokens c x y).2.1.req,
            grant := (renewalNoNewGrantTokens c x y).2.1.grant } : TokPair))
      rw [hf.1, hf.2.1, hf.2.2.1, hf.2.2.2, htoken]

private def sharedSmallSourceTokenRow {n : Nat}
    (ring : DirectedRing n)
    (z : RenewalSmallReference n) (past : List (Fin n))
    (e : Fin n) : TokPair × TokPair :=
  grantDrainTokenRow
    (z.1 e).req (z.1 e).grant
    (z.1 (ring.rightNeighbor e)).req
    (z.1 (ring.rightNeighbor e)).grant
    (grantDrainNativeNext ring
      (sharedSmallSourceView z past) e e).l
    (grantDrainNativeNext ring
      (sharedSmallSourceView z past) e
        (ring.rightNeighbor e)).l
    (sharedSmallSourceFresh ring
      (sharedSmallSourceView z past) e)
    (grantDrainSelect ring
      (sharedSmallSourceView z past) e)

private theorem sharedSmallSelectedTokenSquare
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (z : RenewalSmallReference n)
    (hseen : smallReferenceSeenComplete z)
    (past : List (Fin n)) (e : Fin n) :
    sharedSmallSourceTokenRow ring z past e =
      bankStagePairTokens
        (renewalMaskedPair
          (compileAdvice (ceilLogTwo n))
          (renewalSmallCut ring z.1 z.2 e)
          (z.1 e) (z.1 (ring.rightNeighbor e))) := by
  have hnative := sharedSmallSelectedNativePair ring hn z past e
  have hfire := sharedSmallFireExact ring hn z past e
  have htoken := sharedSmallSuppressedTokenFidelity
    (compileAdvice (ceilLogTwo n))
    (z.1 e) (z.1 (ring.rightNeighbor e))
    (grantDrainSelect ring (sharedSmallSourceView z past) e)
    hfire.symm
  have hmask := sharedSmallMaskedTokenBranch
    (compileAdvice (ceilLogTwo n)) hsmall
    (z.1 e) (z.1 (ring.rightNeighbor e))
  have hx := congrArg CertNative.l hnative.1
  have hy := congrArg CertNative.l hnative.2
  unfold sharedSmallSourceTokenRow
  rw [hx, hy]
  change
    grantDrainTokenRow
      (z.1 e).req (z.1 e).grant
      (z.1 (ring.rightNeighbor e)).req
      (z.1 (ring.rightNeighbor e)).grant
      (transition (compileAdvice (ceilLogTwo n))
        (z.1 e) (z.1 (ring.rightNeighbor e))).1.l
      (transition (compileAdvice (ceilLogTwo n))
        (z.1 e) (z.1 (ring.rightNeighbor e))).2.l
      (dccStep (z.1 e) (z.1 (ring.rightNeighbor e))
        (certificateStep (compileAdvice (ceilLogTwo n))
          (z.1 e) (z.1 (ring.rightNeighbor e))).2.2).request
      (grantDrainSelect ring (sharedSmallSourceView z past) e) =
        bankStagePairTokens
          (renewalMaskedPair
            (compileAdvice (ceilLogTwo n))
            (renewalSmallCut ring z.1 z.2 e)
            (z.1 e) (z.1 (ring.rightNeighbor e)))
  calc
    _ = bankStagePairTokens
        (renewalMaskedPair (compileAdvice (ceilLogTwo n)) true
          (z.1 e) (z.1 (ring.rightNeighbor e))) := htoken.symm
    _ = bankStagePairTokens
        (renewalMaskedPair
          (compileAdvice (ceilLogTwo n))
          (renewalSmallCut ring z.1 z.2 e)
          (z.1 e) (z.1 (ring.rightNeighbor e))) := by
      rw [smallReferenceSeenCutSuccess ring z hseen e]
      exact hmask.symm

theorem sharedSmallPostSeenFieldSquareHolds
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n) :
    SmallGrantDrainPostSeenFieldSquare ring := by
  intro hsmall z past e hseen
  have hnative :=
    sharedSmallNativeMaskedSquare ring (by omega : 2 ≤ n) z past e
  have hrow := sharedSmallSelectedTokenSquare ring
    (by omega : 2 ≤ n) hsmall z hseen past e
  have hreqsource :
      (sharedSmallSourceTokenRow ring z past e).1.req =
        (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          (renewalSmallCut ring z.1 z.2 e)
          (z.1 e) (z.1 (ring.rightNeighbor e))).1.req :=
    congrArg (fun p : TokPair × TokPair => p.1.req) hrow
  have hreqresponder :
      (sharedSmallSourceTokenRow ring z past e).2.req =
        (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          (renewalSmallCut ring z.1 z.2 e)
          (z.1 e) (z.1 (ring.rightNeighbor e))).2.req :=
    congrArg (fun p : TokPair × TokPair => p.2.req) hrow
  have hgrantsource :
      (sharedSmallSourceTokenRow ring z past e).1.grant =
        (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          (renewalSmallCut ring z.1 z.2 e)
          (z.1 e) (z.1 (ring.rightNeighbor e))).1.grant :=
    congrArg (fun p : TokPair × TokPair => p.1.grant) hrow
  have hgrantresponder :
      (sharedSmallSourceTokenRow ring z past e).2.grant =
        (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          (renewalSmallCut ring z.1 z.2 e)
          (z.1 e) (z.1 (ring.rightNeighbor e))).2.grant :=
    congrArg (fun p : TokPair × TokPair => p.2.grant) hrow
  constructor
  · exact hnative
  · constructor
    · funext i
      change
        (if i = e then
           (sharedSmallSourceTokenRow ring z past e).1.req
         else if i = ring.rightNeighbor e then
           (sharedSmallSourceTokenRow ring z past e).2.req
         else (z.1 i).req) =
        (if i = e then
           (renewalMaskedPair (compileAdvice (ceilLogTwo n))
             (renewalSmallCut ring z.1 z.2 e)
             (z.1 e) (z.1 (ring.rightNeighbor e))).1
         else if i = ring.rightNeighbor e then
           (renewalMaskedPair (compileAdvice (ceilLogTwo n))
             (renewalSmallCut ring z.1 z.2 e)
             (z.1 e) (z.1 (ring.rightNeighbor e))).2
         else z.1 i).req
      by_cases he : i = e
      · rw [if_pos he, if_pos he]
        exact hreqsource
      · rw [if_neg he, if_neg he]
        by_cases hj : i = ring.rightNeighbor e
        · simp only [hj, ↓reduceIte]
          exact hreqresponder
        · simp only [hj, ↓reduceIte]
    · funext i
      change
        (if i = e then
           (sharedSmallSourceTokenRow ring z past e).1.grant
         else if i = ring.rightNeighbor e then
           (sharedSmallSourceTokenRow ring z past e).2.grant
         else (z.1 i).grant) =
        (if i = e then
           (renewalMaskedPair (compileAdvice (ceilLogTwo n))
             (renewalSmallCut ring z.1 z.2 e)
             (z.1 e) (z.1 (ring.rightNeighbor e))).1
         else if i = ring.rightNeighbor e then
           (renewalMaskedPair (compileAdvice (ceilLogTwo n))
             (renewalSmallCut ring z.1 z.2 e)
             (z.1 e) (z.1 (ring.rightNeighbor e))).2
         else z.1 i).grant
      by_cases he : i = e
      · rw [if_pos he, if_pos he]
        exact hgrantsource
      · rw [if_neg he, if_neg he]
        by_cases hj : i = ring.rightNeighbor e
        · simp only [hj, ↓reduceIte]
          exact hgrantresponder
        · simp only [hj, ↓reduceIte]

theorem sharedSmallCanonicalRefinementHolds
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    SmallGrantDrainRefinement ring
      (grantDrainCanonicalModel ring hn
        (sharedSmallSourceFresh ring)
        (sharedSmallSourceScratchNext ring))
      sharedSmallSourceView := by
  exact sharedSmallCanonicalRefinementOfFieldSquare
    ring hn hsmall (sharedSmallPostSeenFieldSquareHolds ring hn)

theorem sharedSmallR8eNonincrease
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (z : RenewalSmallReference n) (past : List (Fin n))
    (e : Fin n)
    (hseen : smallReferenceSeenComplete z)
    (hintermediate : GrantDrainEntranceIntermediateZ ring
      (sharedSmallSourceView z past)) :
    grantDrainEntranceSignalCleanupPotential ring
        (nativeProjection (renewalSmallNext ring z e).1) ≤
      grantDrainEntranceSignalCleanupPotential ring
        (nativeProjection z.1) := by
  exact sharedSmallR8eNonincreaseOfFieldSquare ring hn hsmall
    (sharedSmallPostSeenFieldSquareHolds ring hn)
    z past e hseen hintermediate

theorem sharedSmallR8eNominatedDrop
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (z : RenewalSmallReference n) (past : List (Fin n))
    (hseen : smallReferenceSeenComplete z)
    (hintermediate : GrantDrainEntranceIntermediateZ ring
      (sharedSmallSourceView z past))
    (hpositive : 0 <
      grantDrainEntranceSignalCleanupPotential ring
        (nativeProjection z.1)) :
    ∃ e : Fin n,
      grantDrainEntranceSignalCleanupPotential ring
          (nativeProjection (renewalSmallNext ring z e).1) <
        grantDrainEntranceSignalCleanupPotential ring
          (nativeProjection z.1) := by
  exact sharedSmallR8eNominatedDropOfFieldSquare ring hn hsmall
    (sharedSmallPostSeenFieldSquareHolds ring hn)
    z past hseen hintermediate hpositive

end L3.GrantDrainShared

namespace L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-!
The exact OLD-Y source classifier is
grantDrainLedgerYSource from GrantDrainMarks. In particular,
a Y label is retired on F1/F2 or leader sink rather than being
credited to an unrelated surviving X grant. Y moves to X only
on the literal no-FIRE, non-HOLD transport row. Distinct labels
are allowed to merge at X; none can be copied or resurrected.
-/

private def sharedFullLabelRow {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring) (z : M.State) (e : Fin n) :
    TokPair × TokPair :=
  grantDrainTokenRow
    ((M.view z).request e) ((M.view z).grant e)
    ((M.view z).request (ring.rightNeighbor e))
    ((M.view z).grant (ring.rightNeighbor e))
    (grantDrainNativeNext ring (M.view z) e e).l
    (grantDrainNativeNext ring (M.view z) e
      (ring.rightNeighbor e)).l
    (M.freshRequest (M.view z) e)
    (grantDrainSelect ring (M.view z) e)

private def sharedFullLabelYSource {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring) (z : M.State) (e : Fin n) :
    Option Bool :=
  grantDrainLedgerYSource
    ((M.view z).request (ring.rightNeighbor e))
    ((M.view z).grant (ring.rightNeighbor e))
    (grantDrainNativeNext ring (M.view z) e e).l
    (grantDrainNativeNext ring (M.view z) e
      (ring.rightNeighbor e)).l
    (grantDrainSelect ring (M.view z) e)
    (sharedFullLabelRow M z e)

/-- The exhaustive two-slot source and sink cases. No assumption
about the hostile fresh request or consistency of FIRE is used.
The four conclusions are literal facts of the source token owner.
Only the eight finite local coordinates are decided. -/
private theorem sharedFullLabelLocalSources
    (rx gx ry gy lx ly fresh : Bool) (fire : GrantDrainFire) :
    (((grantDrainTokenRow rx gx ry gy lx ly fresh fire).1.grant =
        true →
        gx = true ∨
          (gy = true ∧
            grantDrainLedgerYSource ry gy lx ly fire
              (grantDrainTokenRow rx gx ry gy lx ly fresh fire) =
                some false)) ∧
      ((grantDrainTokenRow rx gx ry gy lx ly fresh fire).2.grant =
        true →
        gy = true ∧
          grantDrainLedgerYSource ry gy lx ly fire
            (grantDrainTokenRow rx gx ry gy lx ly fresh fire) =
              some true)) ∧
    ((grantDrainLedgerYSource ry gy lx ly fire
        (grantDrainTokenRow rx gx ry gy lx ly fresh fire) =
          some false) →
        gy = true ∧
          (grantDrainTokenRow rx gx ry gy lx ly fresh fire).1.grant =
            true) ∧
    ((grantDrainLedgerYSource ry gy lx ly fire
        (grantDrainTokenRow rx gx ry gy lx ly fresh fire) =
          some true) →
        gy = true ∧
          (grantDrainTokenRow rx gx ry gy lx ly fresh fire).2.grant =
            true) := by
  cases rx <;> cases gx <;> cases ry <;> cases gy <;>
    cases lx <;> cases ly <;> cases fresh <;>
    cases fire <;> decide

/-- The selected physical grant bits are exactly the local row;
the responder is distinct from the source for n >= 2. -/
private theorem sharedFullLabelStepSlots {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring) (hn : 2 ≤ n)
    (z : M.State) (e : Fin n) :
    (M.view (M.step z e)).grant e =
      (sharedFullLabelRow M z e).1.grant ∧
    (M.view (M.step z e)).grant (ring.rightNeighbor e) =
      (sharedFullLabelRow M z e).2.grant := by
  constructor
  · rw [M.stepExact z e]
    change
      (if e = e then (sharedFullLabelRow M z e).1.grant
       else if e = ring.rightNeighbor e then
         (sharedFullLabelRow M z e).2.grant
       else (M.view z).grant e) =
        (sharedFullLabelRow M z e).1.grant
    rw [if_pos rfl]
  · have hne : ring.rightNeighbor e ≠ e :=
      EWord.rightNeighborDifferent ring hn e
    rw [M.stepExact z e]
    change
      (if ring.rightNeighbor e = e then
         (sharedFullLabelRow M z e).1.grant
       else if ring.rightNeighbor e = ring.rightNeighbor e then
         (sharedFullLabelRow M z e).2.grant
       else (M.view z).grant (ring.rightNeighbor e)) =
        (sharedFullLabelRow M z e).2.grant
    rw [if_neg hne, if_pos rfl]

/-- Sourced, never manufactured: the NEW X grant comes from OLD X
or a real Y-to-X grant transfer. The NEW Y grant always comes
from OLD Y. The converse clauses rule out spurious Y labels. -/
private theorem sharedFullLabelStepSources {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring) (hn : 2 ≤ n)
    (z : M.State) (e : Fin n) :
    (((M.view (M.step z e)).grant e = true →
        (M.view z).grant e = true ∨
          ((M.view z).grant (ring.rightNeighbor e) = true ∧
            sharedFullLabelYSource M z e = some false)) ∧
      ((M.view (M.step z e)).grant (ring.rightNeighbor e) =
          true →
        (M.view z).grant (ring.rightNeighbor e) = true ∧
          sharedFullLabelYSource M z e = some true)) ∧
    (sharedFullLabelYSource M z e = some false →
      (M.view z).grant (ring.rightNeighbor e) = true ∧
        (M.view (M.step z e)).grant e = true) ∧
    (sharedFullLabelYSource M z e = some true →
      (M.view z).grant (ring.rightNeighbor e) = true ∧
        (M.view (M.step z e)).grant (ring.rightNeighbor e) =
          true) := by
  have hslots := sharedFullLabelStepSlots M hn z e
  have hlocal := sharedFullLabelLocalSources
    ((M.view z).request e) ((M.view z).grant e)
    ((M.view z).request (ring.rightNeighbor e))
    ((M.view z).grant (ring.rightNeighbor e))
    (grantDrainNativeNext ring (M.view z) e e).l
    (grantDrainNativeNext ring (M.view z) e
      (ring.rightNeighbor e)).l
    (M.freshRequest (M.view z) e)
    (grantDrainSelect ring (M.view z) e)
  constructor
  · constructor
    · intro h
      exact hlocal.1.1 (hslots.1.symm.trans h)
    · intro h
      exact hlocal.1.2 (hslots.2.symm.trans h)
  · constructor
    · intro h
      have hrow := hlocal.2.1 h
      exact ⟨hrow.1, hslots.1.trans hrow.2⟩
    · intro h
      have hrow := hlocal.2.2 h
      exact ⟨hrow.1, hslots.2.trans hrow.2⟩

/-- Exact off-edge frame, obtained from the model's stepExact
rather than rewriting a HeadlineConfiguration protocol step. -/
private theorem sharedFullLabelAwayFrame {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring)
    (z : M.State) (e i : Fin n)
    (hx : i ≠ e) (hy : i ≠ ring.rightNeighbor e) :
    (M.view (M.step z e)).grant i = (M.view z).grant i := by
  rw [M.stepExact z e]
  change
    (if i = e then (sharedFullLabelRow M z e).1.grant
     else if i = ring.rightNeighbor e then
       (sharedFullLabelRow M z e).2.grant
     else (M.view z).grant i) = (M.view z).grant i
  simp only [if_neg hx, if_neg hy]

/-- True full-set host update. Every OLD X label is retained at X
iff its GRANT survives. Every OLD Y label follows the exact
GrantDrainMarks Y-owner (stay, Y->X, or retire); labels at other
sites are unchanged. The physical transition does not read this ghost. -/
def sharedFullLabelNextHost {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring)
    (z : M.State) (host : Fin n → Option (Fin n))
    (e origin : Fin n) : Option (Fin n) :=
  if host origin = some e then
    if (M.view (M.step z e)).grant e = true then some e else none
  else if host origin = some (ring.rightNeighbor e) then
    (sharedFullLabelYSource M z e).map
      (fun keptAtY => if keptAtY then ring.rightNeighbor e else e)
  else host origin

/-- Each propagated label remains a genuine initial occupied
identity and sits on a live GRANT site. FIRE and final leader
sinks are already represented in the exact Y-source row. -/
private theorem sharedFullLabelNextHostSound {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring) (hn : 2 ≤ n)
    (start z : M.State) (host : Fin n → Option (Fin n))
    (hcover : SharedGrantFullLabelCover M start z host)
    (e origin site : Fin n)
    (hmove : sharedFullLabelNextHost M z host e origin =
      some site) :
    (M.view start).grant origin = true ∧
      (M.view (M.step z e)).grant site = true := by
  have hsource := sharedFullLabelStepSources M hn z e
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring hn e
  by_cases hx : host origin = some e
  · have hold := (hcover.1 origin e hx).1
    by_cases hnew : (M.view (M.step z e)).grant e = true
    · have hsite : site = e := by
        simpa [sharedFullLabelNextHost, hx, hnew] using hmove.symm
      subst site
      exact ⟨hold, hnew⟩
    · simp [sharedFullLabelNextHost, hx, hnew] at hmove
  · by_cases hy : host origin = some (ring.rightNeighbor e)
    · have hold := (hcover.1 origin (ring.rightNeighbor e) hy).1
      cases hsrc : sharedFullLabelYSource M z e with
      | none =>
          simp [sharedFullLabelNextHost, hx, hy, hsrc, hne] at hmove
      | some b =>
          cases b with
          | false =>
              have hsite : site = e := by
                simpa [sharedFullLabelNextHost, hx, hy, hsrc, hne]
                  using hmove.symm
              subst site
              exact ⟨hold, (hsource.2.1 hsrc).2⟩
          | true =>
              have hsite : site = ring.rightNeighbor e := by
                simpa [sharedFullLabelNextHost, hx, hy, hsrc, hne]
                  using hmove.symm
              subst site
              exact ⟨hold, (hsource.2.2 hsrc).2⟩
    · have hold : host origin = some site := by
        simpa [sharedFullLabelNextHost, hx, hy] using hmove
      have hnotX : site ≠ e := by
        intro h
        apply hx
        rw [h] at hold
        exact hold
      have hnotY : site ≠ ring.rightNeighbor e := by
        intro h
        apply hy
        rw [h] at hold
        exact hold
      have hframe :=
        sharedFullLabelAwayFrame M z e site hnotX hnotY
      exact ⟨(hcover.1 origin site hold).1,
        hframe.trans (hcover.1 origin site hold).2⟩

/-- Exact coverage, not merely the existing chosen-representative
injection: when Y coalesces with a surviving X grant, the old X
and OLD Y labels both survive at X. -/
private theorem sharedFullLabelNextHostCover {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring) (hn : 2 ≤ n)
    (start z : M.State) (host : Fin n → Option (Fin n))
    (hcover : SharedGrantFullLabelCover M start z host)
    (e : Fin n) :
    SharedGrantFullLabelCover M start (M.step z e)
      (sharedFullLabelNextHost M z host e) := by
  have hsource := sharedFullLabelStepSources M hn z e
  constructor
  · intro origin site hmove
    exact sharedFullLabelNextHostSound M hn start z host
      hcover e origin site hmove
  · intro site
    constructor
    · intro hnew
      by_cases hx : site = e
      · subst site
        rcases hsource.1.1 hnew with hgx | ⟨hgy, hsrc⟩
        · obtain ⟨origin, horigin⟩ := (hcover.2 e).mp hgx
          refine ⟨origin, ?_⟩
          simp [sharedFullLabelNextHost, horigin, hnew]
        · obtain ⟨origin, horigin⟩ :=
            (hcover.2 (ring.rightNeighbor e)).mp hgy
          have hne : ring.rightNeighbor e ≠ e :=
            EWord.rightNeighborDifferent ring hn e
          refine ⟨origin, ?_⟩
          simp [sharedFullLabelNextHost, horigin, hne, hsrc]
      · by_cases hy : site = ring.rightNeighbor e
        · subst site
          obtain ⟨hgy, hsrc⟩ := hsource.1.2 hnew
          obtain ⟨origin, horigin⟩ :=
            (hcover.2 (ring.rightNeighbor e)).mp hgy
          have hne : ring.rightNeighbor e ≠ e :=
            EWord.rightNeighborDifferent ring hn e
          refine ⟨origin, ?_⟩
          simp [sharedFullLabelNextHost, horigin, hne, hsrc]
        · have hframe :=
            sharedFullLabelAwayFrame M z e site hx hy
          have hold : (M.view z).grant site = true :=
            hframe.symm.trans hnew
          obtain ⟨origin, horigin⟩ := (hcover.2 site).mp hold
          refine ⟨origin, ?_⟩
          simp [sharedFullLabelNextHost, horigin, hx, hy]
    · intro h
      obtain ⟨origin, horigin⟩ := h
      exact (sharedFullLabelNextHostSound M hn start z host
        hcover e origin site horigin).2

/-- No reassignment in the forward direction; no label moves
except responder-to-source. The OUTSIDE/OLD-HOLD and FIRE
cases are all covered by the same exact local classifier. -/
private theorem sharedFullLabelNextHostMotion {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring)
    (z : M.State) (host : Fin n → Option (Fin n))
    (e origin oldSite newSite : Fin n)
    (hold : host origin = some oldSite)
    (hnew : sharedFullLabelNextHost M z host e origin =
      some newSite) :
    newSite = oldSite ∨
      (oldSite = ring.rightNeighbor e ∧ newSite = e) := by
  by_cases hx : oldSite = e
  · subst oldSite
    by_cases hg : (M.view (M.step z e)).grant e = true
    · have hsite : newSite = e := by
        simpa [sharedFullLabelNextHost, hold, hg] using hnew.symm
      exact Or.inl hsite
    · simp [sharedFullLabelNextHost, hold, hg] at hnew
  · by_cases hy : oldSite = ring.rightNeighbor e
    · subst oldSite
      cases hsrc : sharedFullLabelYSource M z e with
      | none =>
          simp [sharedFullLabelNextHost, hold, hx, hsrc] at hnew
      | some b =>
          cases b with
          | false =>
              have hsite : newSite = e := by
                simpa [sharedFullLabelNextHost, hold, hx, hsrc]
                  using hnew.symm
              exact Or.inr ⟨rfl, hsite⟩
          | true =>
              have hsite : newSite = ring.rightNeighbor e := by
                simpa [sharedFullLabelNextHost, hold, hx, hsrc]
                  using hnew.symm
              exact Or.inl hsite
    · have hsite : newSite = oldSite := by
        simpa [sharedFullLabelNextHost, hold, hx, hy]
          using hnew.symm
      exact Or.inl hsite

/-- The statement already defined in GrantDrainShared is TRUE.
This proves it for every GrantDrainModel with an exact source
step, not just the canonical model. In particular the proof-only
full sets survive collision by union, and the leader sink retires
all labels of a sunk physical host. -/
theorem sharedGrantFullLabelTransportGeneral {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring) (hn : 2 ≤ n) :
    SharedGrantFullLabelTransport M := by
  intro start current host hcover e
  refine ⟨sharedFullLabelNextHost M current host e, ?_, ?_, ?_⟩
  · exact sharedFullLabelNextHostCover M hn start current host
      hcover e
  · intro origin hnone
    simp [sharedFullLabelNextHost, hnone]
  · intro origin oldSite newSite hold hnew
    exact sharedFullLabelNextHostMotion M current host e
      origin oldSite newSite hold hnew

/-- Requested specialization. The canonical model already
discharges its birth payer (sharedSourceFireSpends) and
leader-death frame (sharedSourceLeaderDeathFromE) via the model
constructor. Here only stepExact and the literal token cases
are needed for immutable GRANT labels. -/
theorem sharedGrantCanonicalFullLabelTransport {n : Nat}
    {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    SharedGrantFullLabelTransport
      (grantDrainCanonicalModel ring hn fresh update) := by
  exact sharedGrantFullLabelTransportGeneral
    (grantDrainCanonicalModel ring hn fresh update)
    (by omega : 2 ≤ n)

end L3.GrantDrainShared

namespace L3.GrantDrainShared

open L3.GrantDrainEntrance
open L3.RenewalReferenceClock

set_option autoImplicit false
set_option Elab.async false

/-!
The installed ancestry Prop uses the old
BankGrantNonleftmostLive observer, which counts only a preceding
FOLLOWER LIVE. This is strictly narrower than
SharedPaperNonleftmostLiveExact, which counts the preceding
leader-hosted bullet as the paper does. The former is not
backward-ancestry closed, even on a protected five-site cut.

We first give the faithful source ghost and a positive, corrected
paper-exact ancestry theorem. We then exhibit the literal cut
refuting the older Prop for EVERY ghost, including this one.
No artificial proof of the false old Prop is attempted.
-/

/-- Immutable full GRANT origins transported by the exact source
row, including both old identities when two grants coalesce. -/
def sharedGrantFullLabelWordStep {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring)
    (z : M.State × (Fin n → Option (Fin n)))
    (e : Fin n) : M.State × (Fin n → Option (Fin n)) :=
  (M.step z.1 e, sharedFullLabelNextHost M z.1 z.2 e)

def sharedGrantFullLabelWordRun {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring)
    (start : M.State) (word : List (Fin n)) :
    M.State × (Fin n → Option (Fin n)) :=
  word.foldl (sharedGrantFullLabelWordStep M)
    (start, fun i =>
      if (M.view start).grant i then some i else none)

private theorem sharedGrantFullLabelInitialCover {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring) (start : M.State) :
    SharedGrantFullLabelCover M start start
      (fun i => if (M.view start).grant i then some i else none) := by
  constructor
  · intro origin site h
    cases hg : (M.view start).grant origin with
    | false =>
        simp [hg] at h
    | true =>
        have he : origin = site := by
          simpa [hg] using h
        subst site
        exact ⟨by simp [hg], by simp [hg]⟩
  · intro site
    constructor
    · intro hg
      refine ⟨site, ?_⟩
      simp [hg]
    · rintro ⟨origin, h⟩
      cases hg : (M.view start).grant origin with
      | false =>
          simp [hg] at h
      | true =>
          have he : origin = site := by
            simpa [hg] using h
          rw [← he]
          exact hg

/-- Step-3 full-label transport is iterated on the SAME IID word,
rather than on the chosen-representative injection. -/
theorem sharedGrantFullLabelWordRunCover {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring) (hn : 2 ≤ n)
    (start : M.State) (word : List (Fin n)) :
    SharedGrantFullLabelCover M start
      (sharedGrantFullLabelWordRun M start word).1
      (sharedGrantFullLabelWordRun M start word).2 := by
  have hfold :
      ∀ (w : List (Fin n))
        (z : M.State × (Fin n → Option (Fin n))),
        SharedGrantFullLabelCover M start z.1 z.2 →
        SharedGrantFullLabelCover M start
          (w.foldl (sharedGrantFullLabelWordStep M) z).1
          (w.foldl (sharedGrantFullLabelWordStep M) z).2 := by
    intro w
    induction w with
    | nil =>
        intro z hz
        exact hz
    | cons e rest ih =>
        intro z hz
        exact ih (sharedGrantFullLabelWordStep M z e)
          (sharedFullLabelNextHostCover M hn
            start z.1 z.2 hz e)
  unfold sharedGrantFullLabelWordRun
  exact hfold word _ (sharedGrantFullLabelInitialCover M start)

/-- The full GRANT-label run does not change physical dynamics. -/
theorem sharedGrantFullLabelWordRunPhysical {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring)
    (start : M.State) (word : List (Fin n)) :
    (sharedGrantFullLabelWordRun M start word).1 =
      sharedGrantPhysicalRun M start word := by
  have hfold :
      ∀ (w : List (Fin n))
        (z : M.State × (Fin n → Option (Fin n))),
        (w.foldl (sharedGrantFullLabelWordStep M) z).1 =
          w.foldl M.step z.1 := by
    intro w
    induction w with
    | nil =>
        intro z
        rfl
    | cons e rest ih =>
        intro z
        exact ih (sharedGrantFullLabelWordStep M z e)
  unfold sharedGrantFullLabelWordRun sharedGrantPhysicalRun
  exact hfold word _

/-- Concrete crossing ghost on the canonical source:
* bullet identities: paper-EXACT entrance bullet ghosts;
* grant identities: immutable full label sets of step 3;
* permanent marks: the actual ordered source-ledger marks.

All three projections read the same already-revealed edge prefix,
passed in reverse order. No future scheduler choices are read. -/
noncomputable def sharedGrantFaithfulGhost {n : Nat}
    {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (start : GrantDrainState n Scratch) :
    SharedGrantCrossingGhost n :=
  { bulletHost := fun id past =>
      (grantDrainEntranceRun ring fresh update
        (grantDrainEntranceInitial ring start)
        past.reverse).bulletHosts id
    grantHost := fun id past =>
      (sharedGrantFullLabelWordRun
        (grantDrainCanonicalModel ring hn fresh update)
        start past.reverse).2 id
    everMarked := fun id past =>
      match ((grantDrainEntranceRun ring fresh update
        (grantDrainEntranceInitial ring start)
        past.reverse).grantLabels id).mark with
      | .unmarked => false
      | _ => true }

/-- The GRANT-host projection of the faithful ghost has the complete
physical label cover, including two origins sharing one coalesced host.
This does not yet identify the separate ledger marks with those hosts. -/
theorem sharedGrantFaithfulGhostGrantCover {n : Nat}
    {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (start : GrantDrainState n Scratch)
    (word : List (Fin n)) :
    SharedGrantFullLabelCover
      (grantDrainCanonicalModel ring hn fresh update) start
      (sharedGrantPhysicalRun
        (grantDrainCanonicalModel ring hn fresh update)
        start word)
      (fun id =>
        (sharedGrantFaithfulGhost ring hn fresh update start).grantHost
          id word.reverse) := by
  have hcover := sharedGrantFullLabelWordRunCover
    (grantDrainCanonicalModel ring hn fresh update)
    (by omega : 2 ≤ n) start word
  have hphysical := sharedGrantFullLabelWordRunPhysical
    (grantDrainCanonicalModel ring hn fresh update) start word
  change SharedGrantFullLabelCover
    (grantDrainCanonicalModel ring hn fresh update) start
    (sharedGrantPhysicalRun
      (grantDrainCanonicalModel ring hn fresh update)
      start word)
    (sharedGrantFullLabelWordRun
      (grantDrainCanonicalModel ring hn fresh update)
      start (word.reverse).reverse).2
  simp only [List.reverse_reverse]
  rw [← hphysical]
  exact hcover

/-- The valid BAD(ii) ancestry statement uses the paper-exact
observer. It follows from the canonical source one-edge
origin theorem already incorporated in grantDrainEntranceFaithfulRun.
Every surviving paper-bad LIVE has an INITIAL paper-bad identity;
no ghost ID is fabricated. -/
theorem sharedGrantFaithfulPaperBadLiveAncestry {n : Nat}
    {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (start : GrantDrainState n Scratch)
    (hPB : PPlus ring start.native)
    (word : List (Fin n)) (b : Fin n)
    (hBad : SharedPaperNonleftmostLiveExact ring
      (sharedGrantPhysicalRun
        (grantDrainCanonicalModel ring hn fresh update)
        start word).native b) :
    ∃ id : Fin n,
      SharedPaperNonleftmostLiveExact ring start.native id ∧
      (sharedGrantFaithfulGhost ring hn fresh update start).bulletHost
        id word.reverse = some b := by
  classical
  have hFaith :=
    grantDrainEntranceInitialFaithfulRun
      ring hn fresh update start word hPB
  have hPhysical :
      (grantDrainEntranceRun ring fresh update
        (grantDrainEntranceInitial ring start) word).physical =
      sharedGrantPhysicalRun
        (grantDrainCanonicalModel ring hn fresh update)
        start word := by
    exact grantDrainEntrancePhysicalWordProjection
      ring fresh update word (grantDrainEntranceInitial ring start)
  have hPost : SharedPaperNonleftmostLiveExact ring
      (grantDrainEntranceRun ring fresh update
        (grantDrainEntranceInitial ring start) word).physical.native b := by
    rw [hPhysical]
    exact hBad
  obtain ⟨id, hHost⟩ := hFaith.2 b hPost
  have hInitNonempty :
      (grantDrainEntranceInitial ring start).bulletHosts id ≠ none := by
    intro hEmpty
    have hRetired := grantDrainEntranceBulletRetiredRun
      ring fresh update word (grantDrainEntranceInitial ring start)
      id hEmpty
    rw [hRetired] at hHost
    cases hHost
  have hOld : SharedPaperNonleftmostLiveExact ring
      start.native id := by
    by_cases h : SharedPaperNonleftmostLiveExact ring start.native id
    · exact h
    · have hEmpty :
          (grantDrainEntranceInitial ring start).bulletHosts id =
            none := by
        change grantDrainEntranceBulletInitial ring start id = none
        simp [grantDrainEntranceBulletInitial, h]
      exact False.elim (hInitNonempty hEmpty)
  refine ⟨id, hOld, ?_⟩
  change
    (grantDrainEntranceRun ring fresh update
      (grantDrainEntranceInitial ring start)
      (word.reverse).reverse).bulletHosts id = some b
  simpa only [List.reverse_reverse] using hHost

/-! A five-site protected literal refuter of the OLD Bank observer.
Root 0 carries a shielded LIVE, follower 2 carries another LIVE,
and every other site is native-empty. Both grants and requests are
false. On service 0->1 the root's LIVE moves to follower 1 while
LIVE at 2 stays put. Initially there is NO preceding follower LIVE
for any site; after the service follower 2 has preceding follower
LIVE at 1. Exact paper BAD(ii) was already true at 2 at the cut.
This is an observer failure, not a new physical bad bullet. -/

private def sharedGrantBankRootLiveRing : DirectedRing 5 :=
  ⟨by decide⟩

private def sharedGrantBankRootLiveNative (i : Fin 5) : CertNative :=
  if i.val == 0 then
    { l := true, b := (2 : Fin 3), sh := true, sg := false }
  else if i.val == 2 then
    { l := false, b := (2 : Fin 3), sh := false, sg := false }
  else
    { l := false, b := (0 : Fin 3), sh := false, sg := false }

private def sharedGrantBankRootLiveStart : GrantDrainState 5 Unit :=
  { native := sharedGrantBankRootLiveNative
    request := fun _ => false
    grant := fun _ => false
    scratch := ()
    history := [] }

private def sharedGrantBankRootLiveAfter : GrantDrainState 5 Unit :=
  grantDrainStep sharedGrantBankRootLiveRing
    (fun _ _ => false) (fun _ _ => ())
    sharedGrantBankRootLiveStart (0 : Fin 5)

/-- The counterexample already belongs to the protected PPlus class. -/
theorem sharedGrantBankRootLiveProtected :
    PPlus sharedGrantBankRootLiveRing
      sharedGrantBankRootLiveStart.native := by
  unfold PPlus P PeacefulBullet LiveBullet
    sharedGrantBankRootLiveRing sharedGrantBankRootLiveStart
    sharedGrantBankRootLiveNative
  decide +kernel

/-- No OLD BankGrantNonleftmostLive identity exists at any site. -/
theorem sharedGrantBankRootLiveInitialEmpty :
    ∀ id : Fin 5,
      ¬ BankGrantNonleftmostLive sharedGrantBankRootLiveRing
          sharedGrantBankRootLiveStart.native id := by
  unfold BankGrantNonleftmostLive LiveBullet leaderSector
    sharedGrantBankRootLiveRing sharedGrantBankRootLiveStart
    sharedGrantBankRootLiveNative
  decide +kernel

/-- After ONE original physical edge, site 2 is Bank-bad,
because the earlier LIVE is now on follower 1 rather than root 0. -/
theorem sharedGrantBankRootLiveAfterBad :
    BankGrantNonleftmostLive sharedGrantBankRootLiveRing
      sharedGrantBankRootLiveAfter.native (2 : Fin 5) := by
  unfold BankGrantNonleftmostLive LiveBullet leaderSector
    sharedGrantBankRootLiveRing sharedGrantBankRootLiveAfter
    sharedGrantBankRootLiveStart sharedGrantBankRootLiveNative
  decide +kernel

/-- Strong negative result: not even a perfectly faithful ghost
could make the ORIGINAL SharedGrantBadLiveAncestryComplete true.
It demands an initially Bank-bad ID where no such ID exists. -/
theorem sharedGrantBankAncestryRefutedForEveryGhost :
    ∀ ghost : SharedGrantCrossingGhost 5,
      ¬ SharedGrantBadLiveAncestryComplete
        (grantDrainCanonicalModel sharedGrantBankRootLiveRing
          (by decide : 5 ≤ 5)
          (fun _ _ => false) (fun _ _ => ()))
        sharedGrantBankRootLiveStart ghost := by
  intro ghost h
  have hNew :
      BankGrantNonleftmostLive sharedGrantBankRootLiveRing
        ((grantDrainCanonicalModel sharedGrantBankRootLiveRing
          (by decide : 5 ≤ 5)
          (fun _ _ => false) (fun _ _ => ())).view
          (sharedGrantPhysicalRun
            (grantDrainCanonicalModel sharedGrantBankRootLiveRing
              (by decide : 5 ≤ 5)
              (fun _ _ => false) (fun _ _ => ()))
            sharedGrantBankRootLiveStart [(0 : Fin 5)])).native
        (2 : Fin 5) := by
    change BankGrantNonleftmostLive sharedGrantBankRootLiveRing
      sharedGrantBankRootLiveAfter.native (2 : Fin 5)
    exact sharedGrantBankRootLiveAfterBad
  obtain ⟨id, hOld, _⟩ :=
    h [(0 : Fin 5)] (2 : Fin 5) hNew
  exact (sharedGrantBankRootLiveInitialEmpty id) hOld

end L3.GrantDrainShared

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-!
Answer for R8 step 5.
The first two lemmas give the literal unshielded quiet-source
death row. The all-FIRE lemma treats the actual canonical native
successor: the old source is either a follower with zero signal
or is overwritten by a protected, signal-zero birth.

The five-site regression then exhibits a genuine PPlus weak label
whose source dies and whose persistent label becomes strong.
It is not a proof of universal GrantDrainLedgerNoExhaustion.
-/

/-- A LIVE initiator kills a quiet unshielded leader responder in
the literal E row. The responder's shield and signal stay zero;
the initiator's bullet is consumed. No sector assumption is used. -/
theorem grantDrainWeakSourceQuietDeathPair
    (x y : CertNative)
    (hLive : x.b = (2 : Fin 3))
    (hLeader : y.l = true)
    (hUnshielded : y.sh = false)
    (hQuiet : y.sg = false) :
    (certLiteralEPair x y).1.b = (0 : Fin 3) ∧
    (certLiteralEPair x y).2.l = false ∧
    (certLiteralEPair x y).2.sh = false ∧
    (certLiteralEPair x y).2.sg = false := by
  rcases x with ⟨xl, xb, xsh, xs⟩
  rcases y with ⟨yl, yb, ysh, ys⟩
  change xb = (2 : Fin 3) at hLive
  change yl = true at hLeader
  change ysh = false at hUnshielded
  change ys = false at hQuiet
  subst xb
  subst yl
  subst ysh
  subst ys
  cases xl <;> cases xs <;>
    simp [certLiteralEPair, certFinThree]

/-- The same exact death row at the two actual nativeE sites. -/
theorem grantDrainWeakSourceQuietDeathNativeE
    {n : Nat} (hn : 3 ≤ n)
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (e : Fin n)
    (hLive : (N e).b = (2 : Fin 3))
    (hLeader : (N (ring.rightNeighbor e)).l = true)
    (hUnshielded : (N (ring.rightNeighbor e)).sh = false)
    (hQuiet : (N (ring.rightNeighbor e)).sg = false) :
    (nativeE ring N e e).b = (0 : Fin 3) ∧
    (nativeE ring N e (ring.rightNeighbor e)).l = false ∧
    (nativeE ring N e (ring.rightNeighbor e)).sh = false ∧
    (nativeE ring N e (ring.rightNeighbor e)).sg = false := by
  have hDistinct := grantDrainMarksNeighborDistinct hn ring e
  have hPair := grantDrainWeakSourceQuietDeathPair
    (N e) (N (ring.rightNeighbor e))
    hLive hLeader hUnshielded hQuiet
  simpa [nativeE, hDistinct] using hPair

/-- Full actual post-E/post-FIRE death endpoint case split.
An F1 overwrite at the victim creates a protected leader; every
other FIRE selector leaves the killed victim a signal-zero follower.
This is the endpoint row, not the still-missing global zero-trail
concatenation from the killer's peaceful preceding leader to g. -/
theorem grantDrainWeakSourceQuietDeathAllFire
    {n : Nat} {Scratch : Type}
    (hn : 3 ≤ n)
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hLive : (s.native e).b = (2 : Fin 3))
    (hLeader : (s.native (ring.rightNeighbor e)).l = true)
    (hUnshielded : (s.native (ring.rightNeighbor e)).sh = false)
    (hQuiet : (s.native (ring.rightNeighbor e)).sg = false) :
    ((grantDrainNativeNext ring s e (ring.rightNeighbor e)).l = false ∧
      (grantDrainNativeNext ring s e (ring.rightNeighbor e)).sh = false ∧
      (grantDrainNativeNext ring s e (ring.rightNeighbor e)).sg = false) ∨
    ((grantDrainNativeNext ring s e (ring.rightNeighbor e)).l = true ∧
      (grantDrainNativeNext ring s e (ring.rightNeighbor e)).sh = true ∧
      (grantDrainNativeNext ring s e (ring.rightNeighbor e)).sg = false) := by
  have hE := (grantDrainWeakSourceQuietDeathNativeE
    hn ring s.native e hLive hLeader hUnshielded hQuiet).2
  have hDistinct := grantDrainMarksNeighborDistinct hn ring e
  cases hf : grantDrainSelect ring s e with
  | none =>
      left
      simpa [grantDrainNativeNext, hf] using hE
  | leftLocal =>
      left
      simpa [grantDrainNativeNext, hf, canonicalBirth, hDistinct] using hE
  | rightLocal =>
      right
      simp [grantDrainNativeNext, hf, canonicalBirth, firedNative]
  | cross =>
      left
      simpa [grantDrainNativeNext, hf, canonicalBirth, hDistinct] using hE

/-- The all-FIRE row is about grantDrainStep itself, not a surrogate
native model. Fresh requests and scratch updates are unrestricted. -/
theorem grantDrainWeakSourceQuietDeathActualStep
    {n : Nat} {Scratch : Type}
    (hn : 3 ≤ n)
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hLive : (s.native e).b = (2 : Fin 3))
    (hLeader : (s.native (ring.rightNeighbor e)).l = true)
    (hUnshielded : (s.native (ring.rightNeighbor e)).sh = false)
    (hQuiet : (s.native (ring.rightNeighbor e)).sg = false) :
    (((grantDrainStep ring fresh update s e).native
        (ring.rightNeighbor e)).l = false ∧
      ((grantDrainStep ring fresh update s e).native
        (ring.rightNeighbor e)).sh = false ∧
      ((grantDrainStep ring fresh update s e).native
        (ring.rightNeighbor e)).sg = false) ∨
    (((grantDrainStep ring fresh update s e).native
        (ring.rightNeighbor e)).l = true ∧
      ((grantDrainStep ring fresh update s e).native
        (ring.rightNeighbor e)).sh = true ∧
      ((grantDrainStep ring fresh update s e).native
        (ring.rightNeighbor e)).sg = false) := by
  exact grantDrainWeakSourceQuietDeathAllFire
    hn ring s e hLive hLeader hUnshielded hQuiet

/-!
Exact five-site death-to-strong regression:
  initial leaders: 0 (shielded), 3 (quiet and unshielded);
  initial LIVE: 2, peaceful behind protected source 0;
  initial grant: 4, no requests; edge: 2 -> 3.
Initially the grant at 4 is weakly locked behind source 3.
The LIVE at 2 kills leader 3, and the remaining protected
source 0 supplies a strong zero corridor to the same grant at 4.
No selected FIRE or grant motion is needed on this edge.
-/

def grantDrainWeakDeathFiveRing : DirectedRing 5 :=
  ⟨by decide⟩

def grantDrainWeakDeathFiveNative (i : Fin 5) : CertNative :=
  if i.val == 0 then
    { l := true, b := (0 : Fin 3), sh := true, sg := false }
  else if i.val == 2 then
    { l := false, b := (2 : Fin 3), sh := false, sg := false }
  else if i.val == 3 then
    { l := true, b := (0 : Fin 3), sh := false, sg := false }
  else
    { l := false, b := (0 : Fin 3), sh := false, sg := false }

def grantDrainWeakDeathFiveStart : GrantDrainState 5 Unit :=
  { native := grantDrainWeakDeathFiveNative
    request := fun _ => false
    grant := fun i => i.val == 4
    scratch := ()
    history := [] }

def grantDrainWeakDeathFiveFresh :
    GrantDrainState 5 Unit → Fin 5 → Bool :=
  fun _ _ => false

def grantDrainWeakDeathFiveScratch :
    GrantDrainState 5 Unit → Fin 5 → Unit :=
  fun _ _ => ()

def grantDrainWeakDeathFiveLabel : GrantDrainLedgerLabel 5 :=
  grantDrainLedgerInitial grantDrainWeakDeathFiveRing
    grantDrainWeakDeathFiveStart (4 : Fin 5)

def grantDrainWeakDeathFiveNext : GrantDrainState 5 Unit :=
  grantDrainStep grantDrainWeakDeathFiveRing
    grantDrainWeakDeathFiveFresh grantDrainWeakDeathFiveScratch
    grantDrainWeakDeathFiveStart (2 : Fin 5)

def grantDrainWeakDeathFiveLabelNext : GrantDrainLedgerLabel 5 :=
  grantDrainLedgerStep grantDrainWeakDeathFiveRing
    grantDrainWeakDeathFiveFresh grantDrainWeakDeathFiveScratch
    grantDrainWeakDeathFiveStart (2 : Fin 5)
    grantDrainWeakDeathFiveLabel

/-- The initial LIVE at 2 is genuinely peaceful: its nearest source
is the shielded leader 0 with zero signal through the bullet. -/
theorem grantDrainWeakDeathFivePPlus :
    PPlus grantDrainWeakDeathFiveRing
      grantDrainWeakDeathFiveStart.native := by
  unfold PPlus P PeacefulBullet LiveBullet
    grantDrainWeakDeathFiveRing grantDrainWeakDeathFiveStart
    grantDrainWeakDeathFiveNative
  decide +kernel

/-- Initial identity 4 is weak, hosted and budgeted for 2n=10 hits. -/
theorem grantDrainWeakDeathFiveSeed :
    grantDrainWeakDeathFiveLabel.host = some (4 : Fin 5) ∧
    grantDrainWeakDeathFiveLabel.mark = .weak ∧
    grantDrainWeakDeathFiveLabel.remaining = 10 := by
  unfold grantDrainWeakDeathFiveLabel grantDrainLedgerInitial
  decide +kernel

/-- This is an actual native death edge; site 3 is not merely
hypothesized dead. The OLD LIVE is at site 2. -/
theorem grantDrainWeakDeathFiveDeathEdge :
    (grantDrainWeakDeathFiveStart.native (2 : Fin 5)).b =
      (2 : Fin 3) ∧
    (grantDrainWeakDeathFiveStart.native (3 : Fin 5)).l = true ∧
    (grantDrainWeakDeathFiveStart.native (3 : Fin 5)).sh = false ∧
    (grantDrainWeakDeathFiveStart.native (3 : Fin 5)).sg = false ∧
    (grantDrainWeakDeathFiveNext.native (3 : Fin 5)).l = false ∧
    (grantDrainWeakDeathFiveNext.native (3 : Fin 5)).sh = false ∧
    (grantDrainWeakDeathFiveNext.native (3 : Fin 5)).sg = false := by
  unfold grantDrainWeakDeathFiveNext grantDrainStep
  decide +kernel

/-- The moving ghost is not recreated: host 4 persists, weak promotes
to strong, and the new remaining quota is capped at n=5.
The literal new corridor has a protected source 0. -/
theorem grantDrainWeakDeathFiveStrongRow :
    grantDrainWeakDeathFiveLabelNext.host = some (4 : Fin 5) ∧
    grantDrainWeakDeathFiveLabelNext.mark = .strong ∧
    grantDrainWeakDeathFiveLabelNext.remaining = 5 ∧
    grantDrainLedgerStrongLock grantDrainWeakDeathFiveRing
      grantDrainWeakDeathFiveNext (4 : Fin 5) = true := by
  unfold grantDrainWeakDeathFiveLabelNext grantDrainLedgerStep
  decide +kernel

/-- The newly protected source is four positions behind the host. -/
theorem grantDrainWeakDeathFiveDistance :
    grantDrainStrongProtectedDistance grantDrainWeakDeathFiveRing
      grantDrainWeakDeathFiveNext (some (4 : Fin 5)) = 4 := by
  unfold grantDrainStrongProtectedDistance
  decide +kernel

theorem grantDrainWeakDeathFiveStrongPhysical :
    GrantDrainStrongPhysical grantDrainWeakDeathFiveRing
      grantDrainWeakDeathFiveNext grantDrainWeakDeathFiveLabelNext := by
  unfold GrantDrainStrongPhysical
  refine ⟨(4 : Fin 5), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact grantDrainWeakDeathFiveStrongRow.1
  · exact grantDrainWeakDeathFiveStrongRow.2.1
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact grantDrainWeakDeathFiveStrongRow.2.2.2

theorem grantDrainWeakDeathFiveBudget :
    grantDrainStrongProtectedDistance grantDrainWeakDeathFiveRing
      grantDrainWeakDeathFiveNext
      grantDrainWeakDeathFiveLabelNext.host ≤
    grantDrainWeakDeathFiveLabelNext.remaining := by
  rw [grantDrainWeakDeathFiveStrongRow.1,
    grantDrainWeakDeathFiveDistance,
    grantDrainWeakDeathFiveStrongRow.2.2.1]
  decide

theorem grantDrainWeakDeathFivePPlusAfter :
    PPlus grantDrainWeakDeathFiveRing
      grantDrainWeakDeathFiveNext.native := by
  exact grantDrainStep_preserves_PPlus
    (by decide : 3 ≤ 5)
    grantDrainWeakDeathFiveRing
    grantDrainWeakDeathFiveFresh
    grantDrainWeakDeathFiveScratch
    grantDrainWeakDeathFiveStart (2 : Fin 5)
    grantDrainWeakDeathFivePPlus

/-- The exhibited edge is in the canonical source model itself. -/
theorem grantDrainWeakDeathFiveCanonicalEdge :
    ((GrantDrainShared.grantDrainCanonicalModel
      grantDrainWeakDeathFiveRing (by decide : 5 ≤ 5)
      grantDrainWeakDeathFiveFresh
      grantDrainWeakDeathFiveScratch).step
      grantDrainWeakDeathFiveStart (2 : Fin 5)) =
        grantDrainWeakDeathFiveNext := by
  rfl

/-- Exact one-letter ghost/source word; no replacement transition. -/
theorem grantDrainWeakDeathFiveWord :
    grantDrainLedgerRun grantDrainWeakDeathFiveRing
      grantDrainWeakDeathFiveFresh grantDrainWeakDeathFiveScratch
      grantDrainWeakDeathFiveStart grantDrainWeakDeathFiveLabel
      [(2 : Fin 5)] =
    (grantDrainWeakDeathFiveNext, grantDrainWeakDeathFiveLabelNext) := by
  rfl

theorem grantDrainWeakDeathFiveFirstWordNonexhausted :
    0 <
      (grantDrainLedgerRun grantDrainWeakDeathFiveRing
        grantDrainWeakDeathFiveFresh grantDrainWeakDeathFiveScratch
        grantDrainWeakDeathFiveStart grantDrainWeakDeathFiveLabel
        [(2 : Fin 5)]).2.remaining := by
  rw [grantDrainWeakDeathFiveWord,
    grantDrainWeakDeathFiveStrongRow.2.2.1]
  decide

/-- The all-edge strong geometry now applies to every further
scheduler word from this ACTUAL weak-to-strong death cut. This result
covers continuing strong identities, not yet terminal/weak histories
of the universal NoExhaustion assertion. -/
theorem grantDrainWeakDeathFiveStrongContinuation
    (edges : List (Fin 5))
    (hStrong :
      (grantDrainLedgerRun grantDrainWeakDeathFiveRing
        grantDrainWeakDeathFiveFresh grantDrainWeakDeathFiveScratch
        grantDrainWeakDeathFiveNext grantDrainWeakDeathFiveLabelNext
        edges).2.mark = .strong)
    (hLive :
      (grantDrainLedgerRun grantDrainWeakDeathFiveRing
        grantDrainWeakDeathFiveFresh grantDrainWeakDeathFiveScratch
        grantDrainWeakDeathFiveNext grantDrainWeakDeathFiveLabelNext
        edges).2.host ≠ none) :
    0 <
      (grantDrainLedgerRun grantDrainWeakDeathFiveRing
        grantDrainWeakDeathFiveFresh grantDrainWeakDeathFiveScratch
        grantDrainWeakDeathFiveNext grantDrainWeakDeathFiveLabelNext
        edges).2.remaining := by
  have hGeometry :
      GrantDrainStrongCorridorGeometry
        grantDrainWeakDeathFiveRing
        grantDrainWeakDeathFiveFresh
        grantDrainWeakDeathFiveScratch :=
    grantDrainStrongCorridorGeometry_of_arc_coverage
      grantDrainWeakDeathFiveRing
      grantDrainWeakDeathFiveFresh grantDrainWeakDeathFiveScratch
      (grantDrainMarksStrongArcCoverageOfThree
        (by decide : 3 ≤ 5)
        grantDrainWeakDeathFiveRing
        grantDrainWeakDeathFiveFresh grantDrainWeakDeathFiveScratch)
      (grantDrainMarksStrongPhysicalClosureOfThree
        (by decide : 3 ≤ 5)
        grantDrainWeakDeathFiveRing
        grantDrainWeakDeathFiveFresh grantDrainWeakDeathFiveScratch)
  exact grantDrainStrongNoExhaustionOfGeometry
    (by decide : 3 ≤ 5)
    grantDrainWeakDeathFiveRing
    grantDrainWeakDeathFiveFresh grantDrainWeakDeathFiveScratch
    hGeometry grantDrainWeakDeathFiveNext
    grantDrainWeakDeathFiveLabelNext
    grantDrainWeakDeathFivePPlusAfter
    grantDrainWeakDeathFiveStrongPhysical
    grantDrainWeakDeathFiveBudget
    edges hStrong hLive

end L3

namespace L3.GrantDrainShared

open L3.GrantDrainEntrance
open L3.RenewalReferenceClock

set_option autoImplicit false
set_option Elab.async false

/-! The full-set grant host and promoted source ledger
have the same OLD-token parent. They must be identified before
the native/grant separation clock can be used. -/

/-- A single full-set origin has exactly the same next physical
host as its source ledger label, provided its current host really
carries an OLD grant. The condition is essential at source X:
the ledger checks OLD G_X, whereas the full-label update checks
the NEW G_X. -/
private theorem sharedCrossingFullHostStepEq
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (hosts : Fin n → Option (Fin n))
    (hvalid : ∀ id g, hosts id = some g → s.grant g = true)
    (e id : Fin n) :
    sharedFullLabelNextHost
      (grantDrainCanonicalModel ring hn fresh update)
      s hosts e id =
      grantDrainLedgerHost ring fresh s e (hosts id) := by
  cases hh : hosts id with
  | none =>
      simp [sharedFullLabelNextHost, grantDrainLedgerHost, hh]
  | some g =>
      by_cases hx : g = e
      · subst g
        have hg : s.grant e = true := hvalid id e hh
        have hrow :
            (grantDrainStep ring fresh update s e).grant e =
              (grantDrainLedgerRow ring fresh s e).1.grant := by
          exact (sharedFullLabelStepSlots
            (grantDrainCanonicalModel ring hn fresh update)
            (by omega : 2 ≤ n) s e).1
        simp [sharedFullLabelNextHost, grantDrainLedgerHost,
          hh, hg, hrow]
        change
          (if (grantDrainStep ring fresh update s e).grant e = true
            then some e else none) =
          (if (grantDrainLedgerRow ring fresh s e).1.grant = true
            then some e else none)
        rw [hrow]
      · by_cases hy : g = ring.rightNeighbor e
        · subst g
          have hne : ring.rightNeighbor e ≠ e :=
            EWord.rightNeighborDifferent ring
              (by omega : 2 ≤ n) e
          simp [sharedFullLabelNextHost, grantDrainLedgerHost,
            hh, hne, sharedFullLabelYSource,
            sharedFullLabelRow, grantDrainLedgerRow]
          change
            Option.map (fun keptAtY : Bool =>
              if keptAtY then ring.rightNeighbor e else e)
              (grantDrainLedgerYSource
                (s.request (ring.rightNeighbor e))
                (s.grant (ring.rightNeighbor e))
                (grantDrainNativeNext ring s e e).l
                (grantDrainNativeNext ring s e
                  (ring.rightNeighbor e)).l
                (grantDrainSelect ring s e)
                (grantDrainLedgerRow ring fresh s e)) =
              match grantDrainLedgerYSource
                (s.request (ring.rightNeighbor e))
                (s.grant (ring.rightNeighbor e))
                (grantDrainNativeNext ring s e e).l
                (grantDrainNativeNext ring s e
                  (ring.rightNeighbor e)).l
                (grantDrainSelect ring s e)
                (grantDrainLedgerRow ring fresh s e) with
              | some true => some (ring.rightNeighbor e)
              | some false => some e
              | none => none
          cases hY : grantDrainLedgerYSource
              (s.request (ring.rightNeighbor e))
              (s.grant (ring.rightNeighbor e))
              (grantDrainNativeNext ring s e e).l
              (grantDrainNativeNext ring s e
                (ring.rightNeighbor e)).l
              (grantDrainSelect ring s e)
              (grantDrainLedgerRow ring fresh s e) with
          | none => simp [hY]
          | some stays =>
              cases stays <;> simp [hY]
        · simp [sharedFullLabelNextHost, grantDrainLedgerHost,
            hh, hx, hy]

/-- General fold alignment, retaining the full GrantDrainFullLabelCover
to justify the OLD occupied-source test at every adapted edge. -/
private theorem sharedCrossingAlignedFold
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (start : GrantDrainState n Scratch) :
    ∀ (word : List (Fin n))
      (state : GrantDrainEntranceState n Scratch)
      (hosts : Fin n → Option (Fin n)),
      SharedGrantFullLabelCover
        (grantDrainCanonicalModel ring hn fresh update)
        start state.physical hosts →
      (∀ id, hosts id = (state.grantLabels id).host) →
      ∀ id,
        (word.foldl
          (sharedGrantFullLabelWordStep
            (grantDrainCanonicalModel ring hn fresh update))
          (state.physical, hosts)).2 id =
        ((word.foldl (grantDrainEntranceNext ring fresh update)
          state).grantLabels id).host := by
  intro word
  induction word with
  | nil =>
      intro state hosts _ halign id
      exact halign id
  | cons e rest ih =>
      intro state hosts hcover halign id
      have hvalid : ∀ origin g,
          hosts origin = some g →
            state.physical.grant g = true := by
        intro origin g h
        exact (hcover.1 origin g h).2
      have hnextAlign :
          ∀ origin,
            sharedFullLabelNextHost
              (grantDrainCanonicalModel ring hn fresh update)
              state.physical hosts e origin =
            ((grantDrainEntranceNext ring fresh update state e).grantLabels
              origin).host := by
        intro origin
        calc
          sharedFullLabelNextHost
              (grantDrainCanonicalModel ring hn fresh update)
              state.physical hosts e origin =
            grantDrainLedgerHost ring fresh state.physical e
              (hosts origin) :=
              sharedCrossingFullHostStepEq
                ring hn fresh update state.physical hosts
                hvalid e origin
          _ = grantDrainLedgerHost ring fresh state.physical e
                (state.grantLabels origin).host := by
                  rw [halign origin]
          _ = ((grantDrainEntranceNext ring fresh update state e).grantLabels
                origin).host := rfl
      have hnextCover :
          SharedGrantFullLabelCover
            (grantDrainCanonicalModel ring hn fresh update)
            start
            (grantDrainEntranceNext ring fresh update state e).physical
            (sharedFullLabelNextHost
              (grantDrainCanonicalModel ring hn fresh update)
              state.physical hosts e) := by
        exact sharedFullLabelNextHostCover
          (grantDrainCanonicalModel ring hn fresh update)
          (by omega : 2 ≤ n) start state.physical hosts hcover e
      change
        (rest.foldl
          (sharedGrantFullLabelWordStep
            (grantDrainCanonicalModel ring hn fresh update))
          ((grantDrainEntranceNext ring fresh update state e).physical,
            sharedFullLabelNextHost
              (grantDrainCanonicalModel ring hn fresh update)
              state.physical hosts e)).2 id =
        ((rest.foldl (grantDrainEntranceNext ring fresh update)
          (grantDrainEntranceNext ring fresh update state e)).grantLabels
          id).host
      exact ih (grantDrainEntranceNext ring fresh update state e)
        (sharedFullLabelNextHost
          (grantDrainCanonicalModel ring hn fresh update)
          state.physical hosts e) hnextCover hnextAlign id

/-- Requested FIRST interface theorem. Although everMarked uses the
source ledger and grantHost uses the full label sets, their hosts
agree on EVERY physical edge prefix, even after coalescence and
OLD-root leader sink. Mark promotion is thus attached to the
correct full-label identity, never a different representative. -/
theorem sharedGrantFaithfulMarkFullHostEq
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (start : GrantDrainState n Scratch)
    (word : List (Fin n)) (id : Fin n) :
    (sharedGrantFaithfulGhost ring hn fresh update start).grantHost
      id word.reverse =
    ((grantDrainEntranceRun ring fresh update
      (grantDrainEntranceInitial ring start) word).grantLabels id).host := by
  unfold sharedGrantFaithfulGhost
  change
    (sharedGrantFullLabelWordRun
      (grantDrainCanonicalModel ring hn fresh update)
      start (word.reverse).reverse).2 id =
    ((grantDrainEntranceRun ring fresh update
      (grantDrainEntranceInitial ring start) word).grantLabels id).host
  rw [List.reverse_reverse]
  unfold sharedGrantFullLabelWordRun grantDrainEntranceRun
  change
    (word.foldl
      (sharedGrantFullLabelWordStep
        (grantDrainCanonicalModel ring hn fresh update))
      (start, fun i => if start.grant i then some i else none)).2 id =
    ((word.foldl (grantDrainEntranceNext ring fresh update)
      (grantDrainEntranceInitial ring start)).grantLabels id).host
  apply sharedCrossingAlignedFold ring hn fresh update start word
    (grantDrainEntranceInitial ring start)
    (fun i => if start.grant i then some i else none)
  · exact sharedGrantFullLabelInitialCover
      (grantDrainCanonicalModel ring hn fresh update) start
  · intro i
    rfl

/-- The mark bit of the faithful ghost is precisely the ordered
source-ledger mark. The historical bit cannot be erased at a recut. -/
private theorem sharedGrantFaithfulUnmarked
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (start : GrantDrainState n Scratch)
    (word : List (Fin n)) (id : Fin n)
    (h :
      (sharedGrantFaithfulGhost ring hn fresh update start).everMarked
        id word.reverse = false) :
    ((grantDrainEntranceRun ring fresh update
      (grantDrainEntranceInitial ring start) word).grantLabels id).mark =
        .unmarked := by
  unfold sharedGrantFaithfulGhost at h
  change
    (match ((grantDrainEntranceRun ring fresh update
      (grantDrainEntranceInitial ring start)
      (word.reverse).reverse).grantLabels id).mark with
     | .unmarked => false
     | _ => true) = false at h
  rw [List.reverse_reverse] at h
  cases hm :
      ((grantDrainEntranceRun ring fresh update
        (grantDrainEntranceInitial ring start) word).grantLabels id).mark with
  | unmarked => rfl
  | weak => simp [hm] at h
  | strong => simp [hm] at h
  | terminal => simp [hm] at h

/-! The original crossing counter counts outgoing hits only while
bulletHost is SOME. The source nominated-hit clock pads retired
bullets with a fixed edge. Hence the sound comparison is <=, not
equality after retirement. -/

private def sharedCrossingPrefixHits {n : Nat}
    (host : List (Fin n) → Option (Fin n)) :
    List (Fin n) → List (Fin n) → Nat
  | _, [] => 0
  | past, e :: word =>
      (if host past = some e then 1 else 0) +
        sharedCrossingPrefixHits host (e :: past) word

private theorem sharedCrossingFoldHitsAux {n : Nat}
    (host : List (Fin n) → Option (Fin n)) :
    ∀ (word past : List (Fin n)) (acc : Nat),
      (word.foldl
        (fun z e =>
          (e :: z.1, z.2 +
            (if host z.1 = some e then 1 else 0)))
        (past, acc)).2 =
        acc + sharedCrossingPrefixHits host past word := by
  intro word
  induction word with
  | nil =>
      intro past acc
      simp [sharedCrossingPrefixHits]
  | cons e rest ih =>
      intro past acc
      change
        (rest.foldl
          (fun z a =>
            (a :: z.1, z.2 +
              (if host z.1 = some a then 1 else 0)))
          (e :: past,
            acc + (if host past = some e then 1 else 0))).2 =
        acc + ((if host past = some e then 1 else 0) +
          sharedCrossingPrefixHits host (e :: past) rest)
      rw [ih (e :: past)
        (acc + (if host past = some e then 1 else 0))]
      omega

private theorem sharedCrossingOutgoingHitsEqPrefix {n : Nat}
    (host : List (Fin n) → Option (Fin n))
    (word : List (Fin n)) :
    sharedBadLiveOutgoingHits host word =
      sharedCrossingPrefixHits host [] word := by
  unfold sharedBadLiveOutgoingHits
  have h := sharedCrossingFoldHitsAux host word [] 0
  simpa only [Nat.zero_add] using h

private theorem sharedCrossingEntranceRunAppend
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (initial : GrantDrainEntranceState n Scratch)
    (earlier : List (Fin n)) (e : Fin n) :
    grantDrainEntranceRun ring fresh update initial (earlier ++ [e]) =
      grantDrainEntranceNext ring fresh update
        (grantDrainEntranceRun ring fresh update initial earlier) e := by
  induction earlier generalizing initial with
  | nil => rfl
  | cons a rest ih =>
      change
        grantDrainEntranceRun ring fresh update
          (grantDrainEntranceNext ring fresh update initial a)
          (rest ++ [e]) =
        grantDrainEntranceNext ring fresh update
          (grantDrainEntranceRun ring fresh update
            (grantDrainEntranceNext ring fresh update initial a)
            rest) e
      exact ih (grantDrainEntranceNext ring fresh update initial a)

/-- At every prefix, the exact LIVE host hit is covered by the
padded nominated clock. There is no requirement that the
bullet remain alive through the final word. -/
private theorem sharedCrossingPrefixHitsLeNominated
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (initial : GrantDrainEntranceState n Scratch)
    (j : Fin n) :
    ∀ (word past : List (Fin n))
      (state : GrantDrainEntranceState n Scratch),
      state = grantDrainEntranceRun ring fresh update initial past.reverse →
      sharedCrossingPrefixHits
        (fun earlier =>
          (grantDrainEntranceRun ring fresh update
            initial earlier.reverse).bulletHosts j)
        past word ≤
      grantDrainEntranceBulletHits ring fresh update j state word := by
  intro word
  induction word with
  | nil =>
      intro past state _
      simp [sharedCrossingPrefixHits, grantDrainEntranceBulletHits]
  | cons e rest ih =>
      intro past state hstate
      have hbit :
          (if (grantDrainEntranceRun ring fresh update
            initial past.reverse).bulletHosts j = some e then 1 else 0) ≤
          (if e = grantDrainEntranceBulletChosen state j then 1 else 0) := by
        rw [← hstate]
        cases hb : state.bulletHosts j with
        | none =>
            simp [grantDrainEntranceBulletChosen, hb]
        | some b =>
            by_cases he : e = b
            · subst e
              simp [grantDrainEntranceBulletChosen, hb]
            · simp [grantDrainEntranceBulletChosen, hb, he, eq_comm]
      have hnext :
          grantDrainEntranceNext ring fresh update state e =
            grantDrainEntranceRun ring fresh update
              initial (e :: past).reverse := by
        rw [List.reverse_cons,
          sharedCrossingEntranceRunAppend]
        rw [← hstate]
      have htail := ih (e :: past)
        (grantDrainEntranceNext ring fresh update state e) hnext
      change
        (if (grantDrainEntranceRun ring fresh update
          initial past.reverse).bulletHosts j = some e then 1 else 0) +
          sharedCrossingPrefixHits
            (fun earlier =>
              (grantDrainEntranceRun ring fresh update
                initial earlier.reverse).bulletHosts j)
            (e :: past) rest ≤
        (if e = grantDrainEntranceBulletChosen state j then 1 else 0) +
          grantDrainEntranceBulletHits ring fresh update j
            (grantDrainEntranceNext ring fresh update state e) rest
      exact Nat.add_le_add hbit htail

/-- This is the other interface needed for R8 step 4. It converts
the original ghost's old-state outgoing-host count into the
source-ledger nominated count on the same actual word. -/
theorem sharedGrantFaithfulHitsLeNominated
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (start : GrantDrainState n Scratch)
    (word : List (Fin n)) (id : Fin n) :
    sharedBadLiveOutgoingHits
      ((sharedGrantFaithfulGhost ring hn fresh update start).bulletHost id)
      word ≤
    grantDrainEntranceBulletHits ring fresh update id
      (grantDrainEntranceInitial ring start) word := by
  change
    sharedBadLiveOutgoingHits
      (fun earlier =>
        (grantDrainEntranceRun ring fresh update
          (grantDrainEntranceInitial ring start)
          earlier.reverse).bulletHosts id) word ≤
    grantDrainEntranceBulletHits ring fresh update id
      (grantDrainEntranceInitial ring start) word
  rw [sharedCrossingOutgoingHitsEqPrefix]
  exact sharedCrossingPrefixHitsLeNominated ring fresh update
    (grantDrainEntranceInitial ring start) id
    word [] (grantDrainEntranceInitial ring start) rfl

/-- The requested paper-EXACT crossing theorem. Its hypotheses
refer to the faithful three-coordinate ghost and the genuinely
paper-bad surviving LIVE. No new Prop or protocol state is added.
The actual geometric noncrossing is
grantDrainEntranceNominatedQuota, whose witness is the SOURCE
ledger label now identified with the FULL label host. -/
theorem sharedGrantFaithfulPaperCrossing
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (start : GrantDrainState n Scratch)
    (hPB : PPlus ring start.native)
    (word : List (Fin n))
    (bulletId grantId bSite gSite : Fin n)
    (hBullet :
      (sharedGrantFaithfulGhost ring hn fresh update start).bulletHost
        bulletId word.reverse = some bSite)
    (hGrant :
      (sharedGrantFaithfulGhost ring hn fresh update start).grantHost
        grantId word.reverse = some gSite)
    (hUnmarked :
      (sharedGrantFaithfulGhost ring hn fresh update start).everMarked
        grantId word.reverse = false)
    (_hBad : SharedPaperNonleftmostLiveExact ring
      (sharedGrantPhysicalRun
        (grantDrainCanonicalModel ring hn fresh update)
        start word).native bSite) :
    sharedBadLiveOutgoingHits
      ((sharedGrantFaithfulGhost ring hn fresh update start).bulletHost
        bulletId) word < n := by
  have hB :
      (grantDrainEntranceRun ring fresh update
        (grantDrainEntranceInitial ring start) word).bulletHosts bulletId =
          some bSite := by
    change (grantDrainEntranceRun ring fresh update
      (grantDrainEntranceInitial ring start)
      (word.reverse).reverse).bulletHosts bulletId = some bSite at hBullet
    simpa only [List.reverse_reverse] using hBullet
  have hG :
      ((grantDrainEntranceRun ring fresh update
        (grantDrainEntranceInitial ring start) word).grantLabels
        grantId).host = some gSite := by
    rw [← sharedGrantFaithfulMarkFullHostEq
      ring hn fresh update start word grantId]
    exact hGrant
  have hM := sharedGrantFaithfulUnmarked
    ring hn fresh update start word grantId hUnmarked
  have hQuota :=
    grantDrainEntranceNominatedQuota ring hn fresh update
      start word bulletId grantId bSite gSite
      hPB hB hG hM
  have hHits := sharedGrantFaithfulHitsLeNominated
    ring hn fresh update start word bulletId
  exact Nat.lt_of_le_of_lt hHits hQuota

/-- Decision on the ORIGINAL narrow-observer Prop: TRUE when
instantiated with the faithful ghost and a protected native cut.
BankGrantNonleftmostLive implies the corrected paper observer,
so the stronger paper crossing theorem immediately supplies it.
refutes the OLD ancestry Prop, not this crossing Prop. -/
theorem sharedGrantFaithfulBankCrossing
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (start : GrantDrainState n Scratch)
    (hPB : PPlus ring start.native) :
    SharedGrantBadLiveCrossing
      (grantDrainCanonicalModel ring hn fresh update)
      start (sharedGrantFaithfulGhost ring hn fresh update start) := by
  intro word bulletId grantId bSite gSite
    hBullet hGrant hUnmarked hBank
  have hPaper : SharedPaperNonleftmostLiveExact ring
      (sharedGrantPhysicalRun
        (grantDrainCanonicalModel ring hn fresh update)
        start word).native bSite := by
    have hBankNative : BankGrantNonleftmostLive ring
        (sharedGrantPhysicalRun
          (grantDrainCanonicalModel ring hn fresh update)
          start word).native bSite := by
      change BankGrantNonleftmostLive ring
        (sharedGrantPhysicalRun
          (grantDrainCanonicalModel ring hn fresh update)
          start word).native bSite at hBank
      exact hBank
    have hOld : SharedPaperNonleftmostLive ring
        (sharedGrantPhysicalRun
          (grantDrainCanonicalModel ring hn fresh update)
          start word).native bSite :=
      sharedBankNonleftmostImpliesPaper ring _ bSite hBankNative
    exact sharedPaperOldObserverImpliesExact ring _ bSite hOld
  exact sharedGrantFaithfulPaperCrossing
    ring hn fresh update start hPB word
    bulletId grantId bSite gSite
    hBullet hGrant hUnmarked hPaper

end L3.GrantDrainShared

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-!
R8 step 5.
No declaration below asserts GrantDrainLedgerNoExhaustion.

(1) The first lemma is an arbitrary-n, actual-step ZERO-ARC
preservation theorem on the incoming edge killing a quiet,
unshielded weak source. This proves the former [p,g) suffix
for every cyclic distance, including wraparound and every FIRE.
The additional shielded-prefix concatenation from the killer
LIVE's peaceful source to p is not discharged here.

(2) Retirement forces zero remaining immediately, and remains
absorbed through every future word. An old held GRANT retires
on its next nominated outgoing edge, irrespective of hostile
fresh requests and other OLD tokens.

(3) Independently transported proof-only origins that share
one host nominate the SAME edge at all later cuts and never
split. Their individual already-marked counters do not reset.
Consequently both strong/terminal counters remain <= n, and
both weak-or-higher counters remain <= 2*n, after any future
word; no quota multiplication by the number of coalesced
identities is present. These are upper-bound/accounting
statements, NOT the missing positive-remaining geometric
invariant.
-/

/-- Weak-source death preserves every OLD zero-signal site of
[p,g), with p included and g excluded, for an arbitrary
cyclic distance. The selected native row is the ORIGINAL
post-E/post-FIRE canonical row. This is the old-suffix half
of the D.1 death-to-strong concatenation. -/
theorem grantDrainWeakDeathOldArcZeroAllDistances
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (p g e : Fin n)
    (hIncoming : ring.rightNeighbor e = p)
    (hLive : (s.native e).b = (2 : Fin 3))
    (hLeader : (s.native p).l = true)
    (hUnshielded : (s.native p).sh = false)
    (hQuiet : (s.native p).sg = false)
    (hOldZero : GrantDrainMarksZeroOffsetArc ring s.native p g) :
    GrantDrainMarksZeroOffsetArc ring
      (grantDrainStep ring fresh update s e).native p g := by
  change GrantDrainMarksZeroOffsetArc ring
    (grantDrainNativeNext ring s e) p g
  intro k hk
  by_cases hkzero : k = 0
  · subst k
    have hEndpoint :
        (grantDrainNativeNext ring s e p).sg = false := by
      have hCases :=
        grantDrainWeakSourceQuietDeathAllFire
          (by omega : 3 ≤ n) ring s e
          hLive
          (by simpa only [hIncoming] using hLeader)
          (by simpa only [hIncoming] using hUnshielded)
          (by simpa only [hIncoming] using hQuiet)
      rcases hCases with hFollower | hBorn
      · simpa only [hIncoming] using hFollower.2.2
      · simpa only [hIncoming] using hBorn.2.2
    have hZeroShift : PPL.shiftRight ring p 0 = p := by
      apply Fin.ext
      simp [PPL.shiftRight, Nat.mod_eq_of_lt p.isLt]
    rw [hZeroShift]
    exact hEndpoint
  · have hFrame :=
      grantDrainMarksIncomingSourceInteriorFrame
        (by omega : 3 ≤ n)
        ring s p g e hIncoming k (by omega) hk
    rw [hFrame]
    exact hOldZero k hk

/-- The killed quiet source is either an actual signal-zero
follower or a fresh protected signal-zero leader. The death
edge itself cannot introduce a one-signal site at p. -/
theorem grantDrainWeakDeathOldSourcePostClassification
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (p e : Fin n)
    (hIncoming : ring.rightNeighbor e = p)
    (hLive : (s.native e).b = (2 : Fin 3))
    (hLeader : (s.native p).l = true)
    (hUnshielded : (s.native p).sh = false)
    (hQuiet : (s.native p).sg = false) :
    (((grantDrainStep ring fresh update s e).native p).l = false ∧
      ((grantDrainStep ring fresh update s e).native p).sh = false ∧
      ((grantDrainStep ring fresh update s e).native p).sg = false) ∨
    (((grantDrainStep ring fresh update s e).native p).l = true ∧
      ((grantDrainStep ring fresh update s e).native p).sh = true ∧
      ((grantDrainStep ring fresh update s e).native p).sg = false) := by
  have hRow :=
    grantDrainWeakSourceQuietDeathActualStep
      (by omega : 3 ≤ n) ring fresh update s e
      hLive
      (by simpa only [hIncoming] using hLeader)
      (by simpa only [hIncoming] using hUnshielded)
      (by simpa only [hIncoming] using hQuiet)
  simpa only [hIncoming] using hRow

/-- If a source ledger identity has NO new host, its remaining
quota is exactly zero, regardless of its OLD mark and remaining
counter. No numerical credit can survive retirement. -/
theorem grantDrainLedgerRetiredNextRemainingZero
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hRetired :
      (grantDrainLedgerStep ring fresh update s e label).host = none) :
    (grantDrainLedgerStep ring fresh update s e label).remaining = 0 := by
  have hHost :
      grantDrainLedgerHost ring fresh s e label.host = none := hRetired
  change grantDrainLedgerRemainingNext n label
      (grantDrainLedgerHost ring fresh s e label.host)
      (grantDrainLedgerMarkNext ring fresh update s e label)
      (grantDrainLedgerNominatedHit ring s e label.host)
      (grantDrainLedgerHeld
        (grantDrainStep ring fresh update s e)
        (grantDrainLedgerHost ring fresh s e label.host)) = 0
  rw [hHost]
  rfl

/-- At a retired host there is no selected old-state nominated
edge, independently of the current physical pair or request. -/
theorem grantDrainRetiredNominatedHitFalse
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (e : Fin n) :
    grantDrainLedgerNominatedHit ring s e none = false := by
  rfl

/-- Exact arbitrary-word absorption of BOTH host and quota.
Only an actually retired identity is covered; it does not
hypothesize a future retirement time or a stopping rule. -/
theorem grantDrainLedgerRetiredWordNoRecharge
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    ∀ (word : List (Fin n))
      (s : GrantDrainState n Scratch)
      (label : GrantDrainLedgerLabel n),
      label.host = none →
      label.remaining = 0 →
      (grantDrainLedgerRun ring fresh update s label word).2.host = none ∧
      (grantDrainLedgerRun ring fresh update s label word).2.remaining = 0 := by
  intro word
  induction word with
  | nil =>
      intro s label hHost hZero
      exact ⟨hHost, hZero⟩
  | cons e es ih =>
      intro s label hHost hZero
      have hNextHost :
          (grantDrainLedgerStep ring fresh update s e label).host = none :=
        grantDrainLedgerStep_retired_absorbing
          ring fresh update s e label hHost
      have hNextZero :
          (grantDrainLedgerStep ring fresh update s e label).remaining = 0 :=
        grantDrainLedgerRetiredNextRemainingZero
          ring fresh update s e label hNextHost
      change
        (grantDrainLedgerRun ring fresh update
          (grantDrainStep ring fresh update s e)
          (grantDrainLedgerStep ring fresh update s e label) es).2.host =
          none ∧
        (grantDrainLedgerRun ring fresh update
          (grantDrainStep ring fresh update s e)
          (grantDrainLedgerStep ring fresh update s e label) es).2.remaining =
          0
      exact ih _ _ hNextHost hNextZero

/-- The precise cut-after-retirement assertion: a label retired
on an arbitrary selected edge remains retired AND has zero quota
at every later prefix, no matter what the adversary does. -/
theorem grantDrainLedgerRetiredAfterEdgeForever
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n)
    (word : List (Fin n))
    (hRetired :
      (grantDrainLedgerStep ring fresh update s e label).host = none) :
    (grantDrainLedgerRun ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e label)
      word).2.host = none ∧
    (grantDrainLedgerRun ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e label)
      word).2.remaining = 0 := by
  exact grantDrainLedgerRetiredWordNoRecharge
    ring fresh update word
    (grantDrainStep ring fresh update s e)
    (grantDrainLedgerStep ring fresh update s e label)
    hRetired
    (grantDrainLedgerRetiredNextRemainingZero
      ring fresh update s e label hRetired)

/-- On the outgoing service of an OLD request/grant pair,
either F0 is selected or the final initiator is a leader.
The two cases both sink the pair's old grant. -/
theorem grantDrainHeldOutgoingSelectorOrLeader
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hRequest : s.request e = true)
    (hGrant : s.grant e = true) :
    grantDrainSelect ring s e = .leftLocal ∨
      (grantDrainNativeNext ring s e e).l = true := by
  by_cases hLeader : (s.native e).l = true
  · exact Or.inr
      (grantDrainMarksOutgoingLeaderNext ring s e hLeader)
  · left
    have hAfterELeader :
        (nativeE ring s.native e e).l = false := by
      rw [grantDrainMarksNativeESource,
        grantDrainMarksOutgoingSourceLeaderNative]
      simpa using hLeader
    have hAfterEBullet :
        (nativeE ring s.native e e).b = (0 : Fin 3) :=
      GrantDrainEntrance.grantDrainEntranceNativeESourceBulletZero ring s.native e
    have hEligible :
        grantDrainEligible (nativeE ring s.native e) e = true := by
      simp [grantDrainEligible, hAfterELeader, hAfterEBullet]
    simp [grantDrainSelect, hRequest, hGrant, hEligible]

/-- Finite T0 and final-leader-sink checks, independent of all
other old-token bits and of hostile responder request creation. -/
theorem grantDrainHeldOutgoingLeftLocalGrantSink
    (ry gy lx ly fresh : Bool) :
    (grantDrainTokenRow true true ry gy lx ly fresh .leftLocal).1.grant =
      false := by
  cases ry <;> cases gy <;> cases lx <;>
    cases ly <;> cases fresh <;> decide

theorem grantDrainHeldOutgoingLeaderGrantSink
    (ry gy ly fresh : Bool) (fire : GrantDrainFire) :
    (grantDrainTokenRow true true ry gy true ly fresh fire).1.grant =
      false := by
  cases ry <;> cases gy <;> cases ly <;>
    cases fresh <;> cases fire <;> decide

/-- A terminal OLD held identity RETIRES on its nominated
outgoing edge, in the actual source ledger, for every n.
The conclusion is about the physical owner, not just a mark. -/
theorem grantDrainHeldOutgoingRetires
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hHost : label.host = some e)
    (hRequest : s.request e = true)
    (hGrant : s.grant e = true) :
    (grantDrainLedgerStep ring fresh update s e label).host = none := by
  have hOutcome :=
    grantDrainHeldOutgoingSelectorOrLeader
      ring s e hRequest hGrant
  have hRow :
      (grantDrainLedgerRow ring fresh s e).1.grant = false := by
    unfold grantDrainLedgerRow
    rcases hOutcome with hFire | hLeader
    · rw [hRequest, hGrant, hFire]
      exact grantDrainHeldOutgoingLeftLocalGrantSink
        (s.request (ring.rightNeighbor e))
        (s.grant (ring.rightNeighbor e))
        (grantDrainNativeNext ring s e e).l
        (grantDrainNativeNext ring s e (ring.rightNeighbor e)).l
        (fresh s e)
    · rw [hRequest, hGrant, hLeader]
      exact grantDrainHeldOutgoingLeaderGrantSink
        (s.request (ring.rightNeighbor e))
        (s.grant (ring.rightNeighbor e))
        (grantDrainNativeNext ring s e (ring.rightNeighbor e)).l
        (fresh s e) (grantDrainSelect ring s e)
  change grantDrainLedgerHost ring fresh s e label.host = none
  rw [hHost]
  show (if e = e then
      (if (s.grant e && (grantDrainLedgerRow ring fresh s e).1.grant) = true
        then some e else none) else _) = none
  rw [if_pos rfl, hGrant, hRow]
  rfl

/-- The terminal held outgoing hit consumes the grant identity
and its remaining quota; both stay extinct forever. -/
theorem grantDrainHeldOutgoingRetiresForever
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n)
    (word : List (Fin n))
    (hHost : label.host = some e)
    (hRequest : s.request e = true)
    (hGrant : s.grant e = true) :
    (grantDrainLedgerRun ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e label)
      word).2.host = none ∧
    (grantDrainLedgerRun ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e label)
      word).2.remaining = 0 := by
  exact grantDrainLedgerRetiredAfterEdgeForever
    ring fresh update s e label word
    (grantDrainHeldOutgoingRetires
      ring fresh update s e label hHost hRequest hGrant)

/-- A still-marked ledger identity cannot have its remaining
budget enlarged by ANY scheduler word, even if its mark is
promoted by a native leader death or by coalescence. -/
theorem grantDrainLedgerMarkedNextStillMarked
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hMarked : label.mark ≠ .unmarked) :
    (grantDrainLedgerStep ring fresh update s e label).mark ≠ .unmarked := by
  intro hBad
  have hRank :=
    grantDrainLedgerStep_mark_monotone ring fresh update s e label
  rw [hBad] at hRank
  cases hm : label.mark with
  | unmarked =>
      exact hMarked hm
  | weak =>
      simp [hm, grantDrainMarkRank] at hRank
  | strong =>
      simp [hm, grantDrainMarkRank] at hRank
  | terminal =>
      simp [hm, grantDrainMarkRank] at hRank

theorem grantDrainLedgerMarkedWordNoReset
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    ∀ (word : List (Fin n))
      (s : GrantDrainState n Scratch)
      (label : GrantDrainLedgerLabel n),
      label.mark ≠ .unmarked →
      (grantDrainLedgerRun ring fresh update s label word).2.remaining ≤
        label.remaining := by
  intro word
  induction word with
  | nil =>
      intro s label hMarked
      exact Nat.le_refl _
  | cons e es ih =>
      intro s label hMarked
      have hNextMarked :=
        grantDrainLedgerMarkedNextStillMarked
          ring fresh update s e label hMarked
      have hTail :=
        ih (grantDrainStep ring fresh update s e)
          (grantDrainLedgerStep ring fresh update s e label)
          hNextMarked
      have hFirst :=
        grantDrainLedgerStep_remaining_nonincrease
          ring fresh update s e label hMarked
      change
        (grantDrainLedgerRun ring fresh update
          (grantDrainStep ring fresh update s e)
          (grantDrainLedgerStep ring fresh update s e label) es).2.remaining ≤
        label.remaining
      exact Nat.le_trans hTail hFirst

/-- Once two separately tracked source identities are at the SAME
host, the exact source Y/X transport never splits their hosts.
This is a no-reissuance result, not an assumption of distinctness. -/
theorem grantDrainLedgerSameHostNext
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (a b : GrantDrainLedgerLabel n)
    (hSame : a.host = b.host) :
    (grantDrainLedgerStep ring fresh update s e a).host =
      (grantDrainLedgerStep ring fresh update s e b).host := by
  change grantDrainLedgerHost ring fresh s e a.host =
    grantDrainLedgerHost ring fresh s e b.host
  rw [hSame]

/-- The common host persists for every word of actual physical
transitions, including FIRE, old HOLD, leader death, and births. -/
theorem grantDrainLedgerSameHostWord
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    ∀ (word : List (Fin n))
      (s : GrantDrainState n Scratch)
      (a b : GrantDrainLedgerLabel n),
      a.host = b.host →
      (grantDrainLedgerRun ring fresh update s a word).2.host =
        (grantDrainLedgerRun ring fresh update s b word).2.host := by
  intro word
  induction word with
  | nil =>
      intro s a b hSame
      exact hSame
  | cons e es ih =>
      intro s a b hSame
      have hNextSame :=
        grantDrainLedgerSameHostNext
          ring fresh update s e a b hSame
      change
        (grantDrainLedgerRun ring fresh update
          (grantDrainStep ring fresh update s e)
          (grantDrainLedgerStep ring fresh update s e a) es).2.host =
        (grantDrainLedgerRun ring fresh update
          (grantDrainStep ring fresh update s e)
          (grantDrainLedgerStep ring fresh update s e b) es).2.host
      exact ih _ _ _ hNextSame

/-- The physical coordinate is independent of the proof-only
identity. This is essential when comparing nominated edges of
two coalesced origins on the SAME selected scheduler word. -/
theorem grantDrainLedgerWordPhysicalIndependent
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    ∀ (word : List (Fin n))
      (s : GrantDrainState n Scratch)
      (a b : GrantDrainLedgerLabel n),
      (grantDrainLedgerRun ring fresh update s a word).1 =
        (grantDrainLedgerRun ring fresh update s b word).1 := by
  intro word
  induction word with
  | nil =>
      intro s a b
      rfl
  | cons e es ih =>
      intro s a b
      change
        (grantDrainLedgerRun ring fresh update
          (grantDrainStep ring fresh update s e)
          (grantDrainLedgerStep ring fresh update s e a) es).1 =
        (grantDrainLedgerRun ring fresh update
          (grantDrainStep ring fresh update s e)
          (grantDrainLedgerStep ring fresh update s e b) es).1
      exact ih _ _ _

/-- Coalesced identities nominate one physical edge, NOT two
different opportunities or a sum of two independent clocks. -/
theorem grantDrainLedgerSameHostWordNominee
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (a b : GrantDrainLedgerLabel n)
    (word : List (Fin n)) (e : Fin n)
    (hSame : a.host = b.host) :
    grantDrainLedgerNominatedHit ring
      (grantDrainLedgerRun ring fresh update s a word).1 e
      (grantDrainLedgerRun ring fresh update s a word).2.host =
    grantDrainLedgerNominatedHit ring
      (grantDrainLedgerRun ring fresh update s b word).1 e
      (grantDrainLedgerRun ring fresh update s b word).2.host := by
  rw [grantDrainLedgerWordPhysicalIndependent
    ring fresh update word s a b,
    grantDrainLedgerSameHostWord
      ring fresh update word s a b hSame]

/-- After a literal coalescing edge, any TWO origins whose
new hosts are equal and whose new marks are non-unmarked
share one site trajectory. Each still has <= 2n quota, even
after an arbitrary subsequent word. Their bounds are per
origin, not summed across coalesced labels. -/
theorem grantDrainCoalescedWeakQuotaAllWords
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e : Fin n) (a b : GrantDrainLedgerLabel n)
    (word : List (Fin n))
    (hSame :
      (grantDrainLedgerStep ring fresh update s e a).host =
        (grantDrainLedgerStep ring fresh update s e b).host)
    (hMarkA :
      (grantDrainLedgerStep ring fresh update s e a).mark ≠ .unmarked)
    (hMarkB :
      (grantDrainLedgerStep ring fresh update s e b).mark ≠ .unmarked) :
    (grantDrainLedgerRun ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e a)
      word).2.remaining ≤ 2 * n ∧
    (grantDrainLedgerRun ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e b)
      word).2.remaining ≤ 2 * n ∧
    (grantDrainLedgerRun ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e a)
      word).2.host =
    (grantDrainLedgerRun ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e b)
      word).2.host := by
  have hA :=
    grantDrainLedgerMarkedWordNoReset
      ring fresh update word
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e a)
      hMarkA
  have hB :=
    grantDrainLedgerMarkedWordNoReset
      ring fresh update word
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e b)
      hMarkB
  exact
    ⟨Nat.le_trans hA
       (grantDrainLedgerStep_quota_le_double
         ring fresh update s e a),
     Nat.le_trans hB
       (grantDrainLedgerStep_quota_le_double
         ring fresh update s e b),
     grantDrainLedgerSameHostWord
       ring fresh update word
       (grantDrainStep ring fresh update s e)
       (grantDrainLedgerStep ring fresh update s e a)
       (grantDrainLedgerStep ring fresh update s e b)
       hSame⟩

/-- Strong or terminal labels coalescing on one source grant
each retain at most ONE n-hit cap, even after further edges.
No label receives new credit when another label merges with it. -/
theorem grantDrainCoalescedStrongQuotaAllWords
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e : Fin n) (a b : GrantDrainLedgerLabel n)
    (word : List (Fin n))
    (hSame :
      (grantDrainLedgerStep ring fresh update s e a).host =
        (grantDrainLedgerStep ring fresh update s e b).host)
    (hStrongA : 2 ≤ grantDrainMarkRank
      (grantDrainLedgerStep ring fresh update s e a).mark)
    (hStrongB : 2 ≤ grantDrainMarkRank
      (grantDrainLedgerStep ring fresh update s e b).mark) :
    (grantDrainLedgerRun ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e a)
      word).2.remaining ≤ n ∧
    (grantDrainLedgerRun ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e b)
      word).2.remaining ≤ n ∧
    (grantDrainLedgerRun ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e a)
      word).2.host =
    (grantDrainLedgerRun ring fresh update
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e b)
      word).2.host := by
  have hMarkedA :
      (grantDrainLedgerStep ring fresh update s e a).mark ≠ .unmarked := by
    intro h
    rw [h, grantDrainMarkRank] at hStrongA
    omega
  have hMarkedB :
      (grantDrainLedgerStep ring fresh update s e b).mark ≠ .unmarked := by
    intro h
    rw [h, grantDrainMarkRank] at hStrongB
    omega
  have hA :=
    grantDrainLedgerMarkedWordNoReset
      ring fresh update word
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e a)
      hMarkedA
  have hB :=
    grantDrainLedgerMarkedWordNoReset
      ring fresh update word
      (grantDrainStep ring fresh update s e)
      (grantDrainLedgerStep ring fresh update s e b)
      hMarkedB
  exact
    ⟨Nat.le_trans hA
       (grantDrainLedgerStep_quota_le_strong
         ring fresh update s e a hStrongA),
     Nat.le_trans hB
       (grantDrainLedgerStep_quota_le_strong
         ring fresh update s e b hStrongB),
     grantDrainLedgerSameHostWord
       ring fresh update word
       (grantDrainStep ring fresh update s e)
       (grantDrainLedgerStep ring fresh update s e a)
       (grantDrainLedgerStep ring fresh update s e b)
       hSame⟩

/-- The full-label transport and the actual source
ledger's upper quota bounds coexist on the SAME canonical edge.
Unlike the two preceding statements, this theorem supplies actual
physical ancestry cover, without assuming an imagined no-cloning
bijection. A separate equivalence between the two ghost host maps
and the geometric lower budget still remains to be proved. -/
theorem grantDrainCanonicalFullLabelsWithQuotaCaps
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (start current : GrantDrainState n Scratch)
    (hosts : Fin n → Option (Fin n))
    (labels : Fin n → GrantDrainLedgerLabel n)
    (hCover : GrantDrainShared.SharedGrantFullLabelCover
      (GrantDrainShared.grantDrainCanonicalModel
        ring hn fresh update) start current hosts)
    (e : Fin n) :
    ∃ nextHosts : Fin n → Option (Fin n),
      GrantDrainShared.SharedGrantFullLabelCover
        (GrantDrainShared.grantDrainCanonicalModel
          ring hn fresh update)
        start (grantDrainStep ring fresh update current e) nextHosts ∧
      (∀ origin : Fin n, hosts origin = none →
        nextHosts origin = none) ∧
      (∀ (origin oldSite newSite : Fin n),
        hosts origin = some oldSite →
        nextHosts origin = some newSite →
        newSite = oldSite ∨
          (oldSite = ring.rightNeighbor e ∧ newSite = e)) ∧
      (∀ origin : Fin n,
        (grantDrainLedgerStep ring fresh update current e
          (labels origin)).remaining ≤ 2 * n) := by
  obtain ⟨nextHosts, hNextCover, hRetired, hMovement⟩ :=
    (GrantDrainShared.sharedGrantCanonicalFullLabelTransport
      ring hn fresh update) start current hosts hCover e
  refine ⟨nextHosts, hNextCover, hRetired, hMovement, ?_⟩
  intro origin
  exact grantDrainLedgerStep_quota_le_double
    ring fresh update current e (labels origin)

end L3

namespace L3.GrantDrainEntrance

open L3.HeadlineRenewal
open L3.GrantDrainShared
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-!
The conditional R8e/D.5 scalar entrance starts from
GrantDrainEntranceIntermediateZ = NoBadLive AND I, not merely
NoBadLive. The native I factor is essential for the two
drift theorems. The canonical source transition admits births.
-/

/-- Every actual finite scheduler prefix stays in the drift domain.
This is the canonical source model's step, not a surrogate chain. -/
theorem grantDrainEntranceR8eIntermediateWordClosed
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    ∀ (word : List (Fin n)) (s : GrantDrainState n Scratch),
      GrantDrainEntranceIntermediateZ ring s →
      GrantDrainEntranceIntermediateZ ring
        (word.foldl
          (grantDrainCanonicalModel ring hn fresh update).step s) := by
  intro word
  induction word with
  | nil =>
      intro s hCut
      exact hCut
  | cons e rest ih =>
      intro s hCut
      change GrantDrainEntranceIntermediateZ ring
        (rest.foldl
          (grantDrainCanonicalModel ring hn fresh update).step
          (grantDrainStep ring fresh update s e))
      exact ih (grantDrainStep ring fresh update s e)
        (grantDrainEntranceIntermediateZNext
          ring hn fresh update s e hCut)

/-- Under I, the proven zero-defect criterion converts failure
of C_native into a strictly positive Nat-valued defect count. -/
private theorem grantDrainEntranceR8eDirtyPositive
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (hCut : GrantDrainEntranceIntermediateZ ring s)
    (hDirty : ¬ GrantDrainEntranceClean ring s) :
    0 < grantDrainEntranceSignalCleanupPotential ring s.native := by
  by_cases hZero :
      grantDrainEntranceSignalCleanupPotential ring s.native = 0
  · have hClean : GrantDrainEntranceClean ring s :=
      (grantDrainEntranceR8eZeroImpliesCleanProved
        (Scratch := Scratch) ring) s hCut hZero
    exact False.elim (hDirty hClean)
  · omega

/-- At each dirty state of the closed intermediate class, choose
an OLD-state nominated strict-decrease edge. Outside the class,
or at an already clean state, any fixed edge is harmless because
the restricted cost lemma never requests a drift certificate there. -/
private theorem grantDrainEntranceR8eCandidateEdge
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) :
    ∃ e : Fin n,
      GrantDrainEntranceIntermediateZ ring s →
      ¬ GrantDrainEntranceClean ring s →
      grantDrainEntranceSignalCleanupPotential ring
        (grantDrainStep ring fresh update s e).native + 1 ≤
      grantDrainEntranceSignalCleanupPotential ring s.native := by
  classical
  by_cases hCut : GrantDrainEntranceIntermediateZ ring s
  · by_cases hClean : GrantDrainEntranceClean ring s
    · refine ⟨(⟨0, (show 0 < n by omega)⟩ : Fin n), ?_⟩
      intro _ hDirty
      exact False.elim (hDirty hClean)
    · obtain ⟨e, hDrop⟩ :=
        (grantDrainEntranceR8ePotentialNominatedDropProved
          ring (by omega : 3 ≤ n) fresh update)
          s hCut (grantDrainEntranceR8eDirtyPositive
            ring s hCut hClean)
      refine ⟨e, ?_⟩
      intro _ _
      exact Nat.succ_le_of_lt hDrop
  · refine ⟨(⟨0, (show 0 < n by omega)⟩ : Fin n), ?_⟩
    intro hInside _
    exact False.elim (hCut hInside)

/-- The selection depends only on the current, already observed
physical source state and not on a future scheduler letter. -/
private noncomputable def grantDrainEntranceR8eChosenEdge
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) : Fin n :=
  Classical.choose
    (grantDrainEntranceR8eCandidateEdge
      ring hn fresh update s)

/-- Conditional D.5 clean-sector clock with the SHARP n-2 cap.
The cut is NoBadLive AND I. Every physical successor needed
by the restricted Bellman induction remains in that class.
The bound is on the canonical model's literal step, with its
arbitrary hostile fresh/update functions and possible births. -/
theorem grantDrainEntranceR8eCleanSectorCostSharp
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (hCut : GrantDrainEntranceIntermediateZ ring s)
    (T : Nat) :
    K2ArbitraryElimination.FiniteAccounting.costNumerator
      (grantDrainCanonicalModel ring hn fresh update).step
      (fun x : GrantDrainState n Scratch => C_native ring x.native)
      s T ≤ n ^ T * (n * (n - 2)) := by
  change K2ArbitraryElimination.FiniteAccounting.costNumerator
    (grantDrainStep ring fresh update)
    (GrantDrainEntranceClean ring) s T ≤
      n ^ T * (n * (n - 2))
  have hClosed :
      ∀ x : GrantDrainState n Scratch,
        GrantDrainEntranceIntermediateZ ring x →
        ¬ GrantDrainEntranceClean ring x →
        ∀ e : Fin n,
          GrantDrainEntranceIntermediateZ ring
            (grantDrainStep ring fresh update x e) := by
    intro x hx _ e
    exact grantDrainEntranceIntermediateZNext
      ring hn fresh update x e hx
  have hDrop :
      ∀ x : GrantDrainState n Scratch,
        GrantDrainEntranceIntermediateZ ring x →
        ¬ GrantDrainEntranceClean ring x →
        grantDrainEntranceSignalCleanupPotential ring
          (grantDrainStep ring fresh update x
            (grantDrainEntranceR8eChosenEdge
              ring hn fresh update x)).native + 1 ≤
        grantDrainEntranceSignalCleanupPotential ring x.native := by
    intro x hx hDirty
    exact (Classical.choose_spec
      (grantDrainEntranceR8eCandidateEdge
        ring hn fresh update x)) hx hDirty
  have hNonincrease :
      ∀ x : GrantDrainState n Scratch,
        GrantDrainEntranceIntermediateZ ring x →
        ¬ GrantDrainEntranceClean ring x →
        ∀ e : Fin n,
          grantDrainEntranceSignalCleanupPotential ring
            (grantDrainStep ring fresh update x e).native ≤
          grantDrainEntranceSignalCleanupPotential ring x.native := by
    intro x hx _ e
    exact (grantDrainEntranceR8ePotentialNonincreaseProved
      ring (by omega : 3 ≤ n) fresh update) x e hx
  have hCost :
      K2ArbitraryElimination.FiniteAccounting.costNumerator
        (grantDrainStep ring fresh update)
        (GrantDrainEntranceClean ring) s T ≤
      n ^ T * (n *
        grantDrainEntranceSignalCleanupPotential ring s.native) :=
    L3.Prob.costNumerator_le_of_nominated_edge_on
      (grantDrainStep ring fresh update)
      (GrantDrainEntranceClean ring)
      (GrantDrainEntranceIntermediateZ ring)
      (fun x : GrantDrainState n Scratch =>
        grantDrainEntranceSignalCleanupPotential ring x.native)
      (grantDrainEntranceR8eChosenEdge ring hn fresh update)
      hClosed hDrop hNonincrease s hCut T
  have hCap :
      grantDrainEntranceSignalCleanupPotential ring s.native ≤ n - 2 :=
    (grantDrainEntranceR8ePotentialSharpCapProved
      (Scratch := Scratch) ring (by omega : 3 ≤ n)) s hCut
  calc
    K2ArbitraryElimination.FiniteAccounting.costNumerator
        (grantDrainStep ring fresh update)
        (GrantDrainEntranceClean ring) s T ≤
      n ^ T * (n *
        grantDrainEntranceSignalCleanupPotential ring s.native) := hCost
    _ ≤ n ^ T * (n * (n - 2)) :=
      Nat.mul_le_mul_left _
        (Nat.mul_le_mul_left _ hCap)

/-- Consequently every finite normalized cost is strictly below
4n². The stronger non-strict n(n-2) bound above also controls
the (monotone) expected hitting time after the intermediate cut. -/
theorem grantDrainEntranceR8eCleanSectorCostBelowFour
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (hCut : GrantDrainEntranceIntermediateZ ring s)
    (T : Nat) :
    K2ArbitraryElimination.FiniteAccounting.costNumerator
      (grantDrainCanonicalModel ring hn fresh update).step
      (fun x : GrantDrainState n Scratch => C_native ring x.native)
      s T < n ^ T * (4 * n ^ 2) := by
  have hSharp :=
    grantDrainEntranceR8eCleanSectorCostSharp
      ring hn fresh update s hCut T
  have hPositive : 0 < n := by omega
  have hCoefficient :
      n * (n - 2) < 4 * n ^ 2 := by
    have hLe : n * (n - 2) ≤ n * n :=
      Nat.mul_le_mul_left n (Nat.sub_le n 2)
    have hProductPositive : 0 < n * n :=
      Nat.mul_pos hPositive hPositive
    rw [Nat.pow_two]
    omega
  have hScale :
      n ^ T * (n * (n - 2)) < n ^ T * (4 * n ^ 2) :=
    Nat.mul_lt_mul_of_pos_left hCoefficient (Nat.pow_pos hPositive)
  exact Nat.lt_of_le_of_lt hSharp hScale

/-- Explicit cut-factor form: zero paper-bad LIVE by itself is
not the R8e domain. The native I hypothesis is independently
required, and the all-edge closure theorem keeps both factors. -/
theorem grantDrainEntranceR8eCleanCostOfNoBadAndI
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (hNoBad : GrantDrainEntranceNoBadLive ring s)
    (hI : I ring s.native)
    (T : Nat) :
    K2ArbitraryElimination.FiniteAccounting.costNumerator
      (grantDrainCanonicalModel ring hn fresh update).step
      (fun x : GrantDrainState n Scratch => C_native ring x.native)
      s T < n ^ T * (4 * n ^ 2) := by
  have hCut : GrantDrainEntranceIntermediateZ ring s :=
    ⟨hNoBad, hI⟩
  exact grantDrainEntranceR8eCleanSectorCostBelowFour
    ring hn fresh update s hCut T

end L3.GrantDrainEntrance

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-!
The full arbitrary-distance first-SHIELDED-leader concatenation and
the all-word positive-reserve induction are not asserted here.
The actual death edge is proved to leave the killer's old site
signal-zero, and that site is joined to EVERY old zero-corridor
offset (no bound on the old corridor length). The death service
is not the marked weak host's nominated edge; hence if its
counter was positive, that single death edge cannot exhaust it.

A physical terminal-host leader death is exhibited at n=5.
The persistent ledger mark stays TERMINAL, not STRONG, even
though the moved host gains a physically strong lock.
-/

/-- Peacefulness forces the signal at the old LIVE host itself
to be zero, including when its first-left-leader scan returns none.
This uses the inclusive signal trail of PeacefulCore. -/
theorem grantDrainDeathLiveOwnSignalZero
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch)
    (e : Fin n)
    (hP : PPlus ring s.native)
    (hLive : LiveBullet s.native e) :
    (s.native e).sg = false := by
  have hPeace : PPL.PeacefulCore ring
      (fun i : Fin n => (s.native i).l)
      (fun i : Fin n => (s.native i).sh)
      (fun i : Fin n => (s.native i).sg) e :=
    hP.2 e hLive
  have hZeroShift : PPL.shiftLeft ring e 0 = e := by
    apply Fin.ext
    change (e.val + n - 0 % n) % n = e.val
    simp [Nat.mod_eq_of_lt e.isLt]
  unfold PPL.PeacefulCore at hPeace
  cases hd : PPL.dLLBy ring
      (fun i : Fin n => (s.native i).l) e with
  | none =>
      rw [hd] at hPeace
      exact hPeace e
  | some d =>
      rw [hd] at hPeace
      have hSelf :
          (s.native (PPL.shiftLeft ring e 0)).sg = false :=
        hPeace.2 (⟨0, by omega⟩ : Fin (d + 1))
      simpa only [hZeroShift] using hSelf

/-- The actual old-LIVE killer's signal is zero AFTER its
quiet, unshielded responder leader dies; F0/F2 overwrite
it with the canonical protected zero-signal leader instead.
F1 overwrites only the distinct responder. -/
theorem grantDrainWeakDeathKillerPostSignalZero
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hP : PPlus ring s.native)
    (hLive : LiveBullet s.native e)
    (hLeader : (s.native (ring.rightNeighbor e)).l = true)
    (hUnshielded :
      (s.native (ring.rightNeighbor e)).sh = false)
    (hQuiet :
      (s.native (ring.rightNeighbor e)).sg = false) :
    ((grantDrainStep ring fresh update s e).native e).sg = false := by
  have hKillerZero :=
    grantDrainDeathLiveOwnSignalZero ring s e hP hLive
  have hDeathPair :
      (certLiteralEPair
        (s.native e) (s.native (ring.rightNeighbor e))).2.l = false :=
    (grantDrainWeakSourceQuietDeathPair
      (s.native e) (s.native (ring.rightNeighbor e))
      hLive hLeader hUnshielded hQuiet).2.1
  have hLiteralSourceZero :
      (certLiteralEPair
        (s.native e) (s.native (ring.rightNeighbor e))).1.sg = false :=
    (GrantDrainEntrance.grantDrainEntranceLiteralEDeathSignalsZero
      (s.native e) (s.native (ring.rightNeighbor e))
      hLeader (fun _ => hKillerZero) hDeathPair).1
  have hESource :
      (nativeE ring s.native e e).sg = false := by
    simpa [nativeE] using hLiteralSourceZero
  have hNeighbor :
      ring.rightNeighbor e ≠ e :=
    grantDrainMarksNeighborDistinct (by omega : 3 ≤ n) ring e
  change (grantDrainNativeNext ring s e e).sg = false
  cases hf : grantDrainSelect ring s e with
  | none =>
      simpa [grantDrainNativeNext, hf] using hESource
  | leftLocal =>
      simp [grantDrainNativeNext, hf, canonicalBirth, firedNative]
  | rightLocal =>
      simpa [grantDrainNativeNext, hf,
        canonicalBirth, Ne.symm hNeighbor] using hESource
  | cross =>
      simp [grantDrainNativeNext, hf, canonicalBirth, firedNative]

/-- Clockwise shift across the selected old pair is expressed
entirely in the original directed-ring coordinates. -/
theorem grantDrainWeakDeathRightShiftSucc
    {n : Nat} (ring : DirectedRing n) (e : Fin n) (k : Nat) :
    PPL.shiftRight ring e (k + 1) =
      PPL.shiftRight ring (ring.rightNeighbor e) k := by
  apply Fin.ext
  change (e.val + (k + 1)) % n =
    (((e.val + 1) % n + k) % n)
  calc
    (e.val + (k + 1)) % n = (e.val + 1 + k) % n := by
      congr 1
      omega
    _ = (((e.val + 1) % n + k) % n) := by
      rw [Nat.mod_add_mod]

/-- The killer's own zero signal and the arbitrary-length OLD
weak zero-corridor are now one uninterrupted zero-signal trail
after the ACTUAL canonical death edge. This does not silently
assume that the killer's nearest shielded leader equals the
post-step nearest leader of the grant: the first-leader
concatenation is the remaining geometry obligation. -/
theorem grantDrainWeakDeathStitchedZeroTrail
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (p e g : Fin n)
    (hP : PPlus ring s.native)
    (hLive : LiveBullet s.native e)
    (hEdge : ring.rightNeighbor e = p)
    (hLeader : (s.native p).l = true)
    (hUnshielded : (s.native p).sh = false)
    (hQuiet : (s.native p).sg = false)
    (hOldZero : GrantDrainMarksZeroOffsetArc ring s.native p g) :
    ∀ k : Nat,
      k < PPL.cyclicOffset ring p g + 1 →
      ((grantDrainStep ring fresh update s e).native
        (PPL.shiftRight ring e k)).sg = false := by
  have hKillerPost :=
    grantDrainWeakDeathKillerPostSignalZero
      ring hn fresh update s e hP hLive
      (by simpa only [hEdge] using hLeader)
      (by simpa only [hEdge] using hUnshielded)
      (by simpa only [hEdge] using hQuiet)
  have hOldArcPost :=
    grantDrainWeakDeathOldArcZeroAllDistances
      ring hn fresh update s p g e hEdge
      hLive hLeader hUnshielded hQuiet hOldZero
  intro k hk
  cases k with
  | zero =>
      have hz : PPL.shiftRight ring e 0 = e := by
        apply Fin.ext
        simp [PPL.shiftRight, Nat.mod_eq_of_lt e.isLt]
      simpa only [hz] using hKillerPost
  | succ j =>
      have hj : j < PPL.cyclicOffset ring p g := by
        omega
      change
        ((grantDrainStep ring fresh update s e).native
          (PPL.shiftRight ring e (j + 1))).sg = false
      rw [grantDrainWeakDeathRightShiftSucc ring e j, hEdge]
      exact hOldArcPost j hj

/-- A death edge into the OLD weak source p is not a
nominated incoming hit at a distinct, unheld grant host g. -/
theorem grantDrainWeakDeathNoNominatedHit
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (e p g : Fin n) (label : GrantDrainLedgerLabel n)
    (hHost : label.host = some g)
    (hRequest : s.request g = false)
    (hEdge : ring.rightNeighbor e = p)
    (hDistinct : p ≠ g) :
    grantDrainLedgerNominatedHit ring s e label.host = false := by
  simp [grantDrainLedgerNominatedHit, hHost, hRequest,
    hEdge, hDistinct]

/-- The weak grant's ghost host is unchanged on a source-death
service that is strictly outside its occupied site. This is
source-level GRANT transport, not a hypothetical transition. -/
theorem grantDrainWeakDeathHostFrame
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e p g : Fin n) (label : GrantDrainLedgerLabel n)
    (hHost : label.host = some g)
    (hFrom : e ≠ g)
    (hEdge : ring.rightNeighbor e = p)
    (hTo : p ≠ g) :
    (grantDrainLedgerStep ring fresh update s e label).host =
      some g := by
  change grantDrainLedgerHost ring fresh s e label.host = some g
  rw [hHost]
  have hAway : g ≠ ring.rightNeighbor e := by
    rw [hEdge]
    exact Ne.symm hTo
  simp [grantDrainLedgerHost, Ne.symm hFrom, hAway]

/-- Positive min of two natural budgets. -/
theorem grantDrainDeathMinPositive
    (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    0 < min a b := by
  by_cases hab : a ≤ b
  · rw [Nat.min_eq_left hab]
    exact ha
  · have hba : b ≤ a := by omega
    rw [Nat.min_eq_right hba]
    exact hb

/-- Every already marked quota cap is positive at n>=5,
including terminal HOLD's one-hit cap. -/
theorem grantDrainDeathMarkedCapPositive
    (n : Nat) (hn : 5 ≤ n)
    (mark : GrantDrainMark) (held : Bool)
    (hMarked : mark ≠ .unmarked) :
    0 < grantDrainLedgerQuotaCap n mark held := by
  have hOne : min 1 n = 1 := Nat.min_eq_left (by omega : 1 ≤ n)
  cases mark <;> cases held <;>
    simp [grantDrainLedgerQuotaCap, hOne] at * <;> omega

/-- The death service cannot exhaust a *previously positive*
weak label at an unaffected live host. Unlike the strong n-cap
claim, this lemma does not assume the post-mark is strong:
weak/strong/terminal caps are ALL positive; old nominated hit
is false; the remaining update is a min, never a subtraction.
Global NoExhaustion still requires weak-epoch positivity and
the first-shielded-source geometry at EVERY earlier edge. -/
theorem grantDrainWeakDeathPositiveOffEdge
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e p g : Fin n) (label : GrantDrainLedgerLabel n)
    (hHost : label.host = some g)
    (hMark : label.mark = .weak)
    (hPositive : 0 < label.remaining)
    (hRequest : s.request g = false)
    (hFrom : e ≠ g)
    (hEdge : ring.rightNeighbor e = p)
    (hTo : p ≠ g) :
    (grantDrainLedgerStep ring fresh update s e label).host = some g ∧
    0 < (grantDrainLedgerStep ring fresh update s e label).remaining := by
  have hPostHost :=
    grantDrainWeakDeathHostFrame
      ring fresh update s e p g label hHost hFrom hEdge hTo
  have hNoHit :=
    grantDrainWeakDeathNoNominatedHit
      ring s e p g label hHost hRequest hEdge hTo
  have hOldMarked : label.mark ≠ .unmarked := by
    rw [hMark]
    decide
  have hNewMarked :
      grantDrainLedgerMarkNext ring fresh update s e label ≠
        .unmarked := by
    exact grantDrainLedgerMarkedNextStillMarked
      ring fresh update s e label hOldMarked
  have hCap :
      0 < grantDrainLedgerQuotaCap n
        (grantDrainLedgerMarkNext ring fresh update s e label)
        (grantDrainLedgerHeld
          (grantDrainStep ring fresh update s e)
          (grantDrainLedgerHost ring fresh s e label.host)) :=
    grantDrainDeathMarkedCapPositive n hn _ _ hNewMarked
  have hBudget :
      (grantDrainLedgerStep ring fresh update s e label).remaining =
        min label.remaining
          (grantDrainLedgerQuotaCap n
            (grantDrainLedgerMarkNext ring fresh update s e label)
            (grantDrainLedgerHeld
              (grantDrainStep ring fresh update s e)
              (grantDrainLedgerHost ring fresh s e label.host))) := by
    change grantDrainLedgerRemainingNext n label
      (grantDrainLedgerHost ring fresh s e label.host)
      (grantDrainLedgerMarkNext ring fresh update s e label)
      (grantDrainLedgerNominatedHit ring s e label.host)
      (grantDrainLedgerHeld
        (grantDrainStep ring fresh update s e)
        (grantDrainLedgerHost ring fresh s e label.host)) = _
    have hHostRaw :
        grantDrainLedgerHost ring fresh s e label.host = some g :=
      hPostHost
    rw [hHostRaw, hNoHit]
    simp [grantDrainLedgerRemainingNext, hMark]
  refine ⟨hPostHost, ?_⟩
  rw [hBudget]
  exact grantDrainDeathMinPositive _ _ hPositive hCap

/-- Once the OLD mark is terminal, its permanent join never becomes
strong. A physical strong corridor after a leader death is compatible
with a persistent terminal ghost mark, but not a .terminal -> .strong
ghost transition. -/
theorem grantDrainDeathTerminalMarkPersists
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e : Fin n) (label : GrantDrainLedgerLabel n)
    (hTerminal : label.mark = .terminal) :
    (grantDrainLedgerStep ring fresh update s e label).mark =
      .terminal := by
  change grantDrainLedgerMarkNext ring fresh update s e label =
    .terminal
  unfold grantDrainLedgerMarkNext
  rw [hTerminal]
  cases hRest : grantDrainMarkJoin
      (grantDrainLedgerObservedMark ring s label.host)
      (grantDrainMarkJoin
        (grantDrainLedgerCoalesceMark ring s e label.host
          (grantDrainLedgerHost ring fresh s e label.host))
        (grantDrainLedgerObservedMark ring
          (grantDrainStep ring fresh update s e)
          (grantDrainLedgerHost ring fresh s e label.host))) <;>
    rfl

/-!
The following is a literal n=5 terminal-to-PHYSICAL-strong death
regression. The first weak-source witness had grant at site 4;
we put it at the old unshielded leader 3 instead. The same PPlus
LIVE at 2 kills leader 3 on edge [2]. Its old leader-hosted
unrequested grant moves 3 -> 2, where the protected leader 0
is the nearest preceding shielded source. The persistent mark
is terminal and its quota drops 5 -> 4.
-/

def grantDrainTerminalDeathFiveStart : GrantDrainState 5 Unit :=
  { grantDrainWeakDeathFiveStart with
    grant := fun i => i.val == 3 }

def grantDrainTerminalDeathFiveInitial : GrantDrainLedgerLabel 5 :=
  grantDrainLedgerInitial grantDrainWeakDeathFiveRing
    grantDrainTerminalDeathFiveStart (3 : Fin 5)

def grantDrainTerminalDeathFiveAfter : GrantDrainState 5 Unit :=
  grantDrainStep grantDrainWeakDeathFiveRing
    grantDrainWeakDeathFiveFresh grantDrainWeakDeathFiveScratch
    grantDrainTerminalDeathFiveStart (2 : Fin 5)

def grantDrainTerminalDeathFiveLabelAfter : GrantDrainLedgerLabel 5 :=
  grantDrainLedgerStep grantDrainWeakDeathFiveRing
    grantDrainWeakDeathFiveFresh grantDrainWeakDeathFiveScratch
    grantDrainTerminalDeathFiveStart (2 : Fin 5)
    grantDrainTerminalDeathFiveInitial

theorem grantDrainTerminalDeathFivePPlus :
    PPlus grantDrainWeakDeathFiveRing
      grantDrainTerminalDeathFiveStart.native := by
  exact grantDrainWeakDeathFivePPlus

/-- Exact edge, not a hypothetical post state. -/
theorem grantDrainTerminalDeathFiveWitness :
    grantDrainTerminalDeathFiveInitial.host = some (3 : Fin 5) ∧
    grantDrainTerminalDeathFiveInitial.mark = .terminal ∧
    grantDrainTerminalDeathFiveInitial.remaining = 5 ∧
    (grantDrainTerminalDeathFiveStart.native (2 : Fin 5)).b =
      (2 : Fin 3) ∧
    (grantDrainTerminalDeathFiveStart.native (3 : Fin 5)).l = true ∧
    (grantDrainTerminalDeathFiveAfter.native (3 : Fin 5)).l = false ∧
    grantDrainTerminalDeathFiveLabelAfter.host = some (2 : Fin 5) ∧
    grantDrainTerminalDeathFiveLabelAfter.mark = .terminal ∧
    grantDrainTerminalDeathFiveLabelAfter.remaining = 4 ∧
    grantDrainLedgerStrongLock grantDrainWeakDeathFiveRing
      grantDrainTerminalDeathFiveAfter (2 : Fin 5) = true := by
  unfold grantDrainTerminalDeathFiveInitial
    grantDrainTerminalDeathFiveStart
    grantDrainTerminalDeathFiveAfter
    grantDrainTerminalDeathFiveLabelAfter
  decide +kernel

/-- The n=5 death witness is a canonical-model one-letter word,
and its surviving physically strong terminal-marked label has
strictly positive reserve after the actual service. -/
theorem grantDrainTerminalDeathFiveCanonicalWord :
    grantDrainLedgerRun grantDrainWeakDeathFiveRing
      grantDrainWeakDeathFiveFresh grantDrainWeakDeathFiveScratch
      grantDrainTerminalDeathFiveStart grantDrainTerminalDeathFiveInitial
      [(2 : Fin 5)] =
    (grantDrainTerminalDeathFiveAfter,
      grantDrainTerminalDeathFiveLabelAfter) := by
  rfl

theorem grantDrainTerminalDeathFivePositive :
    0 < (grantDrainLedgerRun grantDrainWeakDeathFiveRing
      grantDrainWeakDeathFiveFresh grantDrainWeakDeathFiveScratch
      grantDrainTerminalDeathFiveStart grantDrainTerminalDeathFiveInitial
      [(2 : Fin 5)]).2.remaining := by
  rw [grantDrainTerminalDeathFiveCanonicalWord,
    grantDrainTerminalDeathFiveWitness.2.2.2.2.2.2.2.2.1]
  decide

end L3

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared
open L3.HeadlineRenewal

set_option autoImplicit false
set_option Elab.async false

/-!
The requested universal zero-BAD-LIVE => I entrance
is FALSE already for the empty scheduler word. The actual missing
step in D.5 is retirement of NONCLEAN DUMMY bullets after the
bad-LIVE cut and before scalar signal cleanup. No replacement
8*n^2 composition is asserted.
-/

/-- I itself is preserved under every actual canonical edge, even
when BAD-LIVE bullets still exist. Neither the E row theorem nor
the canonical-birth closure uses NoBadLive. -/
theorem grantDrainR8eIClosedOnCanonicalEdge
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hI : I ring s.native) :
    I ring (grantDrainStep ring fresh update s e).native := by
  have hLocal : GrantDrainEntranceILocal ring s.native :=
    (grantDrainEntranceIffILocal ring s.native).mp hI
  have hE : GrantDrainEntranceILocal ring
      (nativeE ring s.native e) :=
    grantDrainEntranceILocalNativeEAll ring
      (by omega : 3 ≤ n) s.native e hLocal
  have hNext : GrantDrainEntranceILocal ring
      (grantDrainStep ring fresh update s e).native :=
    grantDrainEntranceILocalPhysicalNextFromE
      ring fresh update s e hE
  exact grantDrainEntranceILocalImpliesI
    ring (grantDrainStep ring fresh update s e).native hNext

/-- Thus I is word-closed IF it holds at the original cut.
This is different from claiming that PPlus establishes I. -/
theorem grantDrainR8eIClosedOnCanonicalWord
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    ∀ (word : List (Fin n)) (s : GrantDrainState n Scratch),
      I ring s.native →
      I ring (grantDrainEntrancePhysicalWord
        ring fresh update s word).native := by
  intro word
  induction word with
  | nil =>
      intro s hI
      exact hI
  | cons e rest ih =>
      intro s hI
      change I ring
        (grantDrainEntrancePhysicalWord ring fresh update
          (grantDrainStep ring fresh update s e) rest).native
      exact ih (grantDrainStep ring fresh update s e)
        (grantDrainR8eIClosedOnCanonicalEdge
          ring hn fresh update s e hI)

/-- One leader at 0, two DUMMY bullets at 1 and 2 in the SAME
five-site leader sector, no LIVE bullet, all signals zero. -/
def grantDrainR8eUncleanCutRing : DirectedRing 5 :=
  ⟨by decide⟩

private def grantDrainR8eUncleanCutNative (i : Fin 5) : CertNative :=
  if i.val == 0 then
    { l := true, b := (0 : Fin 3), sh := false, sg := false }
  else if i.val == 1 then
    { l := false, b := (1 : Fin 3), sh := false, sg := false }
  else if i.val == 2 then
    { l := false, b := (1 : Fin 3), sh := false, sg := false }
  else
    { l := false, b := (0 : Fin 3), sh := false, sg := false }

/-- All physical grant/request bits are zero. In particular no
grant-funded birth is needed for the counterexample. -/
def grantDrainR8eUncleanCutState : GrantDrainState 5 Unit :=
  { native := grantDrainR8eUncleanCutNative
    request := fun _ => false
    grant := fun _ => false
    scratch := ()
    history := [] }

private theorem grantDrainR8eUncleanCutNoLive :
    ∀ v : Fin 5,
      ¬ LiveBullet grantDrainR8eUncleanCutNative v := by
  unfold LiveBullet grantDrainR8eUncleanCutNative
  decide +kernel

theorem grantDrainR8eUncleanCutProtected :
    PPlus grantDrainR8eUncleanCutRing
      grantDrainR8eUncleanCutState.native := by
  constructor
  · refine ⟨(0 : Fin 5), ?_⟩
    change (grantDrainR8eUncleanCutNative (0 : Fin 5)).l = true
    unfold grantDrainR8eUncleanCutNative
    decide +kernel
  · intro v hLive
    exact False.elim (grantDrainR8eUncleanCutNoLive v hLive)

theorem grantDrainR8eUncleanCutNoBad :
    GrantDrainEntranceNoBadLive grantDrainR8eUncleanCutRing
      grantDrainR8eUncleanCutState := by
  intro v hBad
  exact grantDrainR8eUncleanCutNoLive v hBad.1

/-- The unique leader's sector is the entire ring, offsets [0,5).
The finite checker is used only on this small, closed fact. -/
private theorem grantDrainR8eUncleanCutSector :
    sectorLength grantDrainR8eUncleanCutRing
      grantDrainR8eUncleanCutNative
      (0 : Fin 5) (5 : Fin 6) := by
  unfold sectorLength grantDrainR8eUncleanCutRing
    grantDrainR8eUncleanCutNative
  decide +kernel

private theorem grantDrainR8eUncleanCutFirstDummy :
    HasBullet grantDrainR8eUncleanCutNative
      (PPL.shiftRight grantDrainR8eUncleanCutRing
        (0 : Fin 5) (1 : Fin 5).val) := by
  unfold HasBullet grantDrainR8eUncleanCutNative
    grantDrainR8eUncleanCutRing
  decide +kernel

private theorem grantDrainR8eUncleanCutSecondDummy :
    HasBullet grantDrainR8eUncleanCutNative
      (PPL.shiftRight grantDrainR8eUncleanCutRing
        (0 : Fin 5) (2 : Fin 5).val) := by
  unfold HasBullet grantDrainR8eUncleanCutNative
    grantDrainR8eUncleanCutRing
  decide +kernel

/-- I's "at most one bullet per sector" clause forces 1 = 2.
This is the explicit obstruction, not an unproved proposition. -/
theorem grantDrainR8eUncleanCutNotI :
    ¬ I grantDrainR8eUncleanCutRing
      grantDrainR8eUncleanCutState.native := by
  intro hI
  have hUnique : (1 : Fin 5) = (2 : Fin 5) :=
    ((hI.2 (0 : Fin 5) (5 : Fin 6)
      grantDrainR8eUncleanCutSector).1
      (1 : Fin 5) (2 : Fin 5)
      (by decide : (1 : Fin 5).val < (5 : Fin 6).val)
      (by decide : (2 : Fin 5).val < (5 : Fin 6).val)
      grantDrainR8eUncleanCutFirstDummy
      grantDrainR8eUncleanCutSecondDummy)
  exact (by decide : (1 : Fin 5) ≠ (2 : Fin 5)) hUnique

/-- The R8d first-stage stopping predicate is already true at
time zero: every initial paper-bad LIVE ghost is absent. -/
private theorem grantDrainR8eUncleanCutDoneInitially :
    GrantDrainEntranceDone
      (grantDrainEntranceInitial grantDrainR8eUncleanCutRing
        grantDrainR8eUncleanCutState) := by
  left
  intro id
  change grantDrainEntranceBulletInitial
    grantDrainR8eUncleanCutRing grantDrainR8eUncleanCutState id = none
  unfold grantDrainEntranceBulletInitial
  simp [grantDrainR8eUncleanCutNoBad id]

/-- LITERAL counterexample: n=5, root 0, DUMMY sites 1 and 2,
zero grants and requests, scheduler word []. This is the FIRST
NoBadLive cut (time zero), and also the FIRST Done cut. I is false.
The run is the canonical source run, not an invented transition. -/
theorem grantDrainR8eFirstNoBadCutRefuted :
    PPlus grantDrainR8eUncleanCutRing
      grantDrainR8eUncleanCutState.native ∧
    GrantDrainEntranceDone
      (grantDrainEntranceInitial grantDrainR8eUncleanCutRing
        grantDrainR8eUncleanCutState) ∧
    GrantDrainEntranceNoBadLive grantDrainR8eUncleanCutRing
      (grantDrainEntrancePhysicalWord
        grantDrainR8eUncleanCutRing
        (fun _ _ => false) (fun _ _ => ())
        grantDrainR8eUncleanCutState ([] : List (Fin 5))) ∧
    ¬ I grantDrainR8eUncleanCutRing
      (grantDrainEntrancePhysicalWord
        grantDrainR8eUncleanCutRing
        (fun _ _ => false) (fun _ _ => ())
        grantDrainR8eUncleanCutState ([] : List (Fin 5))).native := by
  refine ⟨grantDrainR8eUncleanCutProtected,
    grantDrainR8eUncleanCutDoneInitially, ?_, ?_⟩
  · change GrantDrainEntranceNoBadLive
      grantDrainR8eUncleanCutRing grantDrainR8eUncleanCutState
    exact grantDrainR8eUncleanCutNoBad
  · change ¬ I grantDrainR8eUncleanCutRing
      grantDrainR8eUncleanCutState.native
    exact grantDrainR8eUncleanCutNotI

/-- It is not possible to repair the proposed universal proof by
choosing any pre-cut invariant J that contains ALL PPlus starts
and whose conjunction with NoBadLive forces I. Closure of J
would be an additional requirement, so the contradiction here
is strictly stronger than a failure of closure. -/
theorem grantDrainR8eNoUniversalPreCutInvariant :
    ¬ ∃ J : GrantDrainState 5 Unit → Prop,
      (∀ s, PPlus grantDrainR8eUncleanCutRing s.native → J s) ∧
      (∀ s, J s →
        GrantDrainEntranceNoBadLive grantDrainR8eUncleanCutRing s →
        I grantDrainR8eUncleanCutRing s.native) := by
  intro h
  rcases h with ⟨J, hContains, hSuffices⟩
  exact grantDrainR8eUncleanCutNotI
    (hSuffices grantDrainR8eUncleanCutState
      (hContains grantDrainR8eUncleanCutState
        grantDrainR8eUncleanCutProtected)
      grantDrainR8eUncleanCutNoBad)

end L3.GrantDrainEntrance

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-!
On the actual death service, a canonical F0 can birth a new
shielded leader at the killer, so the NEW first preceding leader
need not equal the OLD peaceful killer's shielded source.
The all-word result below covers marked labels before ANY nominated
hit, not the remaining all-hit R8 weak budget.
-/

def grantDrainDeathBornFiveStart : GrantDrainState 5 Unit :=
  { grantDrainWeakDeathFiveStart with
    request := fun i => i.val == 2
    grant := fun i => i.val == 2 || i.val == 4 }

def grantDrainDeathBornFiveAfter : GrantDrainState 5 Unit :=
  grantDrainStep grantDrainWeakDeathFiveRing
    grantDrainWeakDeathFiveFresh grantDrainWeakDeathFiveScratch
    grantDrainDeathBornFiveStart (2 : Fin 5)

def grantDrainDeathBornFiveLabel : GrantDrainLedgerLabel 5 :=
  grantDrainLedgerInitial grantDrainWeakDeathFiveRing
    grantDrainDeathBornFiveStart (4 : Fin 5)

def grantDrainDeathBornFiveLabelAfter :
    GrantDrainLedgerLabel 5 :=
  grantDrainLedgerStep grantDrainWeakDeathFiveRing
    grantDrainWeakDeathFiveFresh grantDrainWeakDeathFiveScratch
    grantDrainDeathBornFiveStart (2 : Fin 5)
    grantDrainDeathBornFiveLabel

theorem grantDrainDeathBornFivePPlus :
    PPlus grantDrainWeakDeathFiveRing
      grantDrainDeathBornFiveStart.native := by
  exact grantDrainWeakDeathFivePPlus

/-- OLD LIVE at 2 has first-left root 0 and a zero-signal
peaceful trail to it. -/
theorem grantDrainDeathBornFiveOldPeacefulSource :
    leaderSector grantDrainWeakDeathFiveRing
      grantDrainDeathBornFiveStart.native
      (0 : Fin 5) (2 : Fin 5) ∧
    signalTrail grantDrainWeakDeathFiveRing
      grantDrainDeathBornFiveStart.native
      (0 : Fin 5) (2 : Fin 5) ∧
    (grantDrainDeathBornFiveStart.native (0 : Fin 5)).sh = true := by
  unfold leaderSector signalTrail
    grantDrainDeathBornFiveStart
    grantDrainWeakDeathFiveStart
    grantDrainWeakDeathFiveNative
    grantDrainWeakDeathFiveRing
  decide +kernel

/-- A second initial identity at site 4 is WEAK, with cap 2n. -/
theorem grantDrainDeathBornFiveOldWeak :
    grantDrainDeathBornFiveLabel.host = some (4 : Fin 5) ∧
    grantDrainDeathBornFiveLabel.mark = .weak ∧
    grantDrainDeathBornFiveLabel.remaining = 10 ∧
    grantDrainLedgerWeakLock grantDrainWeakDeathFiveRing
      grantDrainDeathBornFiveStart (4 : Fin 5) = true := by
  unfold grantDrainDeathBornFiveLabel
    grantDrainLedgerInitial
    grantDrainDeathBornFiveStart
  decide +kernel

/-- Actual native-E death at 3; simultaneous canonical F0
makes the killer at 2 a shielded new leader. -/
theorem grantDrainDeathBornFiveActualFireAndDeath :
    grantDrainSelect grantDrainWeakDeathFiveRing
      grantDrainDeathBornFiveStart (2 : Fin 5) = .leftLocal ∧
    (grantDrainDeathBornFiveStart.native (3 : Fin 5)).l = true ∧
    (grantDrainDeathBornFiveStart.native (3 : Fin 5)).sh = false ∧
    (grantDrainDeathBornFiveAfter.native (3 : Fin 5)).l = false ∧
    (grantDrainDeathBornFiveAfter.native (2 : Fin 5)).l = true ∧
    (grantDrainDeathBornFiveAfter.native (2 : Fin 5)).sh = true ∧
    (grantDrainDeathBornFiveAfter.native (2 : Fin 5)).sg = false := by
  unfold grantDrainDeathBornFiveAfter
    grantDrainDeathBornFiveStart
    grantDrainWeakDeathFiveStart
    grantDrainWeakDeathFiveNative
    grantDrainWeakDeathFiveRing
    grantDrainStep
  decide +kernel

/-- Refutation of the unqualified post-first-source identity:
the old peaceful source is 0, the actual NEW first source
of surviving grant 4 is shielded site 2. -/
theorem grantDrainDeathBornFiveFirstSourceRefutesOldSource :
    grantDrainLeftLeaderDistance grantDrainWeakDeathFiveRing
      grantDrainDeathBornFiveAfter.native (4 : Fin 5) = 2 ∧
    PPL.shiftLeft grantDrainWeakDeathFiveRing (4 : Fin 5)
      (grantDrainLeftLeaderDistance grantDrainWeakDeathFiveRing
        grantDrainDeathBornFiveAfter.native (4 : Fin 5)) =
        (2 : Fin 5) ∧
    PPL.shiftLeft grantDrainWeakDeathFiveRing (4 : Fin 5)
      (grantDrainLeftLeaderDistance grantDrainWeakDeathFiveRing
        grantDrainDeathBornFiveAfter.native (4 : Fin 5)) ≠
        (0 : Fin 5) := by
  unfold grantDrainDeathBornFiveAfter
    grantDrainDeathBornFiveStart
    grantDrainWeakDeathFiveStart
    grantDrainWeakDeathFiveNative
    grantDrainWeakDeathFiveRing
  decide +kernel

/-- Even though the old source identity is not preserved,
the physical strong lock and positive remaining quota are real. -/
theorem grantDrainDeathBornFivePromotes :
    grantDrainDeathBornFiveLabelAfter.host = some (4 : Fin 5) ∧
    grantDrainDeathBornFiveLabelAfter.mark = .strong ∧
    grantDrainDeathBornFiveLabelAfter.remaining = 5 ∧
    grantDrainLedgerStrongLock grantDrainWeakDeathFiveRing
      grantDrainDeathBornFiveAfter (4 : Fin 5) = true := by
  unfold grantDrainDeathBornFiveLabelAfter
    grantDrainDeathBornFiveLabel
    grantDrainDeathBornFiveStart
    grantDrainDeathBornFiveAfter
    grantDrainWeakDeathFiveStart
    grantDrainWeakDeathFiveNative
    grantDrainWeakDeathFiveRing
  decide +kernel

theorem grantDrainDeathBornFiveCanonicalEdge :
    (GrantDrainShared.grantDrainCanonicalModel
      grantDrainWeakDeathFiveRing (by decide : 5 ≤ 5)
      grantDrainWeakDeathFiveFresh
      grantDrainWeakDeathFiveScratch).step
      grantDrainDeathBornFiveStart (2 : Fin 5) =
        grantDrainDeathBornFiveAfter := by
  rfl

theorem grantDrainDeathBornFiveCanonicalWord :
    grantDrainLedgerRun grantDrainWeakDeathFiveRing
      grantDrainWeakDeathFiveFresh grantDrainWeakDeathFiveScratch
      grantDrainDeathBornFiveStart grantDrainDeathBornFiveLabel
      [(2 : Fin 5)] =
        (grantDrainDeathBornFiveAfter,
          grantDrainDeathBornFiveLabelAfter) := by
  rfl

/-- Positive marked quota survives one NON-nominated edge if the
host survives. This includes cap shrinking weak 2n to strong n. -/
theorem grantDrainMarkedNoHitStepPositive
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hMarked : label.mark ≠ .unmarked)
    (hPositive : 0 < label.remaining)
    (hNoHit :
      grantDrainLedgerNominatedHit ring s e label.host = false)
    (hLive :
      (grantDrainLedgerStep ring fresh update s e label).host ≠ none) :
    0 < (grantDrainLedgerStep ring fresh update s e label).remaining := by
  have hNextMarked :
      grantDrainLedgerMarkNext ring fresh update s e label ≠ .unmarked :=
    grantDrainLedgerMarkedNextStillMarked
      ring fresh update s e label hMarked
  have hCap :
      0 < grantDrainLedgerQuotaCap n
        (grantDrainLedgerMarkNext ring fresh update s e label)
        (grantDrainLedgerHeld
          (grantDrainStep ring fresh update s e)
          (grantDrainLedgerHost ring fresh s e label.host)) :=
    grantDrainDeathMarkedCapPositive n hn _ _ hNextMarked
  have hBudget :
      (grantDrainLedgerStep ring fresh update s e label).remaining =
        min label.remaining
          (grantDrainLedgerQuotaCap n
            (grantDrainLedgerMarkNext ring fresh update s e label)
            (grantDrainLedgerHeld
              (grantDrainStep ring fresh update s e)
              (grantDrainLedgerHost ring fresh s e label.host))) := by
    change grantDrainLedgerRemainingNext n label
      (grantDrainLedgerHost ring fresh s e label.host)
      (grantDrainLedgerMarkNext ring fresh update s e label)
      (grantDrainLedgerNominatedHit ring s e label.host)
      (grantDrainLedgerHeld
        (grantDrainStep ring fresh update s e)
        (grantDrainLedgerHost ring fresh s e label.host)) = _
    cases hh : grantDrainLedgerHost ring fresh s e label.host with
    | none =>
        exact False.elim (hLive hh)
    | some g =>
        rw [hNoHit]
        simp [grantDrainLedgerRemainingNext, hMarked]
  rw [hBudget]
  exact grantDrainDeathMinPositive _ _ hPositive hCap

/-- Retirement of a raw source-ledger host is absorbing on words,
without assuming a zero old remaining counter. -/
theorem grantDrainLedgerRetiredHostWord
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    ∀ (word : List (Fin n))
      (s : GrantDrainState n Scratch)
      (label : GrantDrainLedgerLabel n),
      label.host = none →
      (grantDrainLedgerRun ring fresh update s label word).2.host =
        none := by
  intro word
  induction word with
  | nil =>
      intro s label h
      exact h
  | cons e es ih =>
      intro s label h
      change
        (grantDrainLedgerRun ring fresh update
          (grantDrainStep ring fresh update s e)
          (grantDrainLedgerStep ring fresh update s e label) es).2.host =
          none
      exact ih _ _ (grantDrainLedgerStep_retired_absorbing
        ring fresh update s e label h)

/-- No nominated edge in any prefix, tested against each exact
OLD source state and each persistent label at that prefix. -/
def GrantDrainNoNominatedWord
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (label : GrantDrainLedgerLabel n) :
    List (Fin n) → Prop
  | [] => True
  | e :: es =>
      grantDrainLedgerNominatedHit ring s e label.host = false ∧
      GrantDrainNoNominatedWord ring fresh update
        (grantDrainStep ring fresh update s e)
        (grantDrainLedgerStep ring fresh update s e label) es

/-- A surviving marked identity cannot exhaust on an arbitrary
word that never selected its nominated edge. -/
theorem grantDrainMarkedNoHitWordPositive
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    ∀ (word : List (Fin n))
      (s : GrantDrainState n Scratch)
      (label : GrantDrainLedgerLabel n),
      label.mark ≠ .unmarked →
      0 < label.remaining →
      GrantDrainNoNominatedWord ring fresh update s label word →
      (grantDrainLedgerRun ring fresh update s label word).2.host ≠
        none →
      0 <
        (grantDrainLedgerRun ring fresh update s label word).2.remaining := by
  intro word
  induction word with
  | nil =>
      intro s label hMarked hPositive hNoHit hLive
      exact hPositive
  | cons e es ih =>
      intro s label hMarked hPositive hNoHit hLive
      change
        grantDrainLedgerNominatedHit ring s e label.host = false ∧
        GrantDrainNoNominatedWord ring fresh update
          (grantDrainStep ring fresh update s e)
          (grantDrainLedgerStep ring fresh update s e label) es at hNoHit
      change
        (grantDrainLedgerRun ring fresh update
          (grantDrainStep ring fresh update s e)
          (grantDrainLedgerStep ring fresh update s e label)
          es).2.host ≠ none at hLive
      have hNextLive :
          (grantDrainLedgerStep ring fresh update s e label).host ≠ none := by
        intro hGone
        exact hLive (grantDrainLedgerRetiredHostWord
          ring fresh update es
          (grantDrainStep ring fresh update s e)
          (grantDrainLedgerStep ring fresh update s e label)
          hGone)
      have hNextMarked :=
        grantDrainLedgerMarkedNextStillMarked
          ring fresh update s e label hMarked
      have hNextPositive :=
        grantDrainMarkedNoHitStepPositive
          ring hn fresh update s e label
          hMarked hPositive hNoHit.1 hNextLive
      change
        0 < (grantDrainLedgerRun ring fresh update
          (grantDrainStep ring fresh update s e)
          (grantDrainLedgerStep ring fresh update s e label)
          es).2.remaining
      exact ih _ _ hNextMarked hNextPositive hNoHit.2 hLive

/-- Initially occupied marked identities have positive quota. -/
theorem grantDrainInitialMarkedQuotaPositive
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (i : Fin n)
    (hGrant : s.grant i = true)
    (hMarked :
      (grantDrainLedgerInitial ring s i).mark ≠ .unmarked) :
    0 < (grantDrainLedgerInitial ring s i).remaining := by
  have hObserved :
      grantDrainLedgerObservedMark ring s (some i) ≠ .unmarked := by
    simpa [grantDrainLedgerInitial, hGrant] using hMarked
  have hCap := grantDrainDeathMarkedCapPositive
    n hn (grantDrainLedgerObservedMark ring s (some i))
    (grantDrainLedgerHeld s (some i)) hObserved
  simpa [grantDrainLedgerInitial, hGrant] using hCap

/-- The n>=5 PPlus initial WEAK label retains positive quota over
every canonical NO-HIT word with a surviving final host.
The general repeated-hit lower bound remains unproved. -/
theorem grantDrainPPlusWeakNoHitPrefix
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (i : Fin n) (word : List (Fin n))
    (hP : PPlus ring s.native)
    (hGrant : s.grant i = true)
    (hWeak : (grantDrainLedgerInitial ring s i).mark = .weak)
    (hNoHit :
      GrantDrainNoNominatedWord ring fresh update s
        (grantDrainLedgerInitial ring s i) word)
    (hLive :
      (grantDrainLedgerRun ring fresh update s
        (grantDrainLedgerInitial ring s i) word).2.host ≠ none) :
    0 < (grantDrainLedgerRun ring fresh update s
      (grantDrainLedgerInitial ring s i) word).2.remaining := by
  have hMarked :
      (grantDrainLedgerInitial ring s i).mark ≠ .unmarked := by
    rw [hWeak]
    decide
  have hInitialPositive :=
    grantDrainInitialMarkedQuotaPositive
      ring hn s i hGrant hMarked
  exact grantDrainMarkedNoHitWordPositive
    ring hn fresh update word s (grantDrainLedgerInitial ring s i)
    hMarked hInitialPositive hNoHit hLive

end L3
