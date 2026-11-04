import Leader.PPL.ReachCPB.MismatchHistFreshCoherent
import Init.Omega

namespace PPL.Convergence.ReachCPB

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL
open PPL.Probability

/-!
There are two separate negative facts.

(1) The literal "completed iff there is a live terminal owner" invariant is
false even on a canonical ghostRun.  bumpTo appends the terminal metadata to
done when moves becomes exactly tokenTrajectoryMoves, but the live output is
independently filtered by tcLocalValid.  Thus the terminal hop can log a
completion and kill the live owner in the same step.

The weaker statements
  * no completion before the exact terminal move, and
  * at most one completion per lineage ID
are not logically equivalent to that iff.  This file does not refute those
weaker once-only statements.

(2) More importantly for L16,
Lemma16PostEpochFreshNewCompletionStepGeomCoherent itself is false, even when
G is a canonical ghostRun prefix and therefore satisfies the lineage
coherence theorem.  The witness below has n = 6, psi = 2, kappa = 1.

Physical fields at the epoch:
  site :  0  1  2  3  4  5
  dist :  0  1  2  3  1  0
  id   :  0  0  1  0  1  0

Start token-free and use the canonical prefix schedule [0,1,1,1].
The fresh black lineage born at site 0 then sits at site 2 with:
  id        = .born .black 0
  birthSite = 0
  birthStep = 0
  moves     = 4
  offset    = +1
  bit       = 0
  carry     = 0.

Here k = 0 and b = 2 = shiftRight k psi.  The source segment has length 2
and value 0.  But the next border after b is site 5, at distance 3, so the
target segment has bits [1,0,1] and value 5.  Hence the bad-border witness is
5 ≠ (0 + 1) % 4.

The final interaction e = 2 compares the terminal black bit 0 with site 3's
id bit 0, so it is a match: no leader is born.  The ghost bump is 4 -> 5,
so the completion is logged.  The bounced negative ghost is locally invalid
at site 3 and is deleted, giving the completed-without-live-owner witness as
well.

All finite facts below are kernel-reducible with decide; no native_decide,
sorry, by_contra, axiom, or implementation-private name is used.
-/

private theorem q19985Hpsi : 2 ≤ 2 := by
  omega

private theorem q19985Hn3 : 3 ≤ 6 := by
  omega

private def q19985Ring : DirectedRing 6 :=
  ⟨by decide⟩

private def q19985E0 : Fin 6 := ⟨0, by decide⟩
private def q19985E1 : Fin 6 := ⟨1, by decide⟩
private def q19985E2 : Fin 6 := ⟨2, by decide⟩
private def q19985E3 : Fin 6 := ⟨3, by decide⟩
private def q19985E4 : Fin 6 := ⟨4, by decide⟩
private def q19985E5 : Fin 6 := ⟨5, by decide⟩

private def q19985Dist (i : Fin 6) : Fin 4 :=
  if i = q19985E0 then
    (0 : Fin 4)
  else if i = q19985E1 then
    (1 : Fin 4)
  else if i = q19985E2 then
    (2 : Fin 4)
  else if i = q19985E3 then
    (3 : Fin 4)
  else if i = q19985E4 then
    (1 : Fin 4)
  else
    (0 : Fin 4)

private def q19985Id (i : Fin 6) : Bool :=
  if i = q19985E2 ∨ i = q19985E4 then true else false

private def q19985State (i : Fin 6) : PPL.State 2 1 :=
  {
    leader := false
    id := q19985Id i
    dist := q19985Dist i
    last := false
    tokenB := none
    tokenW := none
    mode := true
    clock := (1 : Fin 2)
    signalR := 0
    hits := 0
    bullet := 0
    shield := false
    signalB := false
  }

private def q19985C0 : Config 6 2 1 :=
  q19985State

private def q19985Pre : DetSchedule 6 :=
  [q19985E0, q19985E1, q19985E1, q19985E1]

private def q19985Full : DetSchedule 6 :=
  [q19985E0, q19985E1, q19985E1, q19985E1, q19985E2]

private noncomputable def q19985G : PPL.GhostConfig 6 2 1 :=
  PPL.ghostRun q19985Hpsi q19985Ring 0
    (PPL.initialGhost q19985C0) q19985Pre

private noncomputable def q19985FullG : PPL.GhostConfig 6 2 1 :=
  PPL.ghostRun q19985Hpsi q19985Ring 0
    (PPL.initialGhost q19985C0) q19985Full

private def q19985Token : PPL.TokenData 2 :=
  ((PPL.offsetOneCode 2 q19985Hpsi, (0 : Fin 2)), (0 : Fin 2))

private def q19985Z : PPL.GhostToken 6 2 :=
  {
    value := q19985Token
    lmeta :=
      {
        id := .born .black 0
        birthSite := q19985E0
        birthStep := 0
        moves := 4
      }
  }

private def q19985M : PPL.LineageMeta 6 :=
  {
    id := .born .black 0
    birthSite := q19985E0
    birthStep := 0
    moves := 5
  }

private theorem q19985Fin6Cases (i : Fin 6) :
    i = q19985E0 ∨
    i = q19985E1 ∨
    i = q19985E2 ∨
    i = q19985E3 ∨
    i = q19985E4 ∨
    i = q19985E5 := by
  by_cases h0 : i.val = 0
  · left
    apply Fin.ext
    simpa [q19985E0] using h0
  · by_cases h1 : i.val = 1
    · right
      left
      apply Fin.ext
      simpa [q19985E1] using h1
    · by_cases h2 : i.val = 2
      · right
        right
        left
        apply Fin.ext
        simpa [q19985E2] using h2
      · by_cases h3 : i.val = 3
        · right
          right
          right
          left
          apply Fin.ext
          exact h3
        · by_cases h4 : i.val = 4
          · right
            right
            right
            right
            left
            apply Fin.ext
            exact h4
          · have h5 : i.val = 5 := by
              omega
            right
            right
            right
            right
            right
            apply Fin.ext
            exact h5

private theorem q19985PreBlackAt (i : Fin 6) :
    PPL.ghostTokenAt .black q19985G i =
      if i = q19985E2 then some q19985Z else none := by
  rcases q19985Fin6Cases i with
    h0 | h1 | h2 | h3 | h4 | h5
  · subst i
    decide
  · subst i
    decide
  · subst i
    decide
  · subst i
    decide
  · subst i
    decide
  · subst i
    decide

private theorem q19985OwnerShape
    {i : Fin 6} {z : PPL.GhostToken 6 2}
    (h :
      PPL.ghostTokenAt .black q19985G i = some z) :
    i = q19985E2 ∧ z = q19985Z := by
  by_cases hi : i = q19985E2
  · subst i
    have hrow := q19985PreBlackAt q19985E2
    simp only [if_pos rfl] at hrow
    rw [hrow] at h
    exact ⟨rfl, (Option.some.inj h).symm⟩
  · have hrow := q19985PreBlackAt i
    simp only [if_neg hi] at hrow
    rw [hrow] at h
    cases h

private theorem q19985FrozenId (i : Fin 6) :
    (q19985G.phys i).id = (q19985C0 i).id := by
  rcases q19985Fin6Cases i with
    h0 | h1 | h2 | h3 | h4 | h5
  · subst i
    decide
  · subst i
    decide
  · subst i
    decide
  · subst i
    decide
  · subst i
    decide
  · subst i
    decide

private theorem q19985TokenOffset :
    PPL.decodeOffset 2 (PPL.tokenCode q19985Token) = (1 : Int) := by
  decide

private theorem q19985Macro :
    Lemma16FreshMacroStageAt
      q19985Ring q19985E0 q19985E2 q19985Z 1 := by
  unfold Lemma16FreshMacroStageAt
  dsimp only
  refine ⟨2, ?_, ?_⟩
  · decide
  · have hoff :
        PPL.decodeOffset 2
            (PPL.tokenCode q19985Z.value) =
          (1 : Int) := by
      simpa [q19985Z] using q19985TokenOffset
    rw [hoff]
    left
    simp [q19985Z]

private theorem q19985Payload :
    PPL.payloadCorrect
      q19985Ring q19985C0 q19985E0 1 q19985Token := by
  decide

private theorem q19985Prefix :
    Lemma16TargetPrefix
      q19985Ring q19985C0 q19985E2 q19985E0 1 := by
  unfold Lemma16TargetPrefix
  intro x hx
  have hx0 : x = 0 := by
    omega
  subst x
  decide

private theorem q19985Coherent :
    Lemma16GhostLineageCoherent q19985G := by
  have hprod : Lemma16GhostLineageCoherentRunProducer :=
    lemma16GhostLineageCoherentRunProducer_proved
  unfold Lemma16GhostLineageCoherentRunProducer at hprod
  simpa [q19985G] using
    hprod q19985Hpsi q19985Ring q19985C0 q19985Pre

private theorem q19985Geometry :
    Lemma16PostEpochFreshBorderGeometry
      q19985Ring q19985E2 q19985E0 2 := by
  unfold Lemma16PostEpochFreshBorderGeometry
  decide

private theorem q19985Ready :
    DetectReadyCapped q19985Ring q19985G.phys := by
  decide

private theorem q19985StateInvariant :
    Lemma16PostEpochFreshStateInvariant
      q19985Ring q19985C0 0
      q19985E2 q19985E0 .black q19985G := by
  unfold Lemma16PostEpochFreshStateInvariant
  refine ⟨?_, ?_⟩
  · intro i
    exact q19985FrozenId i
  · unfold Lemma16PostEpochFreshLiveInvariant
    intro i z t howner hid _hsite _hepoch _hprior
    rcases q19985OwnerShape howner with ⟨rfl, rfl⟩
    have ht : t = 0 := by
      change
        PPL.LineageId.born .black 0 =
          PPL.LineageId.born .black t at hid
      cases hid
      rfl
    subst t
    refine
      ⟨1, by omega, q19985Macro,
        q19985Payload, q19985Prefix, ?_⟩
    intro hneg
    have hoff :
        PPL.decodeOffset 2
            (PPL.tokenCode q19985Z.value) =
          (1 : Int) := by
      simpa [q19985Z] using q19985TokenOffset
    rw [hoff] at hneg
    omega

private theorem q19985History :
    ∀ (i : Fin 6)
      (z : PPL.GhostToken 6 2)
      (t : Nat),
      PPL.ghostTokenAt .black q19985G i = some z →
      z.lmeta.id = .born .black t →
      z.lmeta.birthSite = q19985E0 →
      0 ≤ z.lmeta.birthStep := by
  intro _i z _t _howner _hid _hsite
  exact Nat.zero_le z.lmeta.birthStep

set_option maxRecDepth 200000 in
set_option maxHeartbeats 60000000 in
private theorem q19985Bad :
    Lemma16BadBorderWitness
      q19985Ring q19985G.phys
      q19985E2 q19985E0 .black := by
  unfold Lemma16BadBorderWitness PPL.IsBorder PPL.Cd
  dsimp only
  decide

private theorem q19985Fresh :
    PPL.FreshCompletion
      (psi := 2) .black q19985E0 q19985M := by
  unfold PPL.FreshCompletion PPL.FreshAt
  refine ⟨⟨0, rfl, rfl⟩, ?_⟩
  decide

private theorem q19985PreCompleted :
    q19985G.completed = [] := by
  decide

private theorem q19985NotOld :
    q19985M ∉ q19985G.completed := by
  rw [q19985PreCompleted]
  simp

private theorem q19985PostCompleted :
    (PPL.ghostStep
      q19985Hpsi q19985Ring 4
      q19985G q19985E2).completed =
        [q19985M] := by
  decide

private theorem q19985PostMember :
    q19985M ∈
      (PPL.ghostStep
        q19985Hpsi q19985Ring 4
        q19985G q19985E2).completed := by
  rw [q19985PostCompleted]
  simp

private theorem q19985PostNotCPB :
    ¬ PPL.CPB q19985Ring
      (PPL.ghostStep
        q19985Hpsi q19985Ring 4
        q19985G q19985E2).phys := by
  decide

/-!
Literal form of the iff.  It deliberately asks for a
current live owner on the right-hand side.  The next theorem refutes it on
the five-step canonical run.
-/
def Lemma16CompletedIffLiveTerminal
    {n psi kappa : Nat}
    (G : PPL.GhostConfig n psi kappa) : Prop :=
  ∀ x : PPL.LineageId n,
    (∃ m : PPL.LineageMeta n,
      m ∈ G.completed ∧ m.id = x) ↔
    ∃ (kind : PPL.TokenKind)
      (i : Fin n)
      (z : PPL.GhostToken n psi),
      PPL.ghostTokenAt kind G i = some z ∧
      z.lmeta.id = x ∧
      PPL.tokenTrajectoryMoves psi ≤ z.lmeta.moves

private theorem q19985FullCoherent :
    Lemma16GhostLineageCoherent q19985FullG := by
  have hprod : Lemma16GhostLineageCoherentRunProducer :=
    lemma16GhostLineageCoherentRunProducer_proved
  unfold Lemma16GhostLineageCoherentRunProducer at hprod
  simpa [q19985FullG] using
    hprod q19985Hpsi q19985Ring q19985C0 q19985Full

private theorem q19985FullCompleted :
    q19985FullG.completed = [q19985M] := by
  decide

private theorem q19985FullMember :
    q19985M ∈ q19985FullG.completed := by
  rw [q19985FullCompleted]
  simp

private theorem q19985FullBlackNone (i : Fin 6) :
    PPL.ghostTokenAt .black q19985FullG i = none := by
  rcases q19985Fin6Cases i with
    h0 | h1 | h2 | h3 | h4 | h5
  · subst i
    decide
  · subst i
    decide
  · subst i
    decide
  · subst i
    decide
  · subst i
    decide
  · subst i
    decide

private theorem q19985FullNoLiveCompletedId :
    ¬ ∃ (kind : PPL.TokenKind)
      (i : Fin 6)
      (z : PPL.GhostToken 6 2),
      PPL.ghostTokenAt kind q19985FullG i = some z ∧
      z.lmeta.id = q19985M.id := by
  intro h
  rcases h with ⟨kind, i, z, howner, hid⟩
  have hid' :
      z.lmeta.id = .born .black 0 := by
    simpa [q19985M] using hid
  have hcoh :=
    q19985FullCoherent kind .black i z 0 howner hid'
  have hkind : kind = .black := hcoh.1
  subst kind
  have hnone := q19985FullBlackNone i
  rw [hnone] at howner
  cases howner

/--
Canonical counterexample to the literal iff invariant.

The completed record exists, but the terminal bounce is locally invalid and
there is no current live owner carrying that lineage ID.
-/
theorem lemma16CompletedIffLiveTerminal_refuted_q19985 :
    ¬ Lemma16CompletedIffLiveTerminal q19985FullG := by
  intro hiff
  have hcompleted :
      ∃ m : PPL.LineageMeta 6,
        m ∈ q19985FullG.completed ∧
        m.id = q19985M.id :=
    ⟨q19985M, q19985FullMember, rfl⟩
  have hlive :=
    (hiff q19985M.id).mp hcompleted
  rcases hlive with
    ⟨kind, i, z, howner, hid, _hmoves⟩
  exact
    q19985FullNoLiveCompletedId
      ⟨kind, i, z, howner, hid⟩

/--
Canonical counterexample to the proposed coherent terminal row.

The pre-state q19985G is itself ghostRun(initialGhost q19985C0)
[q19985E0,q19985E1,q19985E1,q19985E1], so the earlier coherence invariant supplies coherence.
All remaining hypotheses are checked above.  The final e=2 interaction logs
q19985M but creates no leader, while q19985Bad remains a genuine bad-border
witness because the target border is three sites away.
-/
theorem
    lemma16PostEpochFreshNewCompletionStepGeomCoherent_refuted_q19985 :
    ¬ Lemma16PostEpochFreshNewCompletionStepGeomCoherent := by
  intro hrow
  unfold
    Lemma16PostEpochFreshNewCompletionStepGeomCoherent
    at hrow
  have hs :=
    hrow
      (n := 6) (psi := 2) (kappa := 1)
      q19985Hpsi q19985Hn3
      q19985Ring q19985C0 0
      q19985E2 q19985E0 .black
      4 q19985G q19985E2
      q19985Coherent
      q19985Geometry
      q19985Ready
      q19985StateInvariant
  dsimp only at hs
  rcases hs with hcpb | hterminal
  · exact q19985PostNotCPB hcpb
  · exact
      hterminal
        q19985M
        q19985PostMember
        q19985Fresh
        q19985NotOld
        q19985History
        q19985Bad

end PPL.Convergence.ReachCPB

#print axioms PPL.Convergence.ReachCPB.lemma16CompletedIffLiveTerminal_refuted_q19985
#print axioms PPL.Convergence.ReachCPB.lemma16PostEpochFreshNewCompletionStepGeomCoherent_refuted_q19985
