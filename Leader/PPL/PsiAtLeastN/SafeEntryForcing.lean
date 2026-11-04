import Leader.PPL.SPLEntry.GappedPhases
import Leader.PPL.SPLEntry.ForcingWord
import Leader.PPL.Probability.FixedWord

/-!
# Lemma 18 with the safe target, for every `psi` (F.1b, part c)

The Lemma-18 forcing word `l18Word ring root psi` is the concatenation of
five phases: root reset, distance sweep, last sweep, risky flush and the
Lemma-4 build blocks.  Only the risky-flush phase needs `psi < n`
(`L18GappedRiskyFlushPhaseScoped`); the first three phases are proved for
every `psi` (`l18GappedRootResetPhase_proved`,
`l18GappedDistanceSweepPhase_proved`, `l18GappedLastSweepPhase_proved`), and
each ends in "a prefix of the `P_PL'` run is in `S_PL` at `root`" or
"the endpoint is `C_DL` at `root`".

This file composes those three phases with the rooted safe hit

  `SPLAt ring root C ∨ CDLAt ring root C`

(which, when `segmentCount n psi = 1`, is the rooted Theorem-1 safe target)
and derives the Lemma-18 counting tail for it with no hypothesis on `psi`:

* `l18HitsSafe`: first-hit Boolean for the rooted safe hit along a `P_PL'`
  word (every prefix endpoint, including both ends, is tested);
* `l18ForcingWordReachesSafe`: if `l18Word ring root psi` occurs as an
  ordered subsequence of the schedule, the `P_PL'` run from a `C_PB`
  configuration with unique leader `root` hits the rooted safe predicate;
* `n_mul_l18SafeFailureCount_le_pow`: the fixed-word count, so at most a
  `1/n` fraction of the `l18Horizon n psi`-letter words miss it.
-/

namespace PPL.PsiAtLeastN

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL
open PPL.Convergence.L18

/-- Rooted safe hit: rooted `S_PL` or rooted `C_DL`. -/
def L18SafeAt {n psi kappa : Nat} (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa) : Prop :=
  Or (SPLAt ring root C) (CDLAt ring root C)

instance instDecidableL18SafeAt {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n) (C : Config n psi kappa) :
    Decidable (L18SafeAt ring root C) := by
  unfold L18SafeAt
  infer_instance

/-- First-hit Boolean for the rooted safe hit along a `P_PL'` word.  Same
shape as `l18HitsSPL`. -/
def l18HitsSafe {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    Config n psi kappa → DetSchedule n → Bool
  | C, [] =>
      decide (L18SafeAt ring root C)
  | C, e :: es =>
      decide (L18SafeAt ring root C) ||
        l18HitsSafe ring root (pprimeStep ring C e) es

/-! ## Transport lemmas -/

/-- An `S_PL` first hit is a safe first hit. -/
theorem l18HitsSafe_of_hitsSPL
    {n psi kappa : Nat} (ring : DirectedRing n) (root : Fin n) :
    ∀ (C : Config n psi kappa) (w : DetSchedule n),
      l18HitsSPL ring root C w = true →
        l18HitsSafe ring root C w = true := by
  intro C w
  induction w generalizing C with
  | nil =>
      intro h
      have hs : SPLAt ring root C := by
        simpa [l18HitsSPL] using h
      simp [l18HitsSafe, L18SafeAt, hs]
  | cons e es ih =>
      intro h
      cases hs : decide (SPLAt ring root C) with
      | true =>
          have hs' : SPLAt ring root C := of_decide_eq_true hs
          simp [l18HitsSafe, L18SafeAt, hs']
      | false =>
          have htail :
              l18HitsSPL ring root (pprimeStep ring C e) es = true := by
            simpa [l18HitsSPL, hs] using h
          have := ih (pprimeStep ring C e) htail
          simp [l18HitsSafe, this]

/-- A first hit in a prefix remains a first hit after any suffix. -/
theorem l18HitsSafe_append_left
    {n psi kappa : Nat} (ring : DirectedRing n) (root : Fin n) :
    ∀ (C : Config n psi kappa) (u v : DetSchedule n),
      l18HitsSafe ring root C u = true →
        l18HitsSafe ring root C (u ++ v) = true := by
  intro C u v
  induction u generalizing C with
  | nil =>
      intro h
      cases v with
      | nil => simpa using h
      | cons e es =>
          have hs : decide (L18SafeAt ring root C) = true := by
            simpa [l18HitsSafe] using h
          simp [l18HitsSafe, hs]
  | cons e es ih =>
      intro h
      cases hs : decide (L18SafeAt ring root C) with
      | false =>
          have htail :
              l18HitsSafe ring root (pprimeStep ring C e) es = true := by
            simpa [l18HitsSafe, hs] using h
          have hout := ih (pprimeStep ring C e) htail
          simpa [l18HitsSafe, hs] using hout
      | true =>
          simp [l18HitsSafe, hs]

/-- A first hit in the suffix, started from the prefix endpoint, is a first
hit of the concatenation. -/
theorem l18HitsSafe_append_right
    {n psi kappa : Nat} (ring : DirectedRing n) (root : Fin n) :
    ∀ (C : Config n psi kappa) (u v : DetSchedule n),
      l18HitsSafe ring root (runPPrime ring C u) v = true →
        l18HitsSafe ring root C (u ++ v) = true := by
  intro C u v
  induction u generalizing C with
  | nil =>
      intro h
      simpa [runPPrime] using h
  | cons e es ih =>
      intro h
      cases hs : decide (L18SafeAt ring root C) with
      | false =>
          have htail :
              l18HitsSafe ring root
                  (runPPrime ring (pprimeStep ring C e) es) v = true := by
            simpa [runPPrime] using h
          have hout := ih (pprimeStep ring C e) htail
          simpa [l18HitsSafe, hs] using hout
      | true =>
          simp [l18HitsSafe, hs]

/-- A safe endpoint is a hit of the word (the base case tests the final
configuration). -/
theorem l18HitsSafe_of_endpoint
    {n psi kappa : Nat} (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa) (u : DetSchedule n)
    (h : L18SafeAt ring root (runPPrime ring C u)) :
    l18HitsSafe ring root C u = true := by
  have hnil : l18HitsSafe ring root (runPPrime ring C u) [] = true := by
    simp [l18HitsSafe, h]
  simpa using l18HitsSafe_append_right ring root C u [] hnil

/-- A safe first hit is witnessed by a prefix whose `P_PL'` endpoint is
rooted safe. -/
theorem l18HitsSafe_exists_prefix
    {n psi kappa : Nat} (ring : DirectedRing n) (root : Fin n) :
    ∀ (C : Config n psi kappa) (w : DetSchedule n),
      l18HitsSafe ring root C w = true →
        ∃ pre suf : DetSchedule n,
          w = pre ++ suf ∧ L18SafeAt ring root (runPPrime ring C pre) := by
  intro C w
  induction w generalizing C with
  | nil =>
      intro h
      have hs : L18SafeAt ring root C := by
        simpa [l18HitsSafe] using h
      exact ⟨[], [], rfl, hs⟩
  | cons e rest ih =>
      intro h
      cases hnow : decide (L18SafeAt ring root C) with
      | true =>
          exact ⟨[], e :: rest, by simp,
            by simpa [runPPrime] using of_decide_eq_true hnow⟩
      | false =>
          have htail :
              l18HitsSafe ring root (pprimeStep ring C e) rest = true := by
            simpa [l18HitsSafe, hnow] using h
          obtain ⟨pre, suf, hrest, hs⟩ := ih (pprimeStep ring C e) htail
          exact ⟨e :: pre, suf, by simp [hrest],
            by simpa [runPPrime] using hs⟩

/-! ## Ordered-subsequence split -/

/-- Split an ordered occurrence of `a ++ b` at some scheduler cut (copy of
the private `l18GappedSublistAppendSplit`). -/
theorem sublist_append_split
    {A : Type} (a b w : List A) (hsub : (a ++ b).Sublist w) :
    ∃ u v : List A, w = u ++ v ∧ a.Sublist u ∧ b.Sublist v := by
  induction w generalizing a with
  | nil =>
      cases a with
      | nil =>
          refine ⟨[], [], rfl, List.Sublist.slnil, ?_⟩
          simpa using hsub
      | cons x xs =>
          have hlen := hsub.length_le
          simp at hlen
  | cons y ys ih =>
      cases a with
      | nil =>
          refine ⟨[], y :: ys, rfl, List.Sublist.slnil, ?_⟩
          simpa using hsub
      | cons x xs =>
          have hs : (x :: (xs ++ b)).Sublist (y :: ys) := by
            simpa only [List.cons_append] using hsub
          rcases List.sublist_cons_iff.mp hs with
            hskip | ⟨tail, heq, htake⟩
          · rcases ih (a := x :: xs) hskip with ⟨u, v, hw, hu, hv⟩
            refine ⟨y :: u, v, ?_, ?_, hv⟩
            · simp only [List.cons_append, hw]
            · exact List.Sublist.cons y hu
          · cases heq
            rcases ih (a := xs) htake with ⟨u, v, hw, hu, hv⟩
            refine ⟨y :: u, v, ?_, ?_, hv⟩
            · simp only [List.cons_append, hw]
            · exact List.Sublist.cons_cons y hu

/-! ## Three-phase forcing, every `psi` -/

/-- **Lemma 18, first three phases, every `psi`.**  If the frozen Lemma-18
word occurs as an ordered subsequence of the schedule, the `P_PL'` run from
a `C_PB` configuration with unique leader `root` visits rooted `S_PL` or
rooted `C_DL`.  Proof: split the schedule into the root-reset, distance and
last chunks (the risky-flush and build chunks are ignored) and thread the
three proved gapped phases; a hit inside a chunk is transported through the
rest of the word, and the last-sweep endpoint is rooted `C_DL`. -/
theorem l18ForcingWordReachesSafe
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa)
    (hCPB : CPB ring C)
    (hUnique : L18UniqueLeaderAt C root)
    (w : DetSchedule n)
    (hsub : (l18Word ring root psi).Sublist w) :
    l18HitsSafe ring root C w = true := by
  have hfull :
      (l18RootResetWord ring root ++
        (l18DistanceWord ring root ++
          (l18LastWord ring root ++
            (l18RiskyFlushWord ring root psi ++
              l18BuildWord ring root psi)))).Sublist w := by
    simpa [l18Word] using hsub
  rcases sublist_append_split (l18RootResetWord ring root) _ w hfull with
    ⟨w1, rest1, hw1, hsub1, hrest1⟩
  rcases sublist_append_split (l18DistanceWord ring root) _ rest1 hrest1 with
    ⟨w2, rest2, hw2, hsub2, hrest2⟩
  rcases sublist_append_split (l18LastWord ring root) _ rest2 hrest2 with
    ⟨w3, rest3, hw3, hsub3, _hrest3⟩
  subst hw1 hw2 hw3
  rcases l18GappedRootResetPhase_proved hn3 hpsi ring root C w1
      hCPB hUnique hsub1 with hhit1 | hpost1
  · exact l18HitsSafe_append_left ring root C w1 _
      (l18HitsSafe_of_hitsSPL ring root C w1 hhit1)
  dsimp only at hpost1
  let C1 : Config n psi kappa := runPPrime ring C w1
  apply l18HitsSafe_append_right ring root C w1
  rcases l18GappedDistanceSweepPhase_proved hn3 hpsi ring root C1 w2
      hpost1.1 hpost1.2.1 hpost1.2.2 hsub2 with hhit2 | hpost2
  · exact l18HitsSafe_append_left ring root C1 w2 _
      (l18HitsSafe_of_hitsSPL ring root C1 w2 hhit2)
  dsimp only at hpost2
  let C2 : Config n psi kappa := runPPrime ring C1 w2
  apply l18HitsSafe_append_right ring root C1 w2
  rcases l18GappedLastSweepPhase_proved hn3 hpsi ring root C2 w3
      hpost2.1 hpost2.2.1 hpost2.2.2 hsub3 with hhit3 | hpost3
  · exact l18HitsSafe_append_left ring root C2 w3 _
      (l18HitsSafe_of_hitsSPL ring root C2 w3 hhit3)
  apply l18HitsSafe_append_left ring root C2 w3
  exact l18HitsSafe_of_endpoint ring root C2 w3 (Or.inr hpost3)

/-! ## Counting tail -/

/-- Number of `l18Horizon n psi`-letter words whose `P_PL'` run misses the
rooted safe predicate. -/
def l18SafeFailureCount
    {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa) : Nat :=
  (allSchedules n (l18Horizon n psi)).countP
    (fun schedule => !(l18HitsSafe ring root C schedule))

/-- **Lemma-18 counting tail with the safe target, every `psi`.**  At most
`n^{H18}/n` of the `H18`-letter words miss the rooted safe predicate: each
miss is a word that does not contain `l18Word` as an ordered subsequence,
and the fixed-word count bounds those.  Same arithmetic as
`n_mul_l18FailureCount_le_pow_scoped`. -/
theorem n_mul_l18SafeFailureCount_le_pow
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa)
    (hCPB : CPB ring C)
    (hUnique : L18UniqueLeaderAt C root) :
    n * l18SafeFailureCount ring root C ≤ n ^ l18Horizon n psi := by
  have hfail :
      l18SafeFailureCount ring root C ≤
        PPL.Probability.fixedWordMissCount
          (l18Word ring root psi) (l18Horizon n psi) := by
    change
      (allSchedules n (l18Horizon n psi)).countP
          (fun schedule => !(l18HitsSafe ring root C schedule)) ≤
        (allSchedules n (l18Horizon n psi)).countP
          (fun schedule =>
            decide (Not ((l18Word ring root psi).Sublist schedule)))
    apply l18_countP_mono
    intro schedule hbad
    by_cases hsub : (l18Word ring root psi).Sublist schedule
    · have hs :=
        l18ForcingWordReachesSafe hn3 hpsi ring root C hCPB hUnique
          schedule hsub
      simp [hs] at hbad
    · simp [hsub]
  have hfixed :
      PPL.Probability.fixedWordMissCount
          (l18Word ring root psi) (l18Horizon n psi) *
          2 ^ (4 * l18K n) ≤
        n ^ l18Horizon n psi := by
    simpa [l18Horizon] using
      (PPL.Probability.fixedWordMissCount_mul_twoPow_le_of_length
        (l18Word ring root psi)
        (l18Length n psi)
        (4 * l18K n)
        (l18Word_length hn3 hpsi ring root))
  have hn0 : n ≠ 0 := by omega
  have hlt : n < 2 ^ l18K n := by
    unfold l18K
    exact (Nat.log2_lt hn0).1 (by omega)
  have hpow : 2 ^ l18K n ≤ 2 ^ (4 * l18K n) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  have hn4 : n ≤ 2 ^ (4 * l18K n) := Nat.le_trans (Nat.le_of_lt hlt) hpow
  calc
    n * l18SafeFailureCount ring root C ≤
        n * PPL.Probability.fixedWordMissCount
          (l18Word ring root psi) (l18Horizon n psi) :=
      Nat.mul_le_mul_left n hfail
    _ ≤ 2 ^ (4 * l18K n) * PPL.Probability.fixedWordMissCount
          (l18Word ring root psi) (l18Horizon n psi) :=
      Nat.mul_le_mul_right _ hn4
    _ = PPL.Probability.fixedWordMissCount
          (l18Word ring root psi) (l18Horizon n psi) *
          2 ^ (4 * l18K n) := Nat.mul_comm _ _
    _ ≤ n ^ l18Horizon n psi := hfixed

end PPL.PsiAtLeastN

#print axioms PPL.PsiAtLeastN.l18ForcingWordReachesSafe
#print axioms PPL.PsiAtLeastN.n_mul_l18SafeFailureCount_le_pow
