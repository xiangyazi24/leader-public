import Leader.PPL.SPLEntry.BuiltPairSelectedBlack
import Leader.PPL.SPLEntry.BuiltPairIds
import Leader.PPL.SPLEntry.BuiltPairStepRoute
import Leader.PPL.SPLEntry.CompletionFrameAdapter
import Leader.PPL.SPLEntry.CompletionCoreRoute
import Leader.PPL.SPLEntry.BuildBlockAdvance
import Leader.PPL.SPLEntry.BuildGappedAssembly
import Init.Data.List.Sublist
import Init.Omega

/-!
# L18 prime pair row: assembly around the establishment cut

This file assembles the current-pair half `L18PrimeLemma4PairRow` of the prime
Lemma-4 core from two explicitly named open inputs:

* `L18PrimeSelectedWhiteFrame` — the white sibling of the landed
  `l18PrimeStepSelectedEstablishedTokensBlack` (the white conjunct of
  `hSelected` in `l18PrimeStepPreservesBuiltPairPrefix_of_frames`);
* `L18PrimeLemma4EstablishmentCutRow` — the establishment-cut trace theorem
  (c).

Everything else is reuse of landed declarations:

1. (b) `l18PrimeStepCurrentPairIds_of_established`: the ID/source frame of
   pair `b` after establishment, i.e. `l18PrimeStepProtectedEstablishedIds`
   at prefix index `b+1`;
2. (a, black) `l18PrimeStepCurrentPairSelectedTokensBlack_of_established`:
   the landed black selected-token theorem at prefix index `b+1`, `seg = b`;
3. the suffix frame `l18PrimeRunPrefixAndPair_of_established`, which keeps
   `Prefix b` and `Pair b` along any prime suffix;
4. the final-block case `l18HitsSPL_append_of_fullBlock`;
5. the pure list extraction `q20301MinimalSublistCut` of a minimal cut;
6. the assembly `l18PrimeLemma4PairRow_of_cut`.
-/

namespace PPL.Convergence.L18

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option linter.unusedVariables false

open PPL

open Lean Elab Term Meta in
elab "q20301gap% " s:str : term => do
  let n : Name :=
    ((((((`_private.Leader.PPL.SPLEntry.BuildGappedAssembly).num 0).str
      "PPL").str "Convergence").str "L18").str s.getString)
  mkConstWithFreshMVarLevels n

/-! ## Open inputs, as named propositions -/

/-- White sibling of `l18PrimeStepSelectedEstablishedTokensBlack`: the white
conjunct of `hSelected` in `l18PrimeStepPreservesBuiltPairPrefix_of_frames`,
under the same hypotheses as the landed black theorem.  Not yet proved; it is
an explicit input of the assembly below. -/
def L18PrimeSelectedWhiteFrame : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (b : Nat)
    (C : Config n psi kappa)
    (e : Fin n)
    (hb : b < l18BlockCount n psi)
    (hPrefix : L18BuildPrefixAt ring root b C)
    (hIds :
      ∀ seg : Fin (l18BlockCount n psi),
        seg.val < b →
          sourceIota ring root C seg.val =
              sourceIota ring root
                (pprimeStep ring C e) seg.val ∧
            rootedSegmentId ring root
                (pprimeStep ring C e) seg.val =
              rootedSegmentId ring root C seg.val ∧
            rootedSegmentId ring root
                (pprimeStep ring C e)
                (seg.val + 1) =
              rootedSegmentId ring root C
                (seg.val + 1)),
    ∀ seg : Fin (l18BlockCount n psi),
      seg.val < b →
      ∀ i : Fin n,
        (i = e ∨
          i = ring.rightNeighbor e) →
        (ValidToken .white
            (pprimeStep ring C e) i ∧
          WorkingFor ring root
            (pprimeStep ring C e)
            i .white seg.val) →
        CorrectToken ring root
          (pprimeStep ring C e)
          i .white seg.val

/-- (c): the establishment-cut trace theorem, verbatim
`l18PrimeLemma4EstablishmentCut`, packaged as a proposition.  Not yet proved;
it is an explicit input of the assembly below. -/
def L18PrimeLemma4EstablishmentCutRow : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (b : Nat)
    (C : Config n psi kappa)
    (cut : DetSchedule n)
    (hb : b < l18BlockCount n psi)
    (hPrefix : L18BuildPrefixAt ring root b C)
    (hsub :
      (PPL.lemma4Word ring
        (shiftRight ring root (b * psi)) psi).Sublist cut)
    (hminimal :
      ∀ (cut0 tail : DetSchedule n),
        cut = cut0 ++ tail →
        tail ≠ [] →
        Not
          ((PPL.lemma4Word ring
            (shiftRight ring root (b * psi)) psi).Sublist cut0)),
    let E := runPPrime ring C cut
    Or
      (l18HitsSPL ring root C cut = true)
      (L18BuildPairOK ring root E b)

/-! ## Item 1: ID/source frame of the current pair -/

/-- (b).  Once pair `b` is established on top of `Prefix b`, one prime
letter preserves `sourceIota b` and the segment IDs of `S_b` and `S_(b+1)`.
Proof: promote to `Prefix (b+1)` by `l18BuildPrefixAt_succ_of_pair` and apply
the protected-ID frame `l18PrimeStepProtectedEstablishedIds` at `seg = b`. -/
theorem l18PrimeStepCurrentPairIds_of_established
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (b : Nat)
    (C : Config n psi kappa)
    (e : Fin n)
    (hb : b < l18BlockCount n psi)
    (hbNext : b + 1 < l18BlockCount n psi)
    (hPrefix : L18BuildPrefixAt ring root b C)
    (hPair : L18BuildPairOK ring root C b) :
    let D := pprimeStep ring C e
    And
      (sourceIota ring root C b =
        sourceIota ring root D b)
      (And
        (rootedSegmentId ring root D b =
          rootedSegmentId ring root C b)
        (rootedSegmentId ring root D (b + 1) =
          rootedSegmentId ring root C (b + 1))) := by
  have hSucc :
      L18BuildPrefixAt ring root (b + 1) C :=
    l18BuildPrefixAt_succ_of_pair
      ring root b C hPrefix hPair
  exact
    l18PrimeStepProtectedEstablishedIds
      hn3 hpsi ring root (b + 1) C e hbNext hSucc
      ⟨b, hb⟩ (Nat.lt_succ_self b)

/-! ## Item 2 -/

/-- (a), black half.  After pair `b` is established, at either selected
endpoint every post valid black token working for pair `b` is correct.  This
is the landed `l18PrimeStepSelectedEstablishedTokensBlack` at prefix index
`b+1` and `seg = b`, fed by the ID frame at `b+1`. -/
theorem l18PrimeStepCurrentPairSelectedTokensBlack_of_established
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (b : Nat)
    (C : Config n psi kappa)
    (e : Fin n)
    (hb : b < l18BlockCount n psi)
    (hbNext : b + 1 < l18BlockCount n psi)
    (hPrefix : L18BuildPrefixAt ring root b C)
    (hPair : L18BuildPairOK ring root C b) :
    ∀ i : Fin n,
      Or (i = e) (i = ring.rightNeighbor e) →
      (And
          (ValidToken .black (pprimeStep ring C e) i)
          (WorkingFor ring root (pprimeStep ring C e)
            i .black b)) →
        CorrectToken ring root (pprimeStep ring C e)
          i .black b := by
  intro i hi hVW
  have hSucc :
      L18BuildPrefixAt ring root (b + 1) C :=
    l18BuildPrefixAt_succ_of_pair
      ring root b C hPrefix hPair
  exact
    l18PrimeStepSelectedEstablishedTokensBlack
      hn3 hpsi ring root (b + 1) C e hbNext hSucc
      (l18PrimeStepProtectedEstablishedIds
        hn3 hpsi ring root (b + 1) C e hbNext hSucc)
      ⟨b, hb⟩ (Nat.lt_succ_self b) i hi hVW

/-! ## Item 3: the suffix frame -/

/-- One prime letter preserves `Prefix b`, for every `b < l18BlockCount`,
given the white selected-token frame.  Built from the landed assembler
`l18PrimeStepPreservesBuiltPairPrefix_of_frames` (protected IDs + black
selected tokens + `hWhite`) and the safety frame inside
`l18PrimeStepPreservesBuildPrefix_of_builtPairs`. -/
theorem l18PrimeStepPreservesBuildPrefix_of_white
    (hWhite : L18PrimeSelectedWhiteFrame) :
    ∀ {n psi kappa : Nat}
      (hn3 : 3 ≤ n)
      (hpsi : 2 ≤ psi)
      (ring : DirectedRing n)
      (root : Fin n)
      (b : Nat)
      (C : Config n psi kappa)
      (e : Fin n),
      b < l18BlockCount n psi →
      L18BuildPrefixAt ring root b C →
      L18BuildPrefixAt ring root b
        (pprimeStep ring C e) := by
  apply l18PrimeStepPreservesBuildPrefix_of_builtPairs
  intro n psi kappa hn3 hpsi ring root b C e hb hPrefix
  have hIds :=
    l18PrimeStepProtectedEstablishedIds
      hn3 hpsi ring root b C e hb hPrefix
  apply
    l18PrimeStepPreservesBuiltPairPrefix_of_frames
      hn3 hpsi ring root b C e hb hPrefix hIds
  intro seg hseg i hi
  exact
    ⟨l18PrimeStepSelectedEstablishedTokensBlack
        hn3 hpsi ring root b C e hb hPrefix hIds
        seg hseg i hi,
      hWhite
        hn3 hpsi ring root b C e hb hPrefix hIds
        seg hseg i hi⟩

/-- `Prefix b` survives any prime schedule, given the white frame. -/
theorem l18PrimeRunPreservesBuildPrefix_of_white
    (hWhite : L18PrimeSelectedWhiteFrame)
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (b : Nat)
    (C : Config n psi kappa)
    (schedule : DetSchedule n)
    (hb : b < l18BlockCount n psi)
    (hPrefix : L18BuildPrefixAt ring root b C) :
    L18BuildPrefixAt ring root b
      (runPPrime ring C schedule) := by
  induction schedule generalizing C with
  | nil =>
      exact hPrefix
  | cons e rest ih =>
      exact
        ih (pprimeStep ring C e)
          (l18PrimeStepPreservesBuildPrefix_of_white
            hWhite hn3 hpsi ring root b C e hb hPrefix)

/-- Item 3, the suffix frame.  Once pair `b` is established on top of
`Prefix b` and `b+1 < l18BlockCount`, both `Prefix b` and `Pair b` survive any
prime suffix.  Proof: promote to `Prefix (b+1)`, frame it along the suffix
with the one-letter frame at index `b+1`, and read off both halves. -/
theorem l18PrimeRunPrefixAndPair_of_established
    (hWhite : L18PrimeSelectedWhiteFrame)
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (b : Nat)
    (E : Config n psi kappa)
    (hbNext : b + 1 < l18BlockCount n psi)
    (hPrefix : L18BuildPrefixAt ring root b E)
    (hPair : L18BuildPairOK ring root E b)
    (suffix : DetSchedule n) :
    And
      (L18BuildPrefixAt ring root b (runPPrime ring E suffix))
      (L18BuildPairOK ring root (runPPrime ring E suffix) b) := by
  have hSucc :
      L18BuildPrefixAt ring root (b + 1) E :=
    l18BuildPrefixAt_succ_of_pair
      ring root b E hPrefix hPair
  have hEnd :=
    l18PrimeRunPreservesBuildPrefix_of_white
      hWhite hn3 hpsi ring root (b + 1) E suffix
      hbNext hSucc
  refine ⟨⟨hEnd.1, hEnd.2.1, ?_⟩, ?_⟩
  · intro seg hseg
    exact hEnd.2.2 seg (Nat.lt_succ_of_lt hseg)
  · have hbLt : b < l18BlockCount n psi := by
      omega
    exact hEnd.2.2 ⟨b, hbLt⟩ (Nat.lt_succ_self b)

/-! ## Item 4: the final block -/

/-- If the prime run along `cut` ends in an `SPLAt` configuration, the hit
Boolean along `cut` is true. -/
theorem l18HitsSPL_of_end
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (cut : DetSchedule n)
    (hS : SPLAt ring root (runPPrime ring C cut)) :
    l18HitsSPL ring root C cut = true := by
  induction cut generalizing C with
  | nil =>
      exact decide_eq_true hS
  | cons e rest ih =>
      have htail := ih (pprimeStep ring C e) hS
      simp only [l18HitsSPL, htail, Bool.or_true]

/-- Item 4.  If `b+1 = l18BlockCount` and the cut endpoint carries `Prefix b`
and `Pair b`, the cut endpoint is `SPLAt` (private `l18BuildPrefixAt_full_spl`),
so the hit Boolean is true along the cut and hence along `cut ++ suffix`
(private `l18HitsSPL_append_left_true`). -/
theorem l18HitsSPL_append_of_fullBlock
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (b : Nat)
    (C : Config n psi kappa)
    (cut suffix : DetSchedule n)
    (hbLast : b + 1 = l18BlockCount n psi)
    (hPrefix :
      L18BuildPrefixAt ring root b (runPPrime ring C cut))
    (hPair :
      L18BuildPairOK ring root (runPPrime ring C cut) b) :
    l18HitsSPL ring root C (cut ++ suffix) = true := by
  have hSucc :=
    l18BuildPrefixAt_succ_of_pair
      ring root b (runPPrime ring C cut) hPrefix hPair
  rw [hbLast] at hSucc
  have hS : SPLAt ring root (runPPrime ring C cut) :=
    (q20301gap% "l18BuildPrefixAt_full_spl")
      ring root (runPPrime ring C cut) hSucc
  exact
    (q20301gap% "l18HitsSPL_append_left_true")
      ring root C cut suffix
      (l18HitsSPL_of_end ring root C cut hS)

/-! ## Item 5: minimal cut extraction (pure list bookkeeping) -/

private theorem q20301MinimalTake
    {α : Type} (l s : List α) :
    ∀ k : Nat,
      (∃ j : Nat, j ≤ k ∧ l.Sublist (s.take j)) →
      ∃ m : Nat,
        m ≤ k ∧ l.Sublist (s.take m) ∧
          ∀ j : Nat, j < m → ¬ l.Sublist (s.take j) := by
  intro k
  induction k with
  | zero =>
      intro h
      obtain ⟨j, hj, hsub⟩ := h
      have hj0 : j = 0 := by omega
      subst hj0
      exact ⟨0, Nat.le_refl 0, hsub, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ k ih =>
      intro h
      by_cases hlow : ∃ j : Nat, j ≤ k ∧ l.Sublist (s.take j)
      · obtain ⟨m, hm, hsub, hmin⟩ := ih hlow
        exact ⟨m, Nat.le_succ_of_le hm, hsub, hmin⟩
      · obtain ⟨j, hj, hsub⟩ := h
        have hjk : j = k + 1 := by
          by_cases hjle : j ≤ k
          · exact False.elim (hlow ⟨j, hjle, hsub⟩)
          · omega
        subst hjk
        refine ⟨k + 1, Nat.le_refl _, hsub, ?_⟩
        intro j' hj' hsub'
        exact hlow ⟨j', by omega, hsub'⟩

/-- Item 5.  From `l.Sublist schedule`, split `schedule = cut ++ suffix` with
`l.Sublist cut` and `cut` minimal: no proper prefix of `cut` contains `l`.
This is the `hsub`/`hminimal` pair consumed by the establishment cut. -/
theorem q20301MinimalSublistCut
    {α : Type} (l schedule : List α)
    (h : l.Sublist schedule) :
    ∃ cut suffix : List α,
      schedule = cut ++ suffix ∧
        l.Sublist cut ∧
        ∀ (cut0 tail : List α),
          cut = cut0 ++ tail →
          tail ≠ [] →
          ¬ l.Sublist cut0 := by
  have hfull : l.Sublist (schedule.take schedule.length) := by
    rw [List.take_length]
    exact h
  obtain ⟨m, hm, hsub, hmin⟩ :=
    q20301MinimalTake l schedule schedule.length
      ⟨schedule.length, Nat.le_refl _, hfull⟩
  refine ⟨schedule.take m, schedule.drop m,
    (List.take_append_drop m schedule).symm, hsub, ?_⟩
  intro cut0 tail hcut htail hsub0
  have hlenTake : (schedule.take m).length = m := by
    rw [List.length_take]
    omega
  have hlen :
      cut0.length + tail.length = m := by
    rw [← hlenTake, hcut, List.length_append]
  have htailPos : 0 < tail.length := by
    cases tail with
    | nil => exact False.elim (htail rfl)
    | cons a t => exact Nat.succ_pos _
  have hlt : cut0.length < m := by
    omega
  have htake0 : schedule.take cut0.length = cut0 := by
    have h1 :
        (schedule.take m).take cut0.length = cut0 := by
      rw [hcut]
      exact List.take_append_length
    rw [List.take_take] at h1
    have hmin' : min cut0.length m = cut0.length := by
      omega
    rw [hmin'] at h1
    exact h1
  apply hmin cut0.length hlt
  rw [htake0]
  exact hsub0

/-! ## Item 6: assembly of the pair row -/

/-- Item 6.  The current-pair half `L18PrimeLemma4PairRow` of the prime
Lemma-4 core, from the white selected-token frame and the establishment-cut
theorem (c).

Proof.  Split `schedule = cut ++ suffix` at the minimal cut (item 5) and apply
(c).  A hit along the cut propagates to the schedule.  Otherwise `Pair b` holds
at `E = runPPrime C cut`; `Prefix b` holds at `E` by the run frame (the cut
theorem does not supply it).  If `b+1 = l18BlockCount` the schedule hits SPL
(item 4); otherwise the suffix frame (item 3) carries `Pair b` to the end. -/
theorem l18PrimeLemma4PairRow_of_cut
    (hWhite : L18PrimeSelectedWhiteFrame)
    (hCut : L18PrimeLemma4EstablishmentCutRow) :
    L18PrimeLemma4PairRow := by
  unfold L18PrimeLemma4PairRow
  intro _hlemma4 n psi kappa hn3 hpsi ring root b C schedule hb hPrefix hsub
  obtain ⟨cut, suffix, hsplit, hsubCut, hminimal⟩ :=
    q20301MinimalSublistCut _ schedule hsub
  have hc :=
    hCut hn3 hpsi ring root b C cut hb hPrefix hsubCut hminimal
  dsimp only at hc ⊢
  rw [hsplit]
  rcases hc with hhit | hPairE
  · exact
      Or.inl
        ((q20301gap% "l18HitsSPL_append_left_true")
          ring root C cut suffix hhit)
  · have hPrefixE :
        L18BuildPrefixAt ring root b (runPPrime ring C cut) :=
      l18PrimeRunPreservesBuildPrefix_of_white
        hWhite hn3 hpsi ring root b C cut hb hPrefix
    by_cases hbNext : b + 1 < l18BlockCount n psi
    · have hframe :=
        l18PrimeRunPrefixAndPair_of_established
          hWhite hn3 hpsi ring root b
          (runPPrime ring C cut) hbNext hPrefixE hPairE suffix
      rw [runPPrime_append]
      exact Or.inr hframe.2
    · have hbLast : b + 1 = l18BlockCount n psi := by
        omega
      exact
        Or.inl
          (l18HitsSPL_append_of_fullBlock
            ring root b C cut suffix hbLast hPrefixE hPairE)

end PPL.Convergence.L18

#print axioms PPL.Convergence.L18.l18PrimeStepCurrentPairIds_of_established
#print axioms PPL.Convergence.L18.l18PrimeStepCurrentPairSelectedTokensBlack_of_established
#print axioms PPL.Convergence.L18.l18PrimeRunPrefixAndPair_of_established
#print axioms PPL.Convergence.L18.l18HitsSPL_append_of_fullBlock
#print axioms PPL.Convergence.L18.q20301MinimalSublistCut
#print axioms PPL.Convergence.L18.l18PrimeLemma4PairRow_of_cut
