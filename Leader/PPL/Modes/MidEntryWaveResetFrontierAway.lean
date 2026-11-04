import Leader.PPL.Modes.MidEntryWaveResetFrontierRoute

namespace PPL.Modes.Lemma5

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL.Probability
open PPL.Modes.SignalLineage
open PPL.Modes.Lemma9

/--
Appending one scheduler letter e cannot create a previously missing
subsequence whose final requested letter is a, provided e != a.
-/
private theorem q20168SublistAppendSingletonLastNe
    {A : Type}
    (pre : List A) :
    forall (s : List A) (a e : A),
      (Not ((s ++ [a]).Sublist pre)) ->
      e ≠ a ->
      Not ((s ++ [a]).Sublist (pre ++ [e])) := by
  induction pre with
  | nil =>
      intro s a e _hmiss hne hpost
      have ha :
          a ∈ ([e] : List A) :=
        hpost.subset (by simp)
      have hae : a = e := by
        simpa only [List.mem_singleton] using ha
      exact hne hae.symm
  | cons x xs ih =>
      intro s a e hmiss hne hpost
      cases s with
      | nil =>
          have haPost :
              a ∈ ((x :: xs) ++ [e]) :=
            hpost.subset (by simp)
          have haPre : a ∉ (x :: xs) := by
            intro ha
            apply hmiss
            exact List.singleton_sublist.mpr ha
          rw [List.mem_append] at haPost
          rcases haPost with haOld | haLast
          · exact False.elim (haPre haOld)
          · have hae : a = e := by
              simpa only [List.mem_singleton] using haLast
            exact hne hae.symm
      | cons y ys =>
          have hs :
              (y :: (ys ++ [a])).Sublist
                (x :: (xs ++ [e])) := by
            simpa only [List.cons_append] using hpost
          rcases List.sublist_cons_iff.mp hs with
            hskip | ⟨tail, heq, htake⟩
          · have hmissTail :
                Not (((y :: ys) ++ [a]).Sublist xs) := by
              intro hbad
              apply hmiss
              exact List.Sublist.cons x hbad
            have hbad :=
              ih (y :: ys) a e hmissTail hne
            apply hbad
            simpa only [List.cons_append] using hskip
          · cases heq
            have hmissTail :
                Not ((ys ++ [a]).Sublist xs) := by
              intro hbad
              apply hmiss
              have hfull :
                  (x :: (ys ++ [a])).Sublist
                    (x :: xs) :=
                List.Sublist.cons_cons x hbad
              simpa only [List.cons_append] using hfull
            exact
              ih ys a e hmissTail hne htake

private theorem q20168SeqR_succ
    {n : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (q : Nat) :
    PPL.seqR ring root (q + 1) =
      PPL.seqR ring root q ++
        [PPL.shiftRight ring root q] := by
  unfold PPL.seqR
  rw [List.ofFn_succ_last]
  rfl

theorem lemma5iWaveResetFrontierAwayRow_proved :
    Lemma5iWaveResetFrontierAwayRow := by
  unfold Lemma5iWaveResetFrontierAwayRow
  intro n psi kappa
  intro _hn3 _hpsi ring D pre e
  intro hactive hfront he

  unfold Lemma5iLeaderWaveResetFrontierAt at hfront ⊢
  dsimp only at hfront ⊢
  rcases hfront with
    ⟨q, hqn, hhost, hsub, hnext, hwit⟩

  refine ⟨q, hqn, ?_, ?_, ?_, ?_⟩

  · have hloc :
        lemma5iLeaderWaveHost ring D (pre ++ [e]) =
          if e = lemma5iLeaderWaveHost ring D pre then
            ring.rightNeighbor
              (lemma5iLeaderWaveHost ring D pre)
          else
            lemma5iLeaderWaveHost ring D pre :=
      lemma5iLeaderWaveLocationOneStep_proved
        ring D pre e hactive
    rw [if_neg he] at hloc
    exact hloc.trans hhost

  · exact
      hsub.trans (List.sublist_append_left pre [e])

  · have heLast :
        e ≠
          PPL.shiftRight ring
            (lemma5iLeaderWaveStart ring D) q := by
      intro heq
      apply he
      calc
        e =
            PPL.shiftRight ring
              (lemma5iLeaderWaveStart ring D) q :=
          heq
        _ = lemma5iLeaderWaveHost ring D pre :=
          hhost.symm

    rw [
      q20168SeqR_succ
        ring
        (lemma5iLeaderWaveStart ring D)
        q
    ] at hnext ⊢

    exact
      q20168SublistAppendSingletonLastNe
        pre
        (PPL.seqR ring
          (lemma5iLeaderWaveStart ring D) q)
        (PPL.shiftRight ring
          (lemma5iLeaderWaveStart ring D) q)
        e
        hnext heLast

  · intro j hj
    have hw :
        Lemma5iLeaderWaveResetWitness
          ring D
          (lemma5iLeaderWaveStart ring D)
          pre j :=
      hwit j hj
    unfold Lemma5iLeaderWaveResetWitness at hw ⊢
    rcases hw with
      ⟨before, after, hpre, hsmall, hreset⟩
    refine
      ⟨before, after ++ [e], ?_, hsmall, hreset⟩
    rw [hpre]
    simp only [List.append_assoc, List.cons_append]

end PPL.Modes.Lemma5

#print axioms PPL.Modes.Lemma5.lemma5iWaveResetFrontierAwayRow_proved
