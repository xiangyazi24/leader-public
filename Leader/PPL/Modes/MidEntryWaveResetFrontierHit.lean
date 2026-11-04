import Leader.PPL.Modes.MidEntryWaveResetFrontierAway

namespace PPL.Modes.Lemma5

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL.Probability
open PPL.Modes.SignalLineage
open PPL.Modes.Lemma9

/--
Appending one scheduler letter e cannot create a previously missing
subsequence whose final requested letter is a, provided e ≠ a.
-/
private theorem q20169SublistAppendSingletonLastNe
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

/--
If s ++ [a] was still missing before the append, one appended scheduler
letter cannot create both that missing final a and a later requested b.
-/
private theorem q20169SublistAppendSingletonNoDouble
    {A : Type}
    (pre : List A) :
    forall (s : List A) (a b e : A),
      Not ((s ++ [a]).Sublist pre) ->
      Not ((s ++ [a] ++ [b]).Sublist (pre ++ [e])) := by
  induction pre with
  | nil =>
      intro s a b e _hmiss hpost
      have hlen := hpost.length_le
      simp only
        [List.length_append,
          List.length_singleton,
          List.length_nil] at hlen
      omega
  | cons x xs ih =>
      intro s a b e hmiss hpost
      cases s with
      | nil =>
          have hs :
              (a :: [b]).Sublist
                (x :: (xs ++ [e])) := by
            simpa only
              [List.nil_append, List.cons_append]
              using hpost
          rcases List.sublist_cons_iff.mp hs with
            hskip | ⟨tail, heq, htake⟩
          · have hmissTail :
                Not (([] ++ [a]).Sublist xs) := by
              intro hbad
              apply hmiss
              exact List.Sublist.cons x hbad
            exact
              ih [] a b e hmissTail
                (by
                  exact hskip)
          · cases heq
            apply hmiss
            exact
              List.singleton_sublist.mpr
                (by simp)
      | cons y ys =>
          have hs :
              (y :: (ys ++ [a] ++ [b])).Sublist
                (x :: (xs ++ [e])) := by
            simpa only [List.cons_append] using hpost
          rcases List.sublist_cons_iff.mp hs with
            hskip | ⟨tail, heq, htake⟩
          · have hmissTail :
                Not (((y :: ys) ++ [a]).Sublist xs) := by
              intro hbad
              apply hmiss
              exact List.Sublist.cons x hbad
            exact
              ih (y :: ys) a b e hmissTail
                (by
                  simpa only [List.cons_append]
                    using hskip)
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
              ih ys a b e hmissTail htake

private theorem q20169SeqR_succ
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

private theorem q20169ShiftRight_add
    {n : Nat}
    (ring : DirectedRing n)
    (i : Fin n)
    (a b : Nat) :
    PPL.shiftRight ring
        (PPL.shiftRight ring i a) b =
      PPL.shiftRight ring i (a + b) := by
  apply Fin.ext
  change
    (((i.val + a) % n + b) % n) =
      (i.val + (a + b)) % n
  rw [Nat.mod_add_mod, Nat.add_assoc]

private theorem q20169ShiftRight_succ
    {n : Nat}
    (ring : DirectedRing n)
    (i : Fin n)
    (q : Nat) :
    PPL.shiftRight ring i (q + 1) =
      ring.rightNeighbor
        (PPL.shiftRight ring i q) := by
  calc
    PPL.shiftRight ring i (q + 1) =
        PPL.shiftRight ring
          (PPL.shiftRight ring i q) 1 :=
      (q20169ShiftRight_add ring i q 1).symm
    _ =
        ring.rightNeighbor
          (PPL.shiftRight ring i q) := rfl

private theorem q20169CyclicOffset_lt
    {n : Nat}
    (ring : DirectedRing n)
    (root i : Fin n) :
    PPL.cyclicOffset ring root i < n := by
  unfold PPL.cyclicOffset
  exact Nat.mod_lt _ ring.hn

private theorem q20169ShiftRight_cyclicOffset
    {n : Nat}
    (ring : DirectedRing n)
    (a b : Fin n) :
    PPL.shiftRight ring a
        (PPL.cyclicOffset ring a b) =
      b := by
  apply Fin.ext
  change
    (a.val + ((b.val + n - a.val) % n)) % n =
      b.val
  by_cases hab : a.val ≤ b.val
  · have heq :
        b.val + n - a.val =
          n + (b.val - a.val) := by
      omega
    rw [heq, Nat.add_mod_left,
      Nat.mod_eq_of_lt
        (by omega : b.val - a.val < n)]
    have hsum :
        a.val + (b.val - a.val) = b.val := by
      omega
    rw [hsum, Nat.mod_eq_of_lt b.isLt]
  · have hlt :
        b.val + n - a.val < n := by
      omega
    rw [Nat.mod_eq_of_lt hlt]
    have hsum :
        a.val + (b.val + n - a.val) =
          b.val + n := by
      omega
    rw [hsum, Nat.add_mod_right,
      Nat.mod_eq_of_lt b.isLt]

private theorem q20169HostSelfReset
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (pre : DetSchedule n)
    (hactive :
      Lemma5iLeaderWaveActivePrefix ring D pre) :
    clockResetAt
        ring
        (runPPL ring D pre)
        (lemma5iLeaderWaveHost ring D pre)
        (lemma5iLeaderWaveHost ring D pre) =
      true := by
  have hstop :
      lemma5iLeaderWaveStopB ring D pre = false :=
    hactive.1
  unfold lemma5iLeaderWaveStopB at hstop
  dsimp only at hstop
  have hne :
      ((runPPL ring D pre)
        (lemma5iLeaderWaveHost ring D pre)).signalR.val ≠
        0 :=
    of_decide_eq_false hstop
  have hpos :
      0 <
        ((runPPL ring D pre)
          (lemma5iLeaderWaveHost ring D pre)).signalR.val := by
    omega
  have hlt :=
    ((runPPL ring D pre)
      (lemma5iLeaderWaveHost ring D pre)).signalR.isLt
  have hkpos : 0 < kappa := by
    omega

  unfold clockResetAt
  dsimp only
  by_cases hlead :
      ((runPPL ring D pre)
        (lemma5iLeaderWaveHost ring D pre)).leader =
      true
  · simp [hlead, hkpos]
  · simp [hlead, hpos]

private theorem q20169ResetWitness_append
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (start : Fin n)
    (pre : DetSchedule n)
    (e : Fin n)
    (j : Nat)
    (h :
      Lemma5iLeaderWaveResetWitness
        ring D start pre j) :
    Lemma5iLeaderWaveResetWitness
      ring D start (pre ++ [e]) j := by
  unfold Lemma5iLeaderWaveResetWitness at h ⊢
  rcases h with
    ⟨before, after, hpre, hsub, hreset⟩
  refine
    ⟨before, after ++ [e], ?_, hsub, hreset⟩
  rw [hpre]
  simp only [List.append_assoc, List.cons_append]

private theorem q20169ClockResetSeen_of_prefix_reset
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (x : Fin n)
    (before after : DetSchedule n)
    (e : Fin n)
    (hreset :
      clockResetAt ring
          (runPPL ring D before) x e =
        true) :
    clockResetSeenAux ring x D
        (before ++ (e :: after)) =
      true := by
  induction before generalizing D with
  | nil =>
      have hr :
          clockResetAt ring D x e = true := by
        simpa [runPPL, runPopulationSchedule]
          using hreset
      simp [clockResetSeenAux, hr]
  | cons a rest ih =>
      cases hr : clockResetAt ring D x a with
      | true =>
          simp [List.cons_append,
            clockResetSeenAux, hr]
      | false =>
          have hreset' :
              clockResetAt ring
                  (runPPL ring
                    (pplStep ring D a) rest)
                  x e =
                true := by
            simpa [runPPL, runPopulationSchedule,
              pplStep] using hreset
          have htail :=
            ih (D := pplStep ring D a) hreset'
          simpa [List.cons_append,
            clockResetSeenAux, hr] using htail

private theorem q20169ResetWitness_seen
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (start : Fin n)
    (word : DetSchedule n)
    (j : Nat)
    (h :
      Lemma5iLeaderWaveResetWitness
        ring D start word j) :
    clockResetSeenAux
        ring
        (PPL.shiftRight ring start j)
        D word =
      true := by
  unfold Lemma5iLeaderWaveResetWitness at h
  rcases h with
    ⟨before, after, hword, _hsub, hreset⟩
  rw [hword]
  exact
    q20169ClockResetSeen_of_prefix_reset
      ring D
      (PPL.shiftRight ring start j)
      before after
      (PPL.shiftRight ring start j)
      hreset

private theorem q20169FoldlAnd_true_of_all_true
    (xs : List Bool)
    (h : forall b, b ∈ xs -> b = true) :
    xs.foldl
        (fun a b => a && b) true =
      true := by
  induction xs with
  | nil =>
      rfl
  | cons a rest ih =>
      have ha :
          a = true :=
        h a (by simp)
      have hrest :
          forall b, b ∈ rest -> b = true := by
        intro b hb
        exact h b (by simp [hb])
      simp [List.foldl_cons, ha]
      exact ih hrest

private theorem q20169AllAgentsTrue_of_pointwise
    {n : Nat}
    (p : Fin n -> Bool)
    (h : forall i, p i = true) :
    allAgentsB p = true := by
  unfold allAgentsB
  apply q20169FoldlAnd_true_of_all_true
  intro b hb
  rw [List.mem_ofFn] at hb
  rcases hb with ⟨i, hi⟩
  rw [← hi]
  exact h i

theorem lemma5iWaveResetFrontierHitContinueRow_proved :
    Lemma5iWaveResetFrontierHitContinueRow := by
  unfold Lemma5iWaveResetFrontierHitContinueRow
  intro n psi kappa
  intro _hn3 _hpsi ring D pre e q
  intro hactive _hqn hhost hsub hnext hwit he hcont

  have heq :
      e =
        PPL.shiftRight ring
          (lemma5iLeaderWaveStart ring D) q :=
    he.trans hhost

  have hresetHost :
      clockResetAt
          ring
          (runPPL ring D pre)
          (lemma5iLeaderWaveHost ring D pre)
          (lemma5iLeaderWaveHost ring D pre) =
        true :=
    q20169HostSelfReset ring D pre hactive

  have hresetQ :
      clockResetAt
          ring
          (runPPL ring D pre)
          (PPL.shiftRight ring
            (lemma5iLeaderWaveStart ring D) q)
          (PPL.shiftRight ring
            (lemma5iLeaderWaveStart ring D) q) =
        true := by
    simpa [hhost] using hresetHost

  unfold Lemma5iLeaderWaveResetFrontierAt
  dsimp only
  refine
    ⟨q + 1, hcont, ?_, ?_, ?_, ?_⟩

  · have hloc :
        lemma5iLeaderWaveHost ring D (pre ++ [e]) =
          if e = lemma5iLeaderWaveHost ring D pre then
            ring.rightNeighbor
              (lemma5iLeaderWaveHost ring D pre)
          else
            lemma5iLeaderWaveHost ring D pre :=
      lemma5iLeaderWaveLocationOneStep_proved
        ring D pre e hactive
    rw [if_pos he] at hloc
    calc
      lemma5iLeaderWaveHost ring D (pre ++ [e]) =
          ring.rightNeighbor
            (lemma5iLeaderWaveHost ring D pre) :=
        hloc
      _ =
          ring.rightNeighbor
            (PPL.shiftRight ring
              (lemma5iLeaderWaveStart ring D) q) := by
        rw [hhost]
      _ =
          PPL.shiftRight ring
            (lemma5iLeaderWaveStart ring D) (q + 1) :=
        (q20169ShiftRight_succ
          ring
          (lemma5iLeaderWaveStart ring D)
          q).symm

  · rw [
      q20169SeqR_succ
        ring
        (lemma5iLeaderWaveStart ring D)
        q
    ]
    apply List.append_sublist_iff.mpr
    refine ⟨pre, [e], rfl, hsub, ?_⟩
    rw [← heq]
    exact List.Sublist.refl _

  · have hnext' :
        Not
          ((PPL.seqR ring
              (lemma5iLeaderWaveStart ring D) q ++
            [PPL.shiftRight ring
              (lemma5iLeaderWaveStart ring D) q]).Sublist
            pre) := by
      rw [← q20169SeqR_succ
        ring
        (lemma5iLeaderWaveStart ring D)
        q]
      exact hnext

    rw [
      q20169SeqR_succ
        ring
        (lemma5iLeaderWaveStart ring D)
        (q + 1),
      q20169SeqR_succ
        ring
        (lemma5iLeaderWaveStart ring D)
        q
    ]

    exact
      q20169SublistAppendSingletonNoDouble
        pre
        (PPL.seqR ring
          (lemma5iLeaderWaveStart ring D) q)
        (PPL.shiftRight ring
          (lemma5iLeaderWaveStart ring D) q)
        (PPL.shiftRight ring
          (lemma5iLeaderWaveStart ring D) (q + 1))
        e
        hnext'

  · intro j hj
    by_cases hjq : j < q
    · exact
        q20169ResetWitness_append
          ring D
          (lemma5iLeaderWaveStart ring D)
          pre e j
          (hwit j hjq)
    · have hjqeq : j = q := by
        omega
      subst j
      unfold Lemma5iLeaderWaveResetWitness
      refine
        ⟨pre, [], ?_, hsub, hresetQ⟩
      rw [heq]

theorem lemma5iWaveResetFrontierHitFinishRow_proved :
    Lemma5iWaveResetFrontierHitFinishRow := by
  unfold Lemma5iWaveResetFrontierHitFinishRow
  intro n psi kappa
  intro _hn3 _hpsi ring D pre e q
  intro hactive _hqn hhost hsub _hnext hwit he hfinish

  have heq :
      e =
        PPL.shiftRight ring
          (lemma5iLeaderWaveStart ring D) q :=
    he.trans hhost

  have hresetHost :
      clockResetAt
          ring
          (runPPL ring D pre)
          (lemma5iLeaderWaveHost ring D pre)
          (lemma5iLeaderWaveHost ring D pre) =
        true :=
    q20169HostSelfReset ring D pre hactive

  have hresetQ :
      clockResetAt
          ring
          (runPPL ring D pre)
          (PPL.shiftRight ring
            (lemma5iLeaderWaveStart ring D) q)
          (PPL.shiftRight ring
            (lemma5iLeaderWaveStart ring D) q) =
        true := by
    simpa [hhost] using hresetHost

  have hdone :
      (PPL.seqR ring
        (lemma5iLeaderWaveStart ring D)
        (q + 1)).Sublist
          (pre ++ [e]) := by
    rw [
      q20169SeqR_succ
        ring
        (lemma5iLeaderWaveStart ring D)
        q
    ]
    apply List.append_sublist_iff.mpr
    refine ⟨pre, [e], rfl, hsub, ?_⟩
    rw [← heq]
    exact List.Sublist.refl _

  refine And.intro ?_ ?_

  · simpa [hfinish] using hdone

  · have hwpost :
        forall j : Nat,
          j < n ->
            Lemma5iLeaderWaveResetWitness
              ring D
              (lemma5iLeaderWaveStart ring D)
              (pre ++ [e]) j := by
      intro j hj
      by_cases hjq : j < q
      · exact
          q20169ResetWitness_append
            ring D
            (lemma5iLeaderWaveStart ring D)
            pre e j
            (hwit j hjq)
      · have hjqeq : j = q := by
          omega
        subst j
        unfold Lemma5iLeaderWaveResetWitness
        refine
          ⟨pre, [], ?_, hsub, hresetQ⟩
        rw [heq]

    unfold allClockResetsSeenB
    apply q20169AllAgentsTrue_of_pointwise
    intro x

    let j :=
      PPL.cyclicOffset ring
        (lemma5iLeaderWaveStart ring D) x

    have hjn : j < n := by
      dsimp only [j]
      exact
        q20169CyclicOffset_lt
          ring
          (lemma5iLeaderWaveStart ring D)
          x

    have hwx :
        Lemma5iLeaderWaveResetWitness
          ring D
          (lemma5iLeaderWaveStart ring D)
          (pre ++ [e]) j :=
      hwpost j hjn

    have hseen :
        clockResetSeenAux
            ring
            (PPL.shiftRight ring
              (lemma5iLeaderWaveStart ring D) j)
            D
            (pre ++ [e]) =
          true :=
      q20169ResetWitness_seen
        ring D
        (lemma5iLeaderWaveStart ring D)
        (pre ++ [e]) j
        hwx

    have hsite :
        PPL.shiftRight ring
            (lemma5iLeaderWaveStart ring D) j =
          x := by
      dsimp only [j]
      exact
        q20169ShiftRight_cyclicOffset
          ring
          (lemma5iLeaderWaveStart ring D)
          x

    rw [hsite] at hseen
    exact hseen

end PPL.Modes.Lemma5

#print axioms PPL.Modes.Lemma5.lemma5iWaveResetFrontierHitContinueRow_proved
#print axioms PPL.Modes.Lemma5.lemma5iWaveResetFrontierHitFinishRow_proved
