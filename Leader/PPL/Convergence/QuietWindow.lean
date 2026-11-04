import Leader.PPL.Convergence.ConstructCoupling

namespace PPL.Convergence.ConstructCoupling

set_option autoImplicit false
set_option Elab.async false

open PPL.Probability

/-
Truth check for Lemma5iiQuietWindowCoupling.

The statement is TRUE as written.

DetermineMode is the only phase of one literal P_PL interaction that writes
the mode field.  Algorithm 2 lines 4--9 do not write mode; leaderBirth keeps
the old mode; Algorithm 3 changes only token/id/birth fields and its birth also
keeps mode; Algorithm 5 is framed by Elim.otherView and therefore keeps mode.

Hence the mode stored at the next configuration boundary is exactly the mode
written by DetermineMode in the preceding interaction.  Since constructAlong
requires every stored mode to be Construct (= false) at every boundary,
including the final boundary, its tail condition rules out a hidden
Construct -> Detect -> Construct flip inside an interaction: there is no later
writer that could perform the second flip.

The proof below is stronger than the frozen Prop: it needs only 3 <= n,
2 <= psi, and constructAlong=true.  The midPhysicalB, horizon, c, kappa and
n <= 2^psi hypotheses are counting-layer hypotheses and are irrelevant to
this deterministic implication.  Therefore Lemma5iiWordBound does not change.
-/

/-- Algorithm 2 through line 9, immediately before its two token passes,
written locally only to expose the mode frame. -/
private def preTokenModePair
    {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa) :
    PPL.State psi kappa × PPL.State psi kappa :=
  let s := PPL.createLeaderThroughLine6 hpsi l r
  let l0 := s.left
  let r0 := s.right
  let tmp := s.tmp
  let r1 :=
    if r0.mode = false then
      { r0 with dist := tmp }
    else
      r0
  let l1 :=
    if r1.leader = true then
      { l0 with last := true }
    else if r1.dist.val = 0 ∨ r1.dist.val = psi then
      { l0 with last := false }
    else
      { l0 with last := r1.last }
  (l1, r1)

/-- Algorithm-2 line 6 preserves the post-DetermineMode mode fields. -/
private theorem line6_modes
    {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa) :
    let d := PPL.determineMode l r
    let s := PPL.createLeaderThroughLine6 hpsi l r
    s.left.mode = d.1.mode ∧
      s.right.mode = d.2.mode := by
  dsimp only [PPL.createLeaderThroughLine6]
  split
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

/-- Algorithm-2 lines 7--9 also preserve those mode fields. -/
private theorem preTokenModePair_modes
    {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa) :
    let d := PPL.determineMode l r
    let q := preTokenModePair hpsi l r
    q.1.mode = d.1.mode ∧
      q.2.mode = d.2.mode := by
  let s := PPL.createLeaderThroughLine6 hpsi l r
  have hs := line6_modes hpsi l r
  have hp :
      let q := preTokenModePair hpsi l r
      q.1.mode = s.left.mode ∧
        q.2.mode = s.right.mode := by
    dsimp only [preTokenModePair]
    all_goals try (split <;> try dsimp only)
    all_goals try (split <;> try dsimp only)
    all_goals try (split <;> try dsimp only)
    all_goals exact ⟨rfl, rfl⟩
  dsimp only at hs hp ⊢
  exact
    ⟨hp.1.trans hs.1,
      hp.2.trans hs.2⟩

/-- The two Algorithm-3 token passes preserve the mode fields as well. -/
private theorem createLeader_modes
    {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa) :
    let d := PPL.determineMode l r
    let q := PPL.createLeader hpsi l r
    q.1.mode = d.1.mode ∧
      q.2.mode = d.2.mode := by
  let p := preTokenModePair hpsi l r
  let b := PPL.moveToken hpsi .black p.1 p.2
  let w := PPL.moveToken hpsi .white b.1 b.2
  have hdef :
      PPL.createLeader hpsi l r = w := by
    rfl
  have hp := preTokenModePair_modes hpsi l r
  have hb :=
    moveToken_modes hpsi PPL.TokenKind.black p.1 p.2
  have hw :=
    moveToken_modes hpsi PPL.TokenKind.white b.1 b.2
  dsimp only at hp hb hw
  rw [hdef]
  exact
    ⟨hw.1.trans (hb.1.trans hp.1),
      hw.2.trans (hb.2.trans hp.2)⟩

/-- Algorithm 5 does not write mode. -/
private theorem eliminateLeaders_modes
    {psi kappa : Nat}
    (l r : PPL.State psi kappa) :
    let q := PPL.eliminateLeaders l r
    q.1.mode = l.mode ∧
      q.2.mode = r.mode := by
  dsimp only
  have hl := PPL.Elim.otherView_eliminateLeaders_left l r
  have hr := PPL.Elim.otherView_eliminateLeaders_right l r
  exact
    ⟨congrArg
        (fun z : PPL.Elim.OtherFields psi kappa => z.mode) hl,
      congrArg
        (fun z : PPL.Elim.OtherFields psi kappa => z.mode) hr⟩

/-- Public pair-level seam: the mode stored at the end of a literal P_PL
interaction is exactly the mode written by DetermineMode. -/
theorem postDetermineModeModeStable
    {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa) :
    let d := PPL.determineMode l r
    let q := PPL.ppl hpsi l r
    q.1.mode = d.1.mode ∧
      q.2.mode = d.2.mode := by
  let c := PPL.createLeader hpsi l r
  let q := PPL.eliminateLeaders c.1 c.2
  have hc := createLeader_modes hpsi l r
  have he := eliminateLeaders_modes c.1 c.2
  have hdef :
      PPL.ppl hpsi l r = q := by
    rfl
  dsimp only at hc he
  dsimp only
  rw [hdef]
  exact
    ⟨he.1.trans hc.1,
      he.2.trans hc.2⟩

private theorem rightNeighbor_ne_self_quiet
    {n : Nat} (ring : DirectedRing n)
    (hn2 : 2 ≤ n) (i : Fin n) :
    ring.rightNeighbor i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [DirectedRing.rightNeighbor] at hv
  by_cases hlt : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : i.val + 1 = n := by
      omega
    rw [heq, Nat.mod_self] at hv
    omega

/-- Configuration-level seam for the two scheduled endpoints. -/
theorem pplStep_endpoint_modes
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa) (e : Fin n) :
    let j := ring.rightNeighbor e
    let d := PPL.determineMode (C e) (C j)
    (PPL.Probability.pplStep ring C e e).mode = d.1.mode ∧
      (PPL.Probability.pplStep ring C e j).mode = d.2.mode := by
  dsimp only
  have hp :=
    postDetermineModeModeStable hpsi
      (C e) (C (ring.rightNeighbor e))
  dsimp only at hp
  have hne :
      ring.rightNeighbor e ≠ e :=
    rightNeighbor_ne_self_quiet ring (by omega) e
  constructor
  · simpa [PPL.Probability.pplStep,
      PopulationProtocol.step, PPL.protocol,
      PPL.transition, hpsi] using hp.1
  · simpa [PPL.Probability.pplStep,
      PopulationProtocol.step, PPL.protocol,
      PPL.transition, hpsi, hne] using hp.2

private theorem foldl_and_false
    (xs : List Bool) :
    xs.foldl (fun acc b => acc && b) false = false := by
  induction xs with
  | nil =>
      rfl
  | cons b xs ih =>
      simp only [List.foldl_cons]
      cases b <;> simpa using ih

private theorem foldl_and_false_of_mem
    (xs : List Bool)
    (hmem : false ∈ xs) :
    xs.foldl (fun acc b => acc && b) true = false := by
  induction xs with
  | nil =>
      simp at hmem
  | cons b xs ih =>
      rcases List.mem_cons.mp hmem with hb | htail
      · subst b
        simp only [List.foldl_cons]
        change
          xs.foldl (fun acc b => acc && b) false = false
        exact foldl_and_false xs
      · cases b with
        | false =>
            simp only [List.foldl_cons]
            change
              xs.foldl (fun acc b => acc && b) false = false
            exact foldl_and_false xs
        | true =>
            simp only [List.foldl_cons]
            change
              xs.foldl (fun acc b => acc && b) true = false
            exact ih htail

private theorem allAgentsStoredConstruct_of_true
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (h :
      PPL.Modes.Lemma5.allAgentsB
        (fun i : Fin n =>
          decide ((C i).mode = false)) = true) :
    ∀ i : Fin n, (C i).mode = false := by
  intro i
  cases hm : (C i).mode with
  | false =>
      rfl
  | true =>
      have hmem :
          false ∈
            List.ofFn
              (fun j : Fin n =>
                decide ((C j).mode = false)) := by
        rw [List.mem_ofFn]
        refine ⟨i, ?_⟩
        simp [hm]
      have hf :=
        foldl_and_false_of_mem
          (List.ofFn
            (fun j : Fin n =>
              decide ((C j).mode = false)))
          hmem
      unfold PPL.Modes.Lemma5.allAgentsB at h
      rw [hf] at h
      contradiction

/-- Any successful constructAlong word certifies that the configuration at
the beginning of that recursive suffix has every stored mode Construct. -/
private theorem constructAlong_start_allAgents
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (word : DetSchedule n)
    (h :
      PPL.Modes.Lemma5.constructAlong ring C word = true) :
    PPL.Modes.Lemma5.allAgentsB
        (fun i : Fin n =>
          decide ((C i).mode = false)) = true := by
  cases word with
  | nil =>
      simpa [PPL.Modes.Lemma5.constructAlong] using h
  | cons e rest =>
      simp only [PPL.Modes.Lemma5.constructAlong, Bool.and_eq_true] at h
      exact h.1

/-- Strong deterministic quiet-window bridge.  The counting-specific Lemma-5
hypotheses are not needed: constructAlong itself already implies the exact
post-DetermineMode condition interaction by interaction. -/
theorem constructAlong_implies_postDetermineModeConstructAlong
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (word : DetSchedule n)
    (hconstruct :
      PPL.Modes.Lemma5.constructAlong ring C word = true) :
    PostDetermineModeConstructAlong ring C word := by
  induction word generalizing C with
  | nil =>
      trivial
  | cons e rest ih =>
      simp only [PPL.Modes.Lemma5.constructAlong, Bool.and_eq_true] at hconstruct
      have hparts :=
        hconstruct
      have hnextAll :=
        constructAlong_start_allAgents
          ring
          (PPL.Probability.pplStep ring C e)
          rest hparts.2
      have hstored :=
        allAgentsStoredConstruct_of_true
          (PPL.Probability.pplStep ring C e)
          hnextAll
      have hm :=
        pplStep_endpoint_modes
          hn3 hpsi ring C e
      dsimp only at hm
      change
        PostDetermineModeConstructAt ring C e ∧
          PostDetermineModeConstructAlong ring
            (PPL.Probability.pplStep ring C e) rest
      constructor
      · change
          (PPL.determineMode
              (C e) (C (ring.rightNeighbor e))).1.mode = false ∧
            (PPL.determineMode
              (C e) (C (ring.rightNeighbor e))).2.mode = false
        exact
          ⟨hm.1.symm.trans (hstored e),
            hm.2.symm.trans
              (hstored (ring.rightNeighbor e))⟩
      · exact
          ih
            (C := PPL.Probability.pplStep ring C e)
            hparts.2

/-- The frozen Wave-3 quiet-window node is true without changing its statement
or the Lemma-5(ii) failure event. -/
theorem lemma5iiQuietWindowCoupling :
    Lemma5iiQuietWindowCoupling := by
  intro n psi kappa c
  intro hn3 hpsi _hc _hkappa _hnpow
  intro ring C word _hmid _hlen hconstruct
  exact
    constructAlong_implies_postDetermineModeConstructAlong
      hn3 hpsi ring C word hconstruct

end PPL.Convergence.ConstructCoupling

#print axioms PPL.Convergence.ConstructCoupling.postDetermineModeModeStable
#print axioms PPL.Convergence.ConstructCoupling.pplStep_endpoint_modes
#print axioms PPL.Convergence.ConstructCoupling.constructAlong_implies_postDetermineModeConstructAlong
#print axioms PPL.Convergence.ConstructCoupling.lemma5iiQuietWindowCoupling

