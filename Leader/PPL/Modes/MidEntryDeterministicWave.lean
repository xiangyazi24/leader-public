import Leader.PPL.Modes.MidEntryResetModeCap
import Leader.PPL.Modes.StoppedClockSuffixCorrected
import Leader.PPL.Modes.SignalLineageLocal
import Leader.PPL.ReachCPB.WordBound
import Leader.PPL.MainTheorem.Kappa

/-!
# Lemma 5(i), deterministic form: one clockwise maximum-reset wave

Paper Lemma 5(i) shows that from `C_PB` a random schedule reaches the
mid-phase set `C_mid` (a leader is present, every clock is at most
`kappa / 2`, every mode is Construct) with high probability.  Once the
scheduler is chosen, the probabilistic encounter/TTL argument is not needed:
pick a leader `root` and schedule the clockwise word

  `seqR ring root n = root, root+1, ..., root+(n-1)`.

*First letter.* The initiator `root` is a leader, so Algorithm 4 line 35 arms
its right signal to the maximum `kappa`.

*Every letter.* If the initiator is a leader or already carries
`signalR = kappa`, then the armed left signal equals `kappa`, which dominates
any responder signal (a value in `Fin (kappa + 1)`), including ties.  Hence
line 39 resets both endpoint clocks to `0`, line 41 hands the responder the
signal `kappa` with its hit counter reset to `0` (so the TTL test at line 43
cannot fire when `psi >= 2`), and lines 49--50 write
`mode := (clock == kappa) = false` since `0 < kappa`.  The later
CreateLeader/MoveToken/EliminateLeaders suffix does not write clock, mode or
signalR (landed projections `clockSuffixPairProjection`,
`postDetermineModeModeStable`, `postDetermineModeSignalStable`).

*Induction.* After letter `k` the responder `root+(k+1)` carries `kappa`,
which is exactly the initiator of the next letter.  Every site touched so far
has clock `0` and Construct mode, and later letters touch only sites that they
reset again.  After `n` letters every site has been touched.  `C_PB` is closed
under the literal transition (`cpb_run_closed`), so a leader is still present,
and the endpoint lies in `C_mid`.

This file is only about the literal `PPL.protocol`; no hypothesis is carried
beyond `3 <= n`, `2 <= psi`, `0 < kappa` and `C_PB`.
-/

namespace PPL.Modes.Lemma5

set_option autoImplicit false
set_option Elab.async false

open PPL.Probability
open PPL.Modes.SignalLineage

/-! ## Boolean fold helpers -/

private theorem wave_foldl_or_true
    (xs : List Bool) :
    xs.foldl (fun acc b => acc || b) true = true := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      simp only [List.foldl_cons, Bool.true_or]
      exact ih

private theorem wave_foldl_or_true_of_mem
    (xs : List Bool) (hmem : true ∈ xs) :
    xs.foldl (fun acc b => acc || b) false = true := by
  induction xs with
  | nil => simp at hmem
  | cons b xs ih =>
      rcases List.mem_cons.mp hmem with hb | ht
      · subst b
        simp only [List.foldl_cons, Bool.false_or]
        exact wave_foldl_or_true xs
      · cases b
        · simp only [List.foldl_cons, Bool.false_or]
          exact ih ht
        · simp only [List.foldl_cons, Bool.false_or]
          exact wave_foldl_or_true xs

private theorem wave_foldl_and_true
    (xs : List Bool) (hall : ∀ b, b ∈ xs → b = true) :
    xs.foldl (fun acc b => acc && b) true = true := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      have hb : b = true := hall b (List.mem_cons_self ..)
      subst hb
      simp only [List.foldl_cons, Bool.true_and]
      exact ih (fun c hc => hall c (List.mem_cons_of_mem _ hc))

private theorem wave_leaderPresent_of_exists
    {n psi kappa : Nat} (C : Config n psi kappa)
    (h : ∃ i : Fin n, (C i).leader = true) :
    leaderPresent C = true := by
  obtain ⟨i, hi⟩ := h
  unfold leaderPresent
  apply wave_foldl_or_true_of_mem
  rw [List.mem_ofFn]
  exact ⟨i, hi⟩

private theorem wave_allAgentsB_of_forall
    {n : Nat} (p : Fin n → Bool) (h : ∀ i, p i = true) :
    allAgentsB p = true := by
  unfold allAgentsB
  apply wave_foldl_and_true
  intro b hb
  rw [List.mem_ofFn] at hb
  obtain ⟨i, hi⟩ := hb
  rw [← hi]
  exact h i

/-! ## Ring index arithmetic -/

private theorem wave_rightNeighbor_ne_self
    {n : Nat} (hn3 : 3 <= n) (ring : DirectedRing n) (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  simp only [DirectedRing.rightNeighbor] at hv
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : e.val + 1 = n := by omega
    rw [heq, Nat.mod_self] at hv
    omega

private theorem wave_shiftRight_zero
    {n : Nat} (ring : DirectedRing n) (root : Fin n) :
    PPL.shiftRight ring root 0 = root := by
  apply Fin.ext
  simp only [PPL.shiftRight, Nat.add_zero]
  exact Nat.mod_eq_of_lt root.isLt

private theorem wave_shiftRight_succ
    {n : Nat} (ring : DirectedRing n) (root : Fin n) (k : Nat) :
    PPL.shiftRight ring root (k + 1) =
      ring.rightNeighbor (PPL.shiftRight ring root k) := by
  apply Fin.ext
  simp only [PPL.shiftRight, DirectedRing.rightNeighbor]
  rw [Nat.mod_add_mod]
  congr 1

private theorem wave_shiftRight_surj
    {n : Nat} (ring : DirectedRing n) (root i : Fin n) :
    ∃ j : Nat, j < n ∧ PPL.shiftRight ring root j = i := by
  refine ⟨(i.val + n - root.val) % n, Nat.mod_lt _ ring.hn, ?_⟩
  apply Fin.ext
  simp only [PPL.shiftRight]
  rw [Nat.add_mod_mod]
  have hsum : root.val + (i.val + n - root.val) = i.val + n := by
    have := root.isLt
    omega
  rw [hsum, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt i.isLt

/-! ## The clockwise word and run splitting -/

private theorem wave_seqR_succ
    {n : Nat} (ring : DirectedRing n) (root : Fin n) (k : Nat) :
    PPL.seqR ring root (k + 1) =
      PPL.seqR ring root k ++ [PPL.shiftRight ring root k] := by
  apply List.ext_getElem
  · simp [PPL.seqR]
  · intro i h1 h2
    simp only [PPL.seqR, List.getElem_ofFn]
    rw [List.getElem_append]
    split
    · simp
    · rename_i hi
      simp only [List.length_ofFn] at hi
      have h1' : i < k + 1 := by
        simpa [PPL.seqR] using h1
      have hik : i = k := by
        omega
      subst hik
      simp

private theorem wave_seqR_length
    {n : Nat} (ring : DirectedRing n) (root : Fin n) (k : Nat) :
    (PPL.seqR ring root k).length = k := by
  simp [PPL.seqR]

private theorem wave_runPPL_append
    {n psi kappa : Nat} (ring : DirectedRing n) (C : Config n psi kappa)
    (w1 w2 : DetSchedule n) :
    runPPL ring C (w1 ++ w2) = runPPL ring (runPPL ring C w1) w2 := by
  induction w1 generalizing C with
  | nil => rfl
  | cons e rest ih =>
      simp only [List.cons_append, runPPL, runPopulationSchedule]
      exact ih _

private theorem wave_runPPL_single
    {n psi kappa : Nat} (ring : DirectedRing n) (C : Config n psi kappa)
    (e : Fin n) :
    runPPL ring C [e] = pplStep ring C e := rfl

private theorem wave_pplStep_other
    {n psi kappa : Nat} (ring : DirectedRing n) (C : Config n psi kappa)
    (e x : Fin n) (hxe : x ≠ e) (hxr : x ≠ ring.rightNeighbor e) :
    pplStep ring C e x = C x := by
  simp [pplStep, PopulationProtocol.step, hxe, hxr]

/-! ## One maximum-signal letter -/

/--
**Top-signal wave step.**  If the initiator `e` of the scheduled letter is a
leader or already carries the maximum right signal `kappa`, then after the
full literal P_PL interaction both endpoints have clock `0` and Construct mode,
and the responder `rightNeighbor e` carries `signalR = kappa`.

Proof: the pre-letter reset test `clockResetAt` holds at both endpoints (armed
left signal `kappa > 0`), so the landed corrected reset row gives clock `0`,
and the landed mode-cap row (`mode = true -> clock = kappa`) forces
Construct.  The signal part is the landed DetermineMode responder trichotomy:
the armed left signal `kappa` is not below any responder signal, so the
left-wins row installs exactly `kappa` at the responder; the full-step
projection `postDetermineModeSignalStable` lifts it through the suffix.
-/
theorem lemma5iTopWaveStep
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hkappa : 0 < kappa)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e : Fin n)
    (htop : Or ((C e).leader = true) ((C e).signalR.val = kappa)) :
    let C' := pplStep ring C e
    And ((C' e).clock.val = 0)
      (And ((C' e).mode = false)
        (And ((C' (ring.rightNeighbor e)).clock.val = 0)
          (And ((C' (ring.rightNeighbor e)).mode = false)
            ((C' (ring.rightNeighbor e)).signalR.val = kappa)))) := by
  have hself : ring.rightNeighbor e ≠ e :=
    wave_rightNeighbor_ne_self hn3 ring e
  have harmed : armedSignalVal (C e) = kappa := by
    unfold armedSignalVal
    by_cases hl : (C e).leader = true
    · simp [hl]
    · have hs : (C e).signalR.val = kappa := by
        rcases htop with h | h
        · exact absurd h hl
        · exact h
      simp [hl, hs]
  have hreset : ∀ x : Fin n, (x = e ∨ x = ring.rightNeighbor e) →
      clockResetAt ring C x e = true := by
    intro x hx
    unfold clockResetAt
    apply decide_eq_true
    refine ⟨hx, Or.inl ?_⟩
    have ha : (if (C e).leader = true then kappa else (C e).signalR.val) =
        kappa := by
      simpa [armedSignalVal] using harmed
    rw [ha]
    exact hkappa
  have hclock : ∀ x : Fin n, (x = e ∨ x = ring.rightNeighbor e) →
      (pplStep ring C e x).clock.val = 0 := fun x hx =>
    PPL.Probability.stoppedClockSuffixBoundsCorrected_conjunct1
      n psi kappa ring C x e hpsi (hreset x hx)
  have hmode : ∀ x : Fin n, (x = e ∨ x = ring.rightNeighbor e) →
      (pplStep ring C e x).mode = false := by
    intro x hx
    cases hm : (pplStep ring C e x).mode with
    | false => rfl
    | true =>
        have hcap :=
          lemma5iMidResetModeCapStep_proved hpsi ring C x e (hreset x hx) hm
        have h0 := hclock x hx
        omega
  -- responder signal
  have hd :=
    determineModeSignalProjection (psi := psi) (kappa := kappa) hpsi
      (C e) (C (ring.rightNeighbor e))
  have hs :=
    step_signal_projection_of_stable postDetermineModeSignalStable
      hpsi ring C e hself
  dsimp only at hd hs
  have hcases := hd.2.2
  unfold DetermineModeResponderCases at hcases
  dsimp only at hcases
  have hdetMax :
      (PPL.determineMode (C e) (C (ring.rightNeighbor e))).2.signalR.val =
        kappa := by
    rcases hcases with hzero | hrest
    · have : kappa = 0 := harmed.symm.trans hzero.1
      omega
    · rcases hrest with hleft | hright
      · exact hleft.2.2.1.trans harmed
      · have hlt : kappa < (C (ring.rightNeighbor e)).signalR.val := by
          have h1 := hright.1
          rw [harmed] at h1
          exact h1
        have hrlt := (C (ring.rightNeighbor e)).signalR.isLt
        omega
  have hsig :
      (pplStep ring C e (ring.rightNeighbor e)).signalR.val = kappa := by
    calc
      (pplStep ring C e (ring.rightNeighbor e)).signalR.val =
          (PPL.determineMode (C e)
            (C (ring.rightNeighbor e))).2.signalR.val := by
        simpa [PPL.Probability.pplStep,
          PPL.Modes.SignalLineage.step] using congrArg Fin.val hs.2.2.1
      _ = kappa := hdetMax
  exact ⟨hclock e (Or.inl rfl), hmode e (Or.inl rfl),
    hclock _ (Or.inr rfl), hmode _ (Or.inr rfl), hsig⟩

/-! ## Induction along the clockwise word -/

/-- Wave invariant after the first `k` letters of `seqR ring root k`: the next
initiator `root + k` is armed (leader or maximum signal), and if `k > 0` every
site `root + j` with `j <= k` has clock `0` and Construct mode. -/
private theorem wave_invariant
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hkappa : 0 < kappa)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (root : Fin n)
    (hroot : (C root).leader = true) :
    ∀ k : Nat,
      let D := runPPL ring C (PPL.seqR ring root k)
      And (Or ((D (PPL.shiftRight ring root k)).leader = true)
              ((D (PPL.shiftRight ring root k)).signalR.val = kappa))
        (∀ j : Nat, j <= k → 0 < k →
          And ((D (PPL.shiftRight ring root j)).clock.val = 0)
            ((D (PPL.shiftRight ring root j)).mode = false)) := by
  intro k
  induction k with
  | zero =>
      dsimp only
      refine ⟨?_, ?_⟩
      · left
        rw [wave_shiftRight_zero]
        exact hroot
      · intro j _ h
        exact absurd h (Nat.lt_irrefl 0)
  | succ k ih =>
      dsimp only at ih ⊢
      obtain ⟨harm, hgood⟩ := ih
      let D := runPPL ring C (PPL.seqR ring root k)
      let e := PPL.shiftRight ring root k
      have hrun : runPPL ring C (PPL.seqR ring root (k + 1)) =
          pplStep ring D e := by
        rw [wave_seqR_succ, wave_runPPL_append, wave_runPPL_single]
      have hnext : PPL.shiftRight ring root (k + 1) = ring.rightNeighbor e :=
        wave_shiftRight_succ ring root k
      have hw := lemma5iTopWaveStep hn3 hpsi hkappa ring D e harm
      dsimp only at hw
      obtain ⟨hc1, hm1, hc2, hm2, hs2⟩ := hw
      rw [hrun, hnext]
      refine ⟨Or.inr hs2, ?_⟩
      intro j hj _
      by_cases hjk : j = k + 1
      · subst hjk
        rw [hnext]
        exact ⟨hc2, hm2⟩
      · have hjle : j <= k := by omega
        by_cases hxe : PPL.shiftRight ring root j = e
        · rw [hxe]
          exact ⟨hc1, hm1⟩
        · by_cases hxr : PPL.shiftRight ring root j = ring.rightNeighbor e
          · rw [hxr]
            exact ⟨hc2, hm2⟩
          · rw [wave_pplStep_other ring D e _ hxe hxr]
            have hkpos : 0 < k := by
              rcases Nat.eq_zero_or_pos k with h0 | hpos
              · exfalso
                apply hxe
                have hj0 : j = 0 := by omega
                subst hj0
                subst h0
                rfl
              · exact hpos
            exact hgood j hjle hkpos

/-! ## Headline -/

/--
**Lemma 5(i), deterministic maximum-reset wave.**  For `3 <= n`,
`2 <= psi`, `0 < kappa`, every configuration in `C_PB` has a current leader
`root` such that the clockwise word `seqR ring root n` (exactly `n` letters,
`root, root+1, ..., root+(n-1)`) ends in the mid-phase set: at the endpoint a
leader is present, every clock is `0 <= kappa / 2`, and every mode is
Construct.

This replaces the paper's probabilistic encounter/TTL argument for Lemma 5(i)
by an explicit schedule; it is a statement about the literal `PPL.protocol`
endpoint, not about a prefix.
-/
theorem lemma5iCPB_seqR_midPhysicalB
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hkappa : 0 < kappa)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (hCPB : PPL.CPB ring C) :
    Exists fun root : Fin n =>
      And ((C root).leader = true)
        (let word : DetSchedule n := PPL.seqR ring root n
         And (word.length = n)
           (PPL.Modes.Lemma5.midPhysicalB
             (PPL.Probability.runPPL ring C word) = true)) := by
  have hCPB' := hCPB
  unfold PPL.CPB PPL.CPBCore at hCPB'
  obtain ⟨⟨root, hroot⟩, _⟩ := hCPB'
  refine ⟨root, hroot, ?_⟩
  dsimp only
  refine ⟨wave_seqR_length ring root n, ?_⟩
  let D := runPPL ring C (PPL.seqR ring root n)
  have hinv := wave_invariant hn3 hpsi hkappa ring C root hroot n
  dsimp only at hinv
  have hall : ∀ i : Fin n, And ((D i).clock.val = 0) ((D i).mode = false) := by
    intro i
    obtain ⟨j, hjn, hji⟩ := wave_shiftRight_surj ring root i
    rw [← hji]
    exact hinv.2 j (Nat.le_of_lt hjn) (by omega)
  have hcpbD : PPL.CPB ring D :=
    PPL.Convergence.ReachCPB.cpb_run_closed hn3 hpsi ring C
      (PPL.seqR ring root n) hCPB
  have hleadD : ∃ i : Fin n, (D i).leader = true := by
    have h := hcpbD
    unfold PPL.CPB PPL.CPBCore at h
    exact h.1
  show midPhysicalB D = true
  unfold midPhysicalB
  rw [wave_leaderPresent_of_exists D hleadD, Bool.true_and]
  apply wave_allAgentsB_of_forall
  intro i
  have hi := hall i
  simp [hi.1, hi.2]

/--
**Theorem-1 wrapper.**  The same deterministic wave at the Theorem-1 clock parameter
`kappa = theorem1Kappa psi`, which is positive for `2 <= psi`.
-/
theorem theorem1L5i_seqR_midPhysicalB
    {n psi : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (C : Config n psi (PPL.theorem1Kappa psi))
    (hCPB : PPL.CPB ring C) :
    Exists fun root : Fin n =>
      And ((C root).leader = true)
        (PPL.Modes.Lemma5.midPhysicalB
          (PPL.Probability.runPPL ring C
            (PPL.seqR ring root n)) = true) := by
  have hkappa : 0 < PPL.theorem1Kappa psi := by
    unfold PPL.theorem1Kappa PPL.theorem1C1 PPL.theorem1C17
    omega
  obtain ⟨root, hroot, _, hmid⟩ :=
    lemma5iCPB_seqR_midPhysicalB hn3 hpsi hkappa ring C hCPB
  exact ⟨root, hroot, hmid⟩

end PPL.Modes.Lemma5

#print axioms PPL.Modes.Lemma5.lemma5iTopWaveStep
#print axioms PPL.Modes.Lemma5.lemma5iCPB_seqR_midPhysicalB
#print axioms PPL.Modes.Lemma5.theorem1L5i_seqR_midPhysicalB
