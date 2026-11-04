import Leader.PPL.SPLEntry.ForcingWordClosed
import Leader.PPL.Modes.MidEntryDeterministicWave
import Leader.PPL.Modes.ClockSuffixBridge
import Leader.PPL.Convergence.QuietWindow
import Leader.PPL.Convergence.ForcedConstructProtocol
import Leader.PPL.Elim.LiteralBridges
import Init.Omega
import Leader.PPL.MainTheorem.GeneralTargets
import Leader.PPL.MainTheorem.PossibleFromCPB

/-!
P_PL Theorem 1 cleanup, phase 2: the declarations of this file that served only the old
psi <= log2 n + 1 route to `theorem1Statement_proved` moved to
`Leader/Superseded/Theorem1LogWindow/Theorem1PossibleUpto8.lean`, namespace `PPL.Superseded.LogWindow`: `up8PB_run`, `up8SumIte_eq_countP`, `up8Unique_of_leaderCount`, `up8L18Hit_exists_prefix`, `up8RunLocalSchedule_eq_runPPL`, `upto8_tailSPL_of_mid`, `theorem1PossibleConvergenceUpto8_of_shortL17`, `theorem1Statement_of_shortL17`.
-/

/-!
# C.4 for `n ≤ 8`: possible convergence from a short deterministic L17 word

This file closes `Theorem1PossibleConvergenceUpto8` conditionally on one
input: every literal Algorithm-5 configuration satisfying `PPL.Elim.PB` has a
scheduler word of length at most `5 n²` ending with exactly one leader
(a deterministic Lemma 17).

The route avoids the From13 stopping-prefix / joint-good Boolean framework
entirely, because the target is only pointwise prefix-hit reachability.  From
an arbitrary configuration `C0` the chain is

1. `C0 → C1` with `CPB C1`: the deterministic L16 chain `reachCPB_exists_theorem1Kappa`;
2. `C1 → Cmid`: the deterministic maximum-reset wave
   `theorem1L5i_seqR_midPhysicalB`; at `Cmid` a leader is present, every
   clock is at most `kappa / 2` and every mode is Construct; `CPB` survives;
3. `Cmid → C17`: the short L17 word `w17` given by the hypothesis, run in the
   auxiliary protocol P_PL'; its literal view is the literal endpoint, which
   has one leader, so `C17` has a unique leader `root`, and `CPB C17` holds;
4. `C17 → SPL`: the proved scoped L18 forcing bridge on `l18Word ring root psi`
   gives a prefix `hit` of that word with `SPLAt root` in P_PL';
5. **Construct slack.**  One literal P_PL interaction raises a clock by at most
   one (DetermineMode lines 46--48; every other write is a reset to `0`), and
   the stored mode after the interaction is `clock == kappa`
   (`finishModes`).  From `Cmid` every clock is `≤ kappa / 2`, and the active
   word `w17 ++ hit` has length at most `5 n² + l18Length n psi ≤ 798` for
   `n ≤ 8`, while `kappa / 2 ≥ 55,206,272`.  Hence the whole run stays
   Construct, P_PL and P_PL' coincide along it (`runCoupling`), and the P_PL'
   SPL endpoint is the literal P_PL endpoint.
-/

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL.Probability
open PPLLResearchFormulation

/-! ## Boolean fold helpers -/

-- Step 6f (P_PL cleanup): the `true`-fold lemma is
-- `PPL.Theorem1General.theorem1FoldlAnd_true`; the private copy is gone.

/-- If every entry is `true`, the `&&` fold from `true` is `true`. -/
private theorem up8FoldlAnd_of_all
    (xs : List Bool) (hall : ∀ b, b ∈ xs → b = true) :
    xs.foldl (fun acc b => acc && b) true = true := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      have hb : b = true := hall b (List.mem_cons_self ..)
      subst hb
      simp only [List.foldl_cons, Bool.true_and]
      exact ih (fun c hc => hall c (List.mem_cons_of_mem _ hc))

private theorem up8AllAgentsB_of_forall
    {n : Nat} (p : Fin n → Bool) (h : ∀ i, p i = true) :
    PPL.Modes.Lemma5.allAgentsB p = true := by
  unfold PPL.Modes.Lemma5.allAgentsB
  apply up8FoldlAnd_of_all
  intro b hb
  rw [List.mem_ofFn] at hb
  obtain ⟨i, hi⟩ := hb
  rw [← hi]
  exact h i

private theorem up8Forall_of_allAgentsB
    {n : Nat} (p : Fin n → Bool)
    (h : PPL.Modes.Lemma5.allAgentsB p = true) :
    ∀ i, p i = true := by
  unfold PPL.Modes.Lemma5.allAgentsB at h
  have hall := (Theorem1General.theorem1FoldlAnd_true _ true h).2
  intro i
  exact hall (p i) (List.mem_ofFn.mpr ⟨i, rfl⟩)

/-! ## Construct slack: one interaction raises a clock by at most one -/

/--
DetermineMode (Algorithm 4) at the pair level: the initiator's clock does not
increase, the responder's clock increases by at most one, and each endpoint's
stored mode is Detect only when its clock equals `kappa` (lines 49--50).
-/
theorem upto8_determineMode_clock_mode
    {psi kappa : Nat}
    (l r : PPL.State psi kappa) :
    let d := PPL.determineMode l r
    d.1.clock.val ≤ l.clock.val ∧
      d.2.clock.val ≤ r.clock.val + 1 ∧
      (d.1.mode = true → d.1.clock.val = kappa) ∧
      (d.2.mode = true → d.2.clock.val = kappa) := by
  simp only [PPL.determineMode]
  repeat' (split <;> try dsimp only)
  all_goals
    unfoldFinishModes
    dsimp only
    refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    first
      | (intro hm; simpa using hm)
      | omega
      | exact Nat.min_le_left _ _
      | simp
      | (simp; omega)

private theorem up8RightNeighbor_ne_self
    {n : Nat} (hn3 : 3 ≤ n) (ring : DirectedRing n) (e : Fin n) :
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

/--
Configuration-level Construct slack for one interaction.  If every clock is at
most `b`, every mode is Construct, and `b + 1 < kappa`, then after any single
literal P_PL interaction every clock is at most `b + 1` and every mode is still
Construct.
-/
theorem upto8_pplStep_clockBound
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : PPLConfig n psi kappa) (e : Fin n) (b : Nat)
    (hC : ∀ i : Fin n, (C i).clock.val ≤ b ∧ (C i).mode = false)
    (hb : b + 1 < kappa) :
    ∀ i : Fin n,
      (pplStep ring C e i).clock.val ≤ b + 1 ∧
        (pplStep ring C e i).mode = false := by
  intro i
  have hne : ring.rightNeighbor e ≠ e :=
    up8RightNeighbor_ne_self hn3 ring e
  have hp :=
    PPL.Probability.clockSuffixPairProjection hpsi
      (C e) (C (ring.rightNeighbor e))
  have hd := upto8_determineMode_clock_mode
    (C e) (C (ring.rightNeighbor e))
  have hm :=
    PPL.Convergence.ConstructCoupling.pplStep_endpoint_modes
      hn3 hpsi ring C e
  dsimp only at hp hd hm
  have hstepE :
      pplStep ring C e e =
        (PPL.ppl hpsi (C e) (C (ring.rightNeighbor e))).1 := by
    simp [pplStep, PopulationProtocol.step,
      PPL.protocol, PPL.transition, hpsi]
  have hstepJ :
      pplStep ring C e (ring.rightNeighbor e) =
        (PPL.ppl hpsi (C e) (C (ring.rightNeighbor e))).2 := by
    simp [pplStep, PopulationProtocol.step,
      PPL.protocol, PPL.transition, hpsi, hne]
  by_cases hie : i = e
  · subst hie
    have hclk :
        (pplStep ring C i i).clock.val =
          (PPL.determineMode (C i) (C (ring.rightNeighbor i))).1.clock.val := by
      rw [hstepE, hp.1]
    have hbe := (hC i).1
    have hle := hd.1
    refine ⟨by omega, ?_⟩
    rw [hm.1]
    cases hmode :
        (PPL.determineMode (C i) (C (ring.rightNeighbor i))).1.mode with
    | false => rfl
    | true =>
        have hk := hd.2.2.1 hmode
        omega
  · by_cases hij : i = ring.rightNeighbor e
    · subst hij
      have hclk :
          (pplStep ring C e (ring.rightNeighbor e)).clock.val =
            (PPL.determineMode (C e)
              (C (ring.rightNeighbor e))).2.clock.val := by
        rw [hstepJ, hp.2.2.1]
      have hbj := (hC (ring.rightNeighbor e)).1
      have hle := hd.2.1
      refine ⟨by omega, ?_⟩
      rw [hm.2]
      cases hmode :
          (PPL.determineMode (C e)
            (C (ring.rightNeighbor e))).2.mode with
      | false => rfl
      | true =>
          have hk := hd.2.2.2 hmode
          omega
    · have hother : pplStep ring C e i = C i := by
        simp [pplStep, PopulationProtocol.step, PPL.protocol, hie, hij]
      rw [hother]
      exact ⟨Nat.le_succ_of_le (hC i).1, (hC i).2⟩

/--
**Construct slack along a word.**  If every clock of `C` is at most `b`, every
mode is Construct, and `b + word.length < kappa`, then the literal P_PL run of
`word` from `C` is Construct at every configuration boundary
(`constructAlong = true`).
-/
theorem upto8_constructAlong_of_clockBound
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) :
    ∀ (word : DetSchedule n) (C : PPLConfig n psi kappa) (b : Nat),
      (∀ i : Fin n, (C i).clock.val ≤ b ∧ (C i).mode = false) →
      b + word.length < kappa →
      PPL.Modes.Lemma5.constructAlong ring C word = true := by
  intro word
  induction word with
  | nil =>
      intro C b hC _hb
      simp only [PPL.Modes.Lemma5.constructAlong]
      apply up8AllAgentsB_of_forall
      intro i
      simp [(hC i).2]
  | cons e rest ih =>
      intro C b hC hb
      simp only [List.length_cons] at hb
      simp only [PPL.Modes.Lemma5.constructAlong, Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      · apply up8AllAgentsB_of_forall
        intro i
        simp [(hC i).2]
      · exact
          ih (pplStep ring C e) (b + 1)
            (upto8_pplStep_clockBound hn3 hpsi ring C e b hC (by omega))
            (by omega)

/-- `midPhysicalB` unpacked: every clock is at most `kappa / 2` and every mode
is Construct. -/
theorem upto8_midPhysical_clockBound
    {n psi kappa : Nat}
    (C : PPLConfig n psi kappa)
    (h : PPL.Modes.Lemma5.midPhysicalB C = true) :
    ∀ i : Fin n,
      (C i).clock.val ≤ kappa / 2 ∧ (C i).mode = false := by
  unfold PPL.Modes.Lemma5.midPhysicalB at h
  rw [Bool.and_eq_true] at h
  have hall := up8Forall_of_allAgentsB _ h.2
  intro i
  have hi := hall i
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
  exact hi

end PPL

#print axioms PPL.upto8_determineMode_clock_mode
#print axioms PPL.upto8_pplStep_clockBound
#print axioms PPL.upto8_constructAlong_of_clockBound
