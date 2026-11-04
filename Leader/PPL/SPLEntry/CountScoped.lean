import Leader.PPL.SPLEntry.ForcingWord
import Leader.PPL.MainTheorem.Skeleton


namespace PPL.Convergence.L18


set_option autoImplicit false
set_option Elab.async false


open PPL
open PPL.Probability


/--
The Lemma-18 ordered-subsequence forcing bridge on the paper domain
`psi < n`.
-/
def L18ForcingWordReachesSPLScoped : Prop :=
  PPL.lemma4_deterministic_core →
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hlt : psi < n)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (schedule : DetSchedule n),
    CPB ring C →
    L18UniqueLeaderAt C root →
    (l18Word ring root psi).Sublist schedule →
    l18HitsSPL ring root C schedule = true


/--
Scoped counterpart of `l18FailureCount_le_fixedWordMissCount`.
The proof is the existing one with the paper-domain premise threaded to the
scoped bridge.
-/
private theorem l18FailureCount_le_fixedWordMissCount_scoped
    (hbridge : L18ForcingWordReachesSPLScoped)
    (hlemma4 : PPL.lemma4_deterministic_core)
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hlt : psi < n)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (hCPB : CPB ring C)
    (hUnique : L18UniqueLeaderAt C root) :
    l18FailureCount ring root C ≤
      PPL.Probability.fixedWordMissCount
        (l18Word ring root psi)
        (l18Horizon n psi) := by
  change
    (allSchedules n (l18Horizon n psi)).countP
        (fun schedule =>
          !(l18HitsSPL ring root C schedule)) ≤
      (allSchedules n (l18Horizon n psi)).countP
        (fun schedule =>
          decide
            (Not ((l18Word ring root psi).Sublist
              schedule)))
  apply l18_countP_mono
  intro schedule hbad
  cases hhit :
      l18HitsSPL ring root C schedule with
  | false =>
      by_cases hsub :
          (l18Word ring root psi).Sublist schedule
      · have hs :=
          hbridge hlemma4
            hn3 hpsi hlt
            ring root C schedule
            hCPB hUnique hsub
        have hft : false = true := by
          simpa [hhit] using hs
        cases hft
      · simp [hsub]
  | true =>
      have hft : false = true := by
        simpa [hhit] using hbad
      cases hft


/--
Scoped Lemma-18 counting tail.

This is `n_mul_l18FailureCount_le_pow` with the additional paper-domain
premise `psi < n`, consumed through
`L18ForcingWordReachesSPLScoped`.
-/
theorem n_mul_l18FailureCount_le_pow_scoped
    (hbridge : L18ForcingWordReachesSPLScoped)
    (hlemma4 : PPL.lemma4_deterministic_core)
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hlt : psi < n)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (hCPB : CPB ring C)
    (hUnique : L18UniqueLeaderAt C root) :
    n * l18FailureCount ring root C ≤
      n ^ l18Horizon n psi := by
  have hfail :
      l18FailureCount ring root C ≤
        PPL.Probability.fixedWordMissCount
          (l18Word ring root psi)
          (l18Horizon n psi) :=
    l18FailureCount_le_fixedWordMissCount_scoped
      hbridge hlemma4 hn3 hpsi hlt
      ring root C hCPB hUnique

  have hfixed :
      PPL.Probability.fixedWordMissCount
          (l18Word ring root psi)
          (l18Horizon n psi) *
          2 ^ (4 * l18K n) ≤
        n ^ l18Horizon n psi := by
    simpa [l18Horizon] using
      (PPL.Probability.fixedWordMissCount_mul_twoPow_le_of_length
        (l18Word ring root psi)
        (l18Length n psi)
        (4 * l18K n)
        (l18Word_length hn3 hpsi ring root))

  have hnpos : 0 < n := by
    omega
  have hn0 : n ≠ 0 :=
    Nat.ne_of_gt hnpos
  have hlt :
      n < 2 ^ l18K n := by
    unfold l18K
    exact (Nat.log2_lt hn0).1 (by omega)
  have hKpos : 0 < l18K n := by
    simp [l18K]
  have hKle :
      l18K n ≤ 4 * l18K n := by
    omega
  have hpow :
      2 ^ l18K n ≤ 2 ^ (4 * l18K n) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hKle
  have hn4 :
      n ≤ 2 ^ (4 * l18K n) :=
    Nat.le_trans (Nat.le_of_lt hlt) hpow

  calc
    n * l18FailureCount ring root C ≤
        n *
          PPL.Probability.fixedWordMissCount
            (l18Word ring root psi)
            (l18Horizon n psi) :=
      Nat.mul_le_mul_left n hfail
    _ ≤
        (2 ^ (4 * l18K n)) *
          PPL.Probability.fixedWordMissCount
            (l18Word ring root psi)
            (l18Horizon n psi) := by
      exact
        Nat.mul_le_mul_right
          (PPL.Probability.fixedWordMissCount
            (l18Word ring root psi)
            (l18Horizon n psi))
          hn4
    _ =
        PPL.Probability.fixedWordMissCount
            (l18Word ring root psi)
            (l18Horizon n psi) *
          2 ^ (4 * l18K n) := by
      ac_rfl
    _ ≤ n ^ l18Horizon n psi :=
      hfixed


end PPL.Convergence.L18


namespace PPL


set_option autoImplicit false
set_option Elab.async false


private theorem theorem1_log2_add_one_lt_self_of_five_le
    {n : Nat}
    (hn5 : 5 ≤ n) :
    Nat.log2 n + 1 < n := by
  rw [Nat.log2_def n, if_pos (by omega : 2 ≤ n)]
  have hhalf :
      Nat.log2 (n / 2) ≤ n / 2 :=
    Nat.log2_le_self (n / 2)
  omega


/--
The Theorem-1 logarithmic window is inside the scoped Lemma-18 paper domain.
-/
theorem theorem1_psi_lt_n
    {n psi : Nat}
    (hn3 : 3 ≤ n)
    (hpsiK : psi ≤ theorem1K n) :
    psi < n := by
  by_cases hn5 : 5 ≤ n
  · have hKlt :
        theorem1K n < n := by
      unfold theorem1K
      exact
        theorem1_log2_add_one_lt_self_of_five_le
          hn5
    exact Nat.lt_of_le_of_lt hpsiK hKlt
  · have hcases :
        Or (n = 3) (n = 4) := by
      omega
    rcases hcases with h3 | h4
    · subst n
      have hKlt :
          theorem1K 3 < 3 := by
        decide
      exact Nat.lt_of_le_of_lt hpsiK hKlt
    · subst n
      have hKlt :
          theorem1K 4 < 4 := by
        decide
      exact Nat.lt_of_le_of_lt hpsiK hKlt


end PPL


#print axioms PPL.Convergence.L18.n_mul_l18FailureCount_le_pow_scoped
#print axioms PPL.theorem1_psi_lt_n
