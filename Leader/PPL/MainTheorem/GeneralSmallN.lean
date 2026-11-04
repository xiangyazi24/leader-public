import Leader.PPL.MainTheorem.GeneralFirstHit
import Leader.PPL.MainTheorem.PossibleUpToEight

/-!
# P_PL Theorem 1, general small-`n` tail from `C_mid`

The deterministic small-`n` route reaches `C_PB`, runs the maximum-reset wave
to a `C_mid` configuration (every clock at most `kappa / 2`, every mode
Construct), then runs a literal one-leader word `w17` followed by the prefix
`hit` of the Lemma-18 forcing word at which the `P_PL'` run first satisfies
the rooted target.  Construct slack makes the `P_PL` and `P_PL'` runs of
`w17 ++ hit` coincide.

The `psi < n`, `n ≤ 8` version (`PPL.PsiBelowN.upto8_tailSPL_of_mid`,
rooted `S_PL`, scoped forcing) and the `n ≤ psi`, `n ≤ 64` version
(`PPL.PsiAtLeastN.psiGe_tailSafe_of_mid`, rooted safe predicate) differ only
in the rooted predicate, the forcing lemma and the slack arithmetic; here
the forcing lemma (`hforce`) and the slack (`hslack`) are hypotheses.

P_PL Theorem 1 cleanup, phase 2, step 6e.
-/

namespace PPL.Theorem1General

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-- **Tail from `C_mid` for a rooted predicate.**  From a `C_PB`
configuration with every clock at most `kappa / 2` and every mode Construct,
given a literal one-leader word `w17` with
`kappa / 2 + |w17| + l18Length < kappa`, and a forcing lemma saying that
along the Lemma-18 word the `P_PL'` run from any `C_PB` configuration with a
unique leader root hits `loc root`, some `P_PL` word from `Cmid` ends in
`loc root` for some root. -/
theorem theorem1TailOfMid_at
    {n psi : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (loc : Fin n → Config n psi (theorem1Kappa psi) → Bool)
    (hforce :
      ∀ (root : Fin n) (C : Config n psi (theorem1Kappa psi)),
        PPL.CPB ring C →
        PPL.Convergence.L18.L18UniqueLeaderAt C root →
        theorem1L18HitsB ring (loc root) C
          (PPL.Convergence.L18.l18Word ring root psi) = true)
    (Cmid : Config n psi (theorem1Kappa psi))
    (hCPB : PPL.CPB ring Cmid)
    (hmid : PPL.Modes.Lemma5.midPhysicalB Cmid = true)
    (w17 : DetSchedule n)
    (hslack :
      theorem1Kappa psi / 2 + w17.length +
          PPL.Convergence.L18.l18Length n psi <
        theorem1Kappa psi)
    (hL1 :
      PPL.LiteralL1
        (PPL.Probability.runPopulationSchedule
          PPL.Elim.protocolE ring (PPL.Elim.viewConfig Cmid) w17)) :
    ∃ (word : DetSchedule n) (root : Fin n),
      loc root (PPL.Probability.runPPL ring Cmid word) = true := by
  let C17 : Config n psi (theorem1Kappa psi) :=
    PPL.Convergence.ConstructCoupling.runPrime ring Cmid w17
  have hproj :
      PPL.Elim.viewConfig C17 =
        PPL.Probability.runPopulationSchedule
          PPL.Elim.protocolE ring (PPL.Elim.viewConfig Cmid) w17 :=
    PPL.Convergence.LiteralEliminationBridges.runPrime_projects
      hpsi ring Cmid w17
  have hcount : PPL.Elim.leaderCount (PPL.Elim.viewConfig C17) = 1 := by
    rw [hproj]
    exact hL1
  obtain ⟨root, hUnique⟩ := theorem1Unique_of_leaderCount C17 hcount
  have hPBmid : PPL.Elim.PB ring (PPL.Elim.viewConfig Cmid) :=
    (PPL.Convergence.LiteralEliminationBridges.cpbViewBridge ring Cmid).mp
      hCPB
  have hPB17 : PPL.Elim.PB ring (PPL.Elim.viewConfig C17) := by
    rw [hproj]
    exact theorem1PB_run ring w17 _ hPBmid
  have hCPB17 : PPL.CPB ring C17 :=
    (PPL.Convergence.LiteralEliminationBridges.cpbViewBridge ring C17).mpr
      hPB17
  have hhit := hforce root C17 hCPB17 hUnique
  obtain ⟨hit, suf, hsplit, hlocPrime⟩ :=
    theorem1L18HitsB_exists_prefix ring (loc root) C17 _ hhit
  have hhitLen : hit.length ≤ PPL.Convergence.L18.l18Length n psi := by
    have h := congrArg List.length hsplit
    rw [PPL.Convergence.L18.l18Word_length hn3 hpsi ring root,
      List.length_append] at h
    omega
  have hslack' :
      theorem1Kappa psi / 2 + (w17 ++ hit).length < theorem1Kappa psi := by
    rw [List.length_append]
    omega
  -- Construct slack along the active word, hence P_PL = P_PL'.
  have hcons :
      PPL.Modes.Lemma5.constructAlong ring Cmid (w17 ++ hit) = true :=
    upto8_constructAlong_of_clockBound hn3 hpsi ring (w17 ++ hit) Cmid
      (theorem1Kappa psi / 2)
      (upto8_midPhysical_clockBound Cmid hmid) hslack'
  have hpost :=
    PPL.Convergence.ConstructCoupling.constructAlong_implies_postDetermineModeConstructAlong
      hn3 hpsi ring Cmid (w17 ++ hit) hcons
  have hcouple :
      PPL.Probability.runPPL ring Cmid (w17 ++ hit) =
        PPL.Convergence.ConstructCoupling.runPrime ring Cmid (w17 ++ hit) :=
    PPL.Convergence.ConstructCoupling.runCoupling hpsi ring Cmid
      (w17 ++ hit) hpost
  have hprime17 : PPL.Convergence.L18.runPPrime ring Cmid w17 = C17 := by
    simpa [C17] using
      PPL.Convergence.PrimeUnify.runPPrime_eq_runPrime ring Cmid w17
  have hprimePre :
      PPL.Convergence.ConstructCoupling.runPrime ring Cmid (w17 ++ hit) =
        PPL.Convergence.L18.runPPrime ring C17 hit := by
    rw [← PPL.Convergence.PrimeUnify.runPPrime_eq_runPrime
          ring Cmid (w17 ++ hit),
      PPL.Convergence.L18.runPPrime_append ring Cmid w17 hit,
      hprime17]
  refine ⟨w17 ++ hit, root, ?_⟩
  rw [hcouple, hprimePre]
  exact hlocPrime

end PPL.Theorem1General
