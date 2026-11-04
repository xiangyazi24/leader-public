import Leader.PPL.MainTheorem.FiveEventSplice
import Leader.PPL.MainTheorem.WindowSPLEntryDynamicPadding
import Leader.PPL.MainTheorem.Whp
import Leader.PPL.MainTheorem.GeneralQuietWindowFit
import Leader.PPL.MainTheorem.GeneralTargets

/-!
# P_PL Theorem 1, general splice: the L5(ii) and L18 rows and the five-event splice, for any target

The `psi < n` chain (`PPL.PsiBelowN.Splice`, target `S_PL`) and the
`n ≤ psi` chain (`PPL.PsiAtLeastN.SafeSplice`, the safe target) carried two
copies of the same argument, differing only in the target.  Here the target
is a parameter, through the generic hitting tests and bad events of
`Leader/PPL/MainTheorem/GeneralTargets.lean`; the only link needed between the
global and the rooted target is that a rooted hit is a global hit (`hloc`).
The quiet-window rows (`theorem1_prime_slice_lengths`,
`theorem1L5iiRow_at`) never used the domain premise and are stated without
it.

The whp union is in `Leader/PPL/MainTheorem/GeneralWhp.lean`.  The two chains
keep their definitions and statements; their rows become special cases
through the bridging equalities of `Targets.lean` (for `S_PL`) and of
`PPL.PsiAtLeastN.SafeRows` (for the safe target).

P_PL Theorem 1 cleanup, phase 2, step 6b (the argument is
the one of `Theorem1L18RowProved.lean`).
-/

namespace PPL.Theorem1General

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-- Post-determine Construct alignment along `u ++ v` restricts to `u`. -/
theorem theorem1PostConstructAlong_prefix
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (u v : DetSchedule n)
    (h :
      PPL.Convergence.ConstructCoupling.PostDetermineModeConstructAlong
          ring C (u ++ v)) :
    PPL.Convergence.ConstructCoupling.PostDetermineModeConstructAlong
        ring C u := by
  induction u generalizing C with
  | nil =>
      trivial
  | cons e rest ih =>
      change
        PPL.Convergence.ConstructCoupling.PostDetermineModeConstructAt
              ring C e ∧
          PPL.Convergence.ConstructCoupling.PostDetermineModeConstructAlong
              ring
              (PPL.Probability.pplStep ring C e)
              (rest ++ v)
        at h
      change
        PPL.Convergence.ConstructCoupling.PostDetermineModeConstructAt
              ring C e ∧
          PPL.Convergence.ConstructCoupling.PostDetermineModeConstructAlong
              ring
              (PPL.Probability.pplStep ring C e)
              rest
      exact ⟨h.1, ih (C := PPL.Probability.pplStep ring C e) h.2⟩

/-- Post-determine Construct alignment along `u ++ v` restricts to `v` from
the endpoint of `u`. -/
theorem theorem1PostConstructAlong_suffix
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (u v : DetSchedule n)
    (h :
      PPL.Convergence.ConstructCoupling.PostDetermineModeConstructAlong
          ring C (u ++ v)) :
    PPL.Convergence.ConstructCoupling.PostDetermineModeConstructAlong
        ring
        (PPL.Probability.runPPL ring C u)
        v := by
  induction u generalizing C with
  | nil =>
      simpa
        [PPL.Probability.runPPL,
          PPL.Probability.runPopulationSchedule]
        using h
  | cons e rest ih =>
      change
        PPL.Convergence.ConstructCoupling.PostDetermineModeConstructAt
              ring C e ∧
          PPL.Convergence.ConstructCoupling.PostDetermineModeConstructAlong
              ring
              (PPL.Probability.pplStep ring C e)
              (rest ++ v)
        at h
      have ht :=
        ih (C := PPL.Probability.pplStep ring C e) h.2
      simpa
        [PPL.Probability.runPPL,
          PPL.Probability.runPopulationSchedule,
          PPL.Probability.pplStep]
        using ht

/-! ## The quiet-window rows, without a domain premise -/

/-- The two prime slices are not truncated inside the quiet word. -/
theorem theorem1_prime_slice_lengths
    {n psi : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi)
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (word : DetSchedule n)
    (t : Nat)
    (hmem : word ∈ allSchedules n (theorem1Horizon n psi))
    (hcut : theorem1MidCut ring C0 word = some t) :
    (theorem1L17Word psi t word).length = theorem1H17 n ∧
      (theorem1L18Word psi t word).length = theorem1H18 n psi := by
  have hquiet :=
    theorem1QuietWord_length_of_cut ring C0 word t hmem hcut
  have hfit := theorem1H17_add_H18_le_H5ii hn3 hpsi hnpow
  have h17 : theorem1H17 n ≤ theorem1H5ii n psi := by
    omega
  have h18 :
      theorem1H18 n psi ≤ theorem1H5ii n psi - theorem1H17 n := by
    omega
  constructor
  · unfold theorem1L17Word
    rw [List.length_take, hquiet]
    exact Nat.min_eq_left h17
  · unfold theorem1L18Word
    rw [List.length_take, List.length_drop, hquiet]
    exact Nat.min_eq_left h18

/-- The L5(ii) row at one `(n, psi)`: when the L5(ii) event fails, the full
`H5ii` Construct window from the dynamic `C_mid` cut is aligned, the `P_PL`
run couples with the prime run, and both prime slices have their exact
lengths. -/
theorem theorem1L5iiRow_at
    {n psi : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi)
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (word : DetSchedule n)
    (t : Nat)
    (Cmid : Config n psi (theorem1Kappa psi))
    (hmem : word ∈ allSchedules n (theorem1Horizon n psi))
    (hcpb :
      PPL.Convergence.ReachCPB.reachesCPB
          ring C0 (theorem1Block16 psi word) = true)
    (hcut : theorem1MidCut ring C0 word = some t)
    (hmid : theorem1MidState ring C0 word = some Cmid)
    (hbad : theorem1Bad5iiB ring C0 word = false) :
    PPL.Modes.Lemma5.constructAlong
        ring Cmid (theorem1QuietWord psi t word) = true ∧
      PPL.Probability.runPPL
          ring Cmid (theorem1QuietWord psi t word) =
        PPL.Convergence.ConstructCoupling.runPrime
          ring Cmid (theorem1QuietWord psi t word) ∧
      (theorem1L17Word psi t word).length = theorem1H17 n ∧
      (theorem1L18Word psi t word).length = theorem1H18 n psi := by
  have hconstruct :
      PPL.Modes.Lemma5.constructAlong
          ring Cmid (theorem1QuietWord psi t word) = true := by
    cases hc :
        PPL.Modes.Lemma5.constructAlong
          ring Cmid (theorem1QuietWord psi t word) with
    | false =>
        simp [theorem1Bad5iiB, hcut, hmid, hcpb, hc] at hbad
    | true =>
        rfl
  have hpost :=
    PPL.Convergence.ConstructCoupling.constructAlong_implies_postDetermineModeConstructAlong
      hn3 hpsi ring Cmid (theorem1QuietWord psi t word) hconstruct
  have hcouple :=
    PPL.Convergence.ConstructCoupling.runCoupling
      hpsi ring Cmid (theorem1QuietWord psi t word) hpost
  have hlens :=
    theorem1_prime_slice_lengths hn3 hpsi hnpow ring C0 word t hmem hcut
  exact ⟨hconstruct, hcouple, hlens.1, hlens.2⟩

/-! ## The L18 row for any target -/

/-- The L18 row at one `(n, psi)` for a rooted Boolean predicate `loc` and
a global Boolean target `tgt` with `loc root C → tgt C`.

If the L18 event fails, some leader root hits `loc` along the `P_PL'` run
of the L18 slice.  The Construct alignment of the quiet word restricts to
the L17 slice and to the hitting prefix of the L18 slice, so the full `P_PL`
run agrees with the `P_PL'` run there; the rooted hit is therefore a
`P_PL` configuration in `tgt`, reached at the prefix
`p ++ (w17 ++ hit)` of the whole word, where `p` is the prefix up to the
dynamic `C_mid` cut (`theorem1DynamicFirstHitFactor`). -/
theorem theorem1L18Row_at
    {n psi : Nat}
    (ring : DirectedRing n)
    (loc : Fin n → Config n psi (theorem1Kappa psi) → Bool)
    (tgt : Config n psi (theorem1Kappa psi) → Bool)
    (hloc : ∀ (root : Fin n) (C : Config n psi (theorem1Kappa psi)),
      loc root C = true → tgt C = true)
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (C0 : Config n psi (theorem1Kappa psi))
    (word : DetSchedule n)
    (t : Nat)
    (Cmid : Config n psi (theorem1Kappa psi))
    (hmem : word ∈ allSchedules n (theorem1Horizon n psi))
    (hcpb :
      PPL.Convergence.ReachCPB.reachesCPB
          ring C0 (theorem1Block16 psi word) = true)
    (hcut : theorem1MidCut ring C0 word = some t)
    (hmid : theorem1MidState ring C0 word = some Cmid)
    (hconstruct :
      PPL.Modes.Lemma5.constructAlong
          ring Cmid (theorem1QuietWord psi t word) = true)
    (hl1 :
      decide
          (PPL.LiteralL1 (theorem1Literal17End ring Cmid t word)) =
        true)
    (hbad : theorem1Bad18Gen ring loc C0 word = false) :
    theorem1ReachesB ring tgt C0 word = true := by
  let quiet := theorem1QuietWord psi t word
  let w17 := theorem1L17Word psi t word
  let w18 := theorem1L18Word psi t word
  let C17 := theorem1Prime17End ring Cmid t word

  have hroots : theorem1AllLeaderRootsMissGen ring loc C17 w18 = false := by
    cases hr : theorem1AllLeaderRootsMissGen ring loc C17 w18 with
    | false =>
        rfl
    | true =>
        have hbadTrue : theorem1Bad18Gen ring loc C0 word = true := by
          simp
            [theorem1Bad18Gen, hcut, hmid, hcpb, hconstruct, hl1,
              C17, w18, hr]
        rw [hbadTrue] at hbad
        contradiction

  obtain ⟨root, _hleader, hhit⟩ :=
    theorem1AllLeaderRootsMissGen_false_exists_hit ring loc C17 w18 hroots

  -- Alignment of the quiet word restricts to the slices

  have hpostWhole :
      PPL.Convergence.ConstructCoupling.PostDetermineModeConstructAlong
          ring Cmid quiet := by
    apply
      PPL.Convergence.ConstructCoupling.constructAlong_implies_postDetermineModeConstructAlong
          hn3 hpsi ring Cmid quiet
    simpa [quiet] using hconstruct

  have hw17 : w17 = quiet.take (theorem1H17 n) := rfl
  have hw18 :
      w18 = (quiet.drop (theorem1H17 n)).take (theorem1H18 n psi) := rfl

  have hquietSplit17 : quiet = w17 ++ quiet.drop (theorem1H17 n) := by
    rw [hw17]
    exact (List.take_append_drop (theorem1H17 n) quiet).symm

  have hpostSplit17 :
      PPL.Convergence.ConstructCoupling.PostDetermineModeConstructAlong
          ring Cmid (w17 ++ quiet.drop (theorem1H17 n)) := by
    rw [← hquietSplit17]
    exact hpostWhole

  have hpost17 :=
    theorem1PostConstructAlong_prefix
      ring Cmid w17 (quiet.drop (theorem1H17 n)) hpostSplit17

  have hpostAfter17 :=
    theorem1PostConstructAlong_suffix
      ring Cmid w17 (quiet.drop (theorem1H17 n)) hpostSplit17

  have hC17full : PPL.Probability.runPPL ring Cmid w17 = C17 :=
    PPL.Convergence.ConstructCoupling.runCoupling hpsi ring Cmid w17 hpost17

  rw [hC17full] at hpostAfter17

  have htailSplit18 :
      quiet.drop (theorem1H17 n) =
        w18 ++
          (quiet.drop (theorem1H17 n)).drop (theorem1H18 n psi) := by
    rw [hw18]
    exact
      (List.take_append_drop (theorem1H18 n psi)
        (quiet.drop (theorem1H17 n))).symm

  have hpostSplit18 :
      PPL.Convergence.ConstructCoupling.PostDetermineModeConstructAlong
          ring C17
          (w18 ++
            (quiet.drop (theorem1H17 n)).drop (theorem1H18 n psi)) := by
    rw [← htailSplit18]
    exact hpostAfter17

  have hpost18 :=
    theorem1PostConstructAlong_prefix
      ring C17 w18
      ((quiet.drop (theorem1H17 n)).drop (theorem1H18 n psi))
      hpostSplit18

  -- The rooted hit is a hit of the full run

  obtain ⟨hit, hitSuf, hw18Hit, hlocPrime⟩ :=
    theorem1L18HitsB_exists_prefix ring (loc root) C17 w18 hhit

  have hpostHitInput :
      PPL.Convergence.ConstructCoupling.PostDetermineModeConstructAlong
          ring C17 (hit ++ hitSuf) := by
    rw [← hw18Hit]
    exact hpost18

  have hpostHit :=
    theorem1PostConstructAlong_prefix ring C17 hit hitSuf hpostHitInput

  have hcoupleHit :=
    PPL.Convergence.ConstructCoupling.runCoupling hpsi ring C17 hit hpostHit

  have hunify :=
    PPL.Convergence.PrimeUnify.runPPrime_eq_runPrime ring C17 hit

  have hfullPrime :
      PPL.Probability.runPPL ring C17 hit =
        PPL.Convergence.L18.runPPrime ring C17 hit :=
    hcoupleHit.trans hunify.symm

  have hlocFull : loc root (PPL.Probability.runPPL ring C17 hit) = true := by
    rw [hfullPrime]
    exact hlocPrime

  have hlocalHit : theorem1ReachesB ring tgt C17 hit = true :=
    theorem1ReachesB_of_endpoint ring tgt C17 hit
      (hloc root _ hlocFull)

  have hlocalHitFrom17 :
      theorem1ReachesB ring tgt
          (PPL.Probability.runPPL ring Cmid w17) hit =
        true := by
    rw [hC17full]
    exact hlocalHit

  have hmidHit : theorem1ReachesB ring tgt Cmid (w17 ++ hit) = true :=
    theorem1ReachesB_append_right ring tgt Cmid w17 hit hlocalHitFrom17

  -- Placing the hit inside the whole word

  obtain ⟨p, phase, pad, _hstop, _hphaseMem, hfactor, hp, hphase⟩ :=
    theorem1DynamicFirstHitFactor
      (T := theorem1H5ii n psi)
      hn3 hpsi (Nat.le_refl _)
      ring C0 word hmem t hcut hcpb

  have hphaseQuiet : phase = quiet := by
    simpa [quiet, theorem1QuietWord] using hphase

  have hprefixState :=
    theorem1DynamicFirstHitPrefixState ring C0 word t hcut

  have hmidRun :
      PPL.Probability.runPPL ring
          (theorem1State16 ring C0 word)
          ((theorem1Block5i psi word).take t) =
        Cmid := by
    have hm := hmid
    unfold theorem1MidState at hm
    rw [hcut] at hm
    exact Option.some.inj hm

  have hpState : PPL.Probability.runPPL ring C0 p = Cmid := by
    rw [hp]
    exact hprefixState.trans hmidRun

  have hquietFactor :
      quiet =
        (w17 ++ hit) ++
          (hitSuf ++
            (quiet.drop (theorem1H17 n)).drop (theorem1H18 n psi)) := by
    calc
      quiet = w17 ++ quiet.drop (theorem1H17 n) := hquietSplit17
      _ =
          w17 ++
            (w18 ++
              (quiet.drop (theorem1H17 n)).drop (theorem1H18 n psi)) :=
        congrArg (fun x => w17 ++ x) htailSplit18
      _ =
          (w17 ++ hit) ++
            (hitSuf ++
              (quiet.drop (theorem1H17 n)).drop (theorem1H18 n psi)) := by
        rw [hw18Hit]
        simp only [List.append_assoc]

  let rest :=
    (hitSuf ++
      (quiet.drop (theorem1H17 n)).drop (theorem1H18 n psi)) ++ pad

  have hglobalFactor : word = (p ++ (w17 ++ hit)) ++ rest := by
    rw [hphaseQuiet] at hfactor
    calc
      word = p ++ quiet ++ pad := hfactor
      _ =
          p ++
            ((w17 ++ hit) ++
              (hitSuf ++
                (quiet.drop (theorem1H17 n)).drop (theorem1H18 n psi))) ++
            pad :=
        congrArg (fun x => p ++ x ++ pad) hquietFactor
      _ = (p ++ (w17 ++ hit)) ++ rest := by
        dsimp only [rest]
        simp only [List.append_assoc]

  have hmidHitAtP :
      theorem1ReachesB ring tgt
          (PPL.Probability.runPPL ring C0 p) (w17 ++ hit) =
        true := by
    rw [hpState]
    exact hmidHit

  have hprefixHit :
      theorem1ReachesB ring tgt C0 (p ++ (w17 ++ hit)) = true :=
    theorem1ReachesB_append_right ring tgt C0 p (w17 ++ hit) hmidHitAtP

  have hfullHit :=
    theorem1ReachesB_append_of_left ring tgt C0
      (p ++ (w17 ++ hit)) rest hprefixHit

  rw [← hglobalFactor] at hfullHit
  exact hfullHit

/-! ## The five-event splice for any target -/

/-- The five-event splice at one `(n, psi)` for any global test `reach`
and L18 event `bad18`, given the five rows: a Theorem-1 word that does not
hit is bad for L16, L5(i), L5(ii), L17 or L18. -/
theorem theorem1FiveEventSplice_at
    {n psi : Nat}
    (reach bad18 :
      DirectedRing n → Config n psi (theorem1Kappa psi) →
        DetSchedule n → Bool)
    (h16 : Theorem1L16Row)
    (h5i : Theorem1L5iRow)
    (h17 : Theorem1L17Row)
    (h5ii :
      ∀ (ring : DirectedRing n)
        (C0 : Config n psi (theorem1Kappa psi))
        (word : DetSchedule n)
        (t : Nat)
        (Cmid : Config n psi (theorem1Kappa psi)),
        word ∈ allSchedules n (theorem1Horizon n psi) →
        PPL.Convergence.ReachCPB.reachesCPB
            ring C0 (theorem1Block16 psi word) = true →
        theorem1MidCut ring C0 word = some t →
        theorem1MidState ring C0 word = some Cmid →
        theorem1Bad5iiB ring C0 word = false →
        PPL.Modes.Lemma5.constructAlong
            ring Cmid (theorem1QuietWord psi t word) = true ∧
          PPL.Probability.runPPL
              ring Cmid (theorem1QuietWord psi t word) =
            PPL.Convergence.ConstructCoupling.runPrime
              ring Cmid (theorem1QuietWord psi t word) ∧
          (theorem1L17Word psi t word).length = theorem1H17 n ∧
          (theorem1L18Word psi t word).length = theorem1H18 n psi)
    (h18 :
      ∀ (ring : DirectedRing n)
        (C0 : Config n psi (theorem1Kappa psi))
        (word : DetSchedule n)
        (t : Nat)
        (Cmid : Config n psi (theorem1Kappa psi)),
        word ∈ allSchedules n (theorem1Horizon n psi) →
        PPL.Convergence.ReachCPB.reachesCPB
            ring C0 (theorem1Block16 psi word) = true →
        theorem1MidCut ring C0 word = some t →
        theorem1MidState ring C0 word = some Cmid →
        PPL.Modes.Lemma5.constructAlong
            ring Cmid (theorem1QuietWord psi t word) = true →
        PPL.Probability.runPPL
            ring Cmid (theorem1QuietWord psi t word) =
          PPL.Convergence.ConstructCoupling.runPrime
            ring Cmid (theorem1QuietWord psi t word) →
        decide
            (PPL.LiteralL1 (theorem1Literal17End ring Cmid t word)) =
          true →
        (theorem1L17Word psi t word).length = theorem1H17 n →
        (theorem1L18Word psi t word).length = theorem1H18 n psi →
        bad18 ring C0 word = false →
        reach ring C0 word = true)
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (word : DetSchedule n)
    (hmem : word ∈ allSchedules n (theorem1Horizon n psi))
    (hfail : !(reach ring C0 word) = true) :
    Or
      (theorem1Bad16B ring C0 word = true)
      (Or
        (theorem1Bad5iB ring C0 word = true)
        (Or
          (theorem1Bad5iiB ring C0 word = true)
          (Or
            (theorem1Bad17B ring C0 word = true)
            (bad18 ring C0 word = true)))) := by
  cases hb16 : theorem1Bad16B ring C0 word with
  | true =>
      exact Or.inl rfl
  | false =>
      have hcpb := h16 ring C0 word hb16
      cases hb5i : theorem1Bad5iB ring C0 word with
      | true =>
          exact Or.inr (Or.inl rfl)
      | false =>
          obtain ⟨t, hcut⟩ := h5i ring C0 word hcpb hb5i
          let Cmid : Config n psi (theorem1Kappa psi) :=
            PPL.Probability.runPPL ring
              (theorem1State16 ring C0 word)
              ((theorem1Block5i psi word).take t)
          have hmid : theorem1MidState ring C0 word = some Cmid := by
            simp [theorem1MidState, hcut, Cmid]
          cases hb5ii : theorem1Bad5iiB ring C0 word with
          | true =>
              exact Or.inr (Or.inr (Or.inl rfl))
          | false =>
              have hwindow :=
                h5ii ring C0 word t Cmid hmem hcpb hcut hmid hb5ii
              cases hb17 : theorem1Bad17B ring C0 word with
              | true =>
                  exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
              | false =>
                  have hl1 :=
                    h17 ring C0 word t Cmid hcpb hcut hmid hwindow.1 hb17
                  cases hb18 : bad18 ring C0 word with
                  | true =>
                      exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
                  | false =>
                      have hhit :=
                        h18 ring C0 word t Cmid hmem hcpb hcut hmid
                          hwindow.1 hwindow.2.1 hl1
                          hwindow.2.2.1 hwindow.2.2.2 hb18
                      simp [hhit] at hfail

/-! ## The `S_PL` L18 row -/

/-- The L18 row for `S_PL` at one `(n, psi)`. -/
theorem theorem1L18RowSPL_at
    {n psi : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (word : DetSchedule n)
    (t : Nat)
    (Cmid : Config n psi (theorem1Kappa psi))
    (hmem : word ∈ allSchedules n (theorem1Horizon n psi))
    (hcpb :
      PPL.Convergence.ReachCPB.reachesCPB
          ring C0 (theorem1Block16 psi word) = true)
    (hcut : theorem1MidCut ring C0 word = some t)
    (hmid : theorem1MidState ring C0 word = some Cmid)
    (hconstruct :
      PPL.Modes.Lemma5.constructAlong
          ring Cmid (theorem1QuietWord psi t word) = true)
    (hl1 :
      decide
          (PPL.LiteralL1 (theorem1Literal17End ring Cmid t word)) =
        true)
    (hbad : theorem1Bad18B ring C0 word = false) :
    theorem1ReachesSPL ring C0 word = true := by
  rw [theorem1ReachesSPL_eq]
  rw [theorem1Bad18B_eq] at hbad
  exact
    theorem1L18Row_at ring
      (fun root C => decide (SPLAt ring root C))
      (fun C => decide (SPL ring C))
      (fun root C h => decide_eq_true ⟨root, of_decide_eq_true h⟩)
      hn3 hpsi C0 word t Cmid hmem hcpb hcut hmid hconstruct hl1 hbad

end PPL.Theorem1General
