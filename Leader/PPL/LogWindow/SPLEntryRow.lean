import Leader.PPL.MainTheorem.FiveEventSplice
import Leader.PPL.MainTheorem.WindowSPLEntryDynamicPadding
import Leader.PPL.Convergence.ForcedConstructProtocol
import Leader.PPL.LogWindow.FiveEventSplice
import Leader.PPL.LogWindow.Statement

/-!
# Superseded (log-window route): whole module `Leader/PPL/Theorem1L18RowProved.lean`

Moved (whole file) from `Leader/PPL/Theorem1L18RowProved.lean` by the P_PL Theorem 1 cleanup, phase 2.
These declarations served only the original psi <= log2 n + 1 route to
`PPL.theorem1Statement_proved`, which now goes through
`PPL.theorem1Statement_proved_via_slack` (`Leader/PPL/MainTheorem/PsiWindowSlack.lean`).
Nothing in the live Theorem 1 closure uses them; they are kept, and still build,
as the record of that route.  Every name `PPL.X` became `PPL.Superseded.LogWindow.X`;
see `research-map/RENAME_MAP_PPL.md` (phase 2).
-/

namespace PPL.Superseded.LogWindow


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


private theorem q20203FoldlAndFalse_existsFalse
    (xs : List Bool)
    (h : xs.foldl (fun a b => a && b) true = false) :
    ∃ b, b ∈ xs ∧ b = false := by
  induction xs with
  | nil =>
      simp at h
  | cons a xs ih =>
      cases ha : a with
      | false =>
          exact ⟨false, by simp, rfl⟩
      | true =>
          have ht :
              xs.foldl (fun u v => u && v) true = false := by
            simpa [List.foldl_cons, ha] using h
          obtain ⟨b, hbmem, hb⟩ := ih ht
          exact ⟨b, by simp [hbmem], hb⟩


private theorem q20203AllLeaderRootsMiss_false_exists_hit
    {n psi : Nat}
    (ring : DirectedRing n)
    (C : Config n psi (theorem1Kappa psi))
    (word : DetSchedule n)
    (hmiss :
      theorem1AllLeaderRootsMissB ring C word = false) :
    ∃ root : Fin n,
      (C root).leader = true ∧
        PPL.Convergence.L18.l18HitsSPL
          ring root C word = true := by
  unfold theorem1AllLeaderRootsMissB at hmiss
  obtain ⟨b, hbmem, hbfalse⟩ :=
    q20203FoldlAndFalse_existsFalse
      (List.ofFn
        (fun root : Fin n =>
          (!(C root).leader) ||
            !(PPL.Convergence.L18.l18HitsSPL
              ring root C word)))
      hmiss
  rw [List.mem_ofFn] at hbmem
  obtain ⟨root, hroot⟩ := hbmem
  have hfalse :
      ((!(C root).leader) ||
          !(PPL.Convergence.L18.l18HitsSPL
            ring root C word)) =
        false := by
    exact hroot.trans hbfalse
  have hleader : (C root).leader = true := by
    cases hl : (C root).leader with
    | false =>
        simp [hl] at hfalse
    | true =>
        rfl
  have hhit :
      PPL.Convergence.L18.l18HitsSPL
          ring root C word =
        true := by
    cases hh :
        PPL.Convergence.L18.l18HitsSPL
          ring root C word with
    | false =>
        simp [hh] at hfalse
    | true =>
        rfl
  exact ⟨root, hleader, hhit⟩


private theorem q20203L18Hit_exists_prefix
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (word : DetSchedule n)
    (hhit :
      PPL.Convergence.L18.l18HitsSPL
        ring root C word = true) :
    ∃ pre suf : DetSchedule n,
      word = pre ++ suf ∧
        SPLAt ring root
          (PPL.Convergence.L18.runPPrime
            ring C pre) := by
  induction word generalizing C with
  | nil =>
      have hspl : SPLAt ring root C := by
        apply of_decide_eq_true
        simpa [PPL.Convergence.L18.l18HitsSPL] using hhit
      exact ⟨[], [], rfl, hspl⟩
  | cons e rest ih =>
      cases hnow : decide (SPLAt ring root C) with
      | true =>
          have hspl : SPLAt ring root C :=
            of_decide_eq_true hnow
          refine ⟨[], e :: rest, by simp, ?_⟩
          simpa [PPL.Convergence.L18.runPPrime] using hspl
      | false =>
          have htail :
              PPL.Convergence.L18.l18HitsSPL
                  ring root
                  (PPL.Convergence.L18.pprimeStep
                    ring C e)
                  rest =
                true := by
            simpa
              [PPL.Convergence.L18.l18HitsSPL,
                hnow]
              using hhit
          obtain ⟨pre, suf, hrest, hspl⟩ :=
            ih
              (C :=
                PPL.Convergence.L18.pprimeStep
                  ring C e)
              htail
          refine ⟨e :: pre, suf, ?_, ?_⟩
          · simp [hrest]
          · simpa [PPL.Convergence.L18.runPPrime] using hspl


private theorem q20203PostConstructAlong_prefix
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
      exact
        ⟨h.1,
          ih
            (C := PPL.Probability.pplStep ring C e)
            h.2⟩


private theorem q20203PostConstructAlong_suffix
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
        ih
          (C := PPL.Probability.pplStep ring C e)
          h.2
      simpa
        [PPL.Probability.runPPL,
          PPL.Probability.runPopulationSchedule,
          PPL.Probability.pplStep]
        using ht


private theorem q20203ReachesSPL_append_right
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (pre suf : DetSchedule n)
    (hsuf :
      theorem1ReachesSPL
        ring
        (PPL.Probability.runPPL ring C pre)
        suf =
      true) :
    theorem1ReachesSPL
      ring C (pre ++ suf) =
    true := by
  induction pre generalizing C with
  | nil =>
      simpa
        [PPL.Probability.runPPL,
          PPL.Probability.runPopulationSchedule]
        using hsuf
  | cons e rest ih =>
      have htail :
          theorem1ReachesSPL
              ring
              (PPL.Probability.runPPL
                ring
                (PPL.Probability.pplStep ring C e)
                rest)
              suf =
            true := by
        simpa
          [PPL.Probability.runPPL,
            PPL.Probability.runPopulationSchedule,
            PPL.Probability.pplStep]
          using hsuf
      have hih :=
        ih
          (C := PPL.Probability.pplStep ring C e)
          htail
      simp only
        [List.cons_append,
          theorem1ReachesSPL]
      change
        (decide (SPL ring C) ||
            theorem1ReachesSPL
              ring
              (PPL.Probability.pplStep ring C e)
              (rest ++ suf)) =
          true
      simp [hih]


private theorem q20203ReachesSPL_of_endpoint
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (word : DetSchedule n)
    (hspl :
      SPL ring
        (PPL.Probability.runPPL ring C word)) :
    theorem1ReachesSPL ring C word = true := by
  have hnil :
      theorem1ReachesSPL
          ring
          (PPL.Probability.runPPL ring C word)
          [] =
        true := by
    simp [theorem1ReachesSPL, hspl]
  simpa using
    q20203ReachesSPL_append_right
      ring C word [] hnil


theorem theorem1L18Row_proved :
    Theorem1L18Row := by
  unfold Theorem1L18Row
  intro n psi
  intro hn3 hpsi _hnpow _hpsiK
  intro ring C0 word t Cmid
  intro hmem hcpb hcut hmid hconstruct
  intro _hwholeCoupling hl1 _hlen17 _hlen18 hbad


  let quiet :=
    theorem1QuietWord psi t word
  let w17 :=
    theorem1L17Word psi t word
  let w18 :=
    theorem1L18Word psi t word
  let C17 :=
    theorem1Prime17End ring Cmid t word


  have hroots :
      theorem1AllLeaderRootsMissB
          ring C17 w18 =
        false := by
    cases hr :
        theorem1AllLeaderRootsMissB
          ring C17 w18 with
    | false =>
        rfl
    | true =>
        have hbadTrue :
            theorem1Bad18B ring C0 word = true := by
          simp
            [theorem1Bad18B,
              hcut, hmid, hcpb,
              hconstruct, hl1,
              C17, w18, hr]
        rw [hbadTrue] at hbad
        contradiction


  obtain ⟨root, _hleader, hhit⟩ :=
    q20203AllLeaderRootsMiss_false_exists_hit
      ring C17 w18 hroots


  have hpostWhole :
      PPL.Convergence.ConstructCoupling.PostDetermineModeConstructAlong
          ring Cmid quiet := by
    apply
      PPL.Convergence.ConstructCoupling.constructAlong_implies_postDetermineModeConstructAlong
          hn3 hpsi ring Cmid quiet
    simpa [quiet] using hconstruct


  have hw17 :
      w17 =
        quiet.take (theorem1H17 n) := by
    rfl
  have hw18 :
      w18 =
        (quiet.drop (theorem1H17 n)).take
          (theorem1H18 n psi) := by
    rfl


  have hquietSplit17 :
      quiet =
        w17 ++
          quiet.drop (theorem1H17 n) := by
    rw [hw17]
    exact
      (List.take_append_drop
        (theorem1H17 n) quiet).symm


  have hpostSplit17 :
      PPL.Convergence.ConstructCoupling.PostDetermineModeConstructAlong
          ring Cmid
          (w17 ++
            quiet.drop (theorem1H17 n)) := by
    rw [← hquietSplit17]
    exact hpostWhole


  have hpost17 :
      PPL.Convergence.ConstructCoupling.PostDetermineModeConstructAlong
          ring Cmid w17 :=
    q20203PostConstructAlong_prefix
      ring Cmid w17
      (quiet.drop (theorem1H17 n))
      hpostSplit17


  have hpostAfter17 :
      PPL.Convergence.ConstructCoupling.PostDetermineModeConstructAlong
          ring
          (PPL.Probability.runPPL ring Cmid w17)
          (quiet.drop (theorem1H17 n)) :=
    q20203PostConstructAlong_suffix
      ring Cmid w17
      (quiet.drop (theorem1H17 n))
      hpostSplit17


  have hcouple17 :=
    PPL.Convergence.ConstructCoupling.runCoupling
      hpsi ring Cmid w17 hpost17


  have hC17full :
      PPL.Probability.runPPL ring Cmid w17 =
        C17 := by
    exact hcouple17


  rw [hC17full] at hpostAfter17


  have htailSplit18 :
      quiet.drop (theorem1H17 n) =
        w18 ++
          (quiet.drop (theorem1H17 n)).drop
            (theorem1H18 n psi) := by
    rw [hw18]
    exact
      (List.take_append_drop
        (theorem1H18 n psi)
        (quiet.drop (theorem1H17 n))).symm


  have hpostSplit18 :
      PPL.Convergence.ConstructCoupling.PostDetermineModeConstructAlong
          ring C17
          (w18 ++
            (quiet.drop (theorem1H17 n)).drop
              (theorem1H18 n psi)) := by
    rw [← htailSplit18]
    exact hpostAfter17


  have hpost18 :
      PPL.Convergence.ConstructCoupling.PostDetermineModeConstructAlong
          ring C17 w18 :=
    q20203PostConstructAlong_prefix
      ring C17 w18
      ((quiet.drop (theorem1H17 n)).drop
        (theorem1H18 n psi))
      hpostSplit18


  obtain ⟨hit, hitSuf, hw18Hit, hsplPrime⟩ :=
    q20203L18Hit_exists_prefix
      ring root C17 w18 hhit


  have hpostHitInput :
      PPL.Convergence.ConstructCoupling.PostDetermineModeConstructAlong
          ring C17 (hit ++ hitSuf) := by
    rw [← hw18Hit]
    exact hpost18


  have hpostHit :
      PPL.Convergence.ConstructCoupling.PostDetermineModeConstructAlong
          ring C17 hit :=
    q20203PostConstructAlong_prefix
      ring C17 hit hitSuf hpostHitInput


  have hcoupleHit :=
    PPL.Convergence.ConstructCoupling.runCoupling
      hpsi ring C17 hit hpostHit


  have hunify :=
    PPL.Convergence.PrimeUnify.runPPrime_eq_runPrime
      ring C17 hit


  have hfullPrime :
      PPL.Probability.runPPL ring C17 hit =
        PPL.Convergence.L18.runPPrime
          ring C17 hit :=
    hcoupleHit.trans hunify.symm


  have hsplFull :
      SPLAt ring root
        (PPL.Probability.runPPL
          ring C17 hit) := by
    rw [hfullPrime]
    exact hsplPrime


  have hlocalHit :
      theorem1ReachesSPL
          ring C17 hit =
        true :=
    q20203ReachesSPL_of_endpoint
      ring C17 hit
      ⟨root, hsplFull⟩


  have hlocalHitFrom17 :
      theorem1ReachesSPL
          ring
          (PPL.Probability.runPPL
            ring Cmid w17)
          hit =
        true := by
    rw [hC17full]
    exact hlocalHit


  have hmidHit :
      theorem1ReachesSPL
          ring Cmid
          (w17 ++ hit) =
        true :=
    q20203ReachesSPL_append_right
      ring Cmid w17 hit hlocalHitFrom17


  obtain
      ⟨p, phase, pad, _hstop, _hphaseMem,
        hfactor, hp, hphase⟩ :=
    theorem1DynamicFirstHitFactor
      (T := theorem1H5ii n psi)
      hn3 hpsi (Nat.le_refl _)
      ring C0 word hmem t hcut hcpb


  have hphaseQuiet :
      phase = quiet := by
    simpa [quiet, theorem1QuietWord] using hphase


  have hprefixState :=
    theorem1DynamicFirstHitPrefixState
      ring C0 word t hcut


  have hmidRun :
      PPL.Probability.runPPL
          ring
          (theorem1State16 ring C0 word)
          ((theorem1Block5i psi word).take t) =
        Cmid := by
    have hm := hmid
    unfold theorem1MidState at hm
    rw [hcut] at hm
    exact Option.some.inj hm


  have hpState :
      PPL.Probability.runPPL ring C0 p =
        Cmid := by
    rw [hp]
    exact hprefixState.trans hmidRun


  have hquietFactor :
      quiet =
        (w17 ++ hit) ++
          (hitSuf ++
            (quiet.drop
                (theorem1H17 n)).drop
              (theorem1H18 n psi)) := by
    calc
      quiet =
          w17 ++
            quiet.drop
              (theorem1H17 n) :=
        hquietSplit17
      _ =
          w17 ++
            (w18 ++
              (quiet.drop
                  (theorem1H17 n)).drop
                (theorem1H18 n psi)) :=
        congrArg (fun x => w17 ++ x) htailSplit18
      _ =
          (w17 ++ hit) ++
            (hitSuf ++
              (quiet.drop
                  (theorem1H17 n)).drop
                (theorem1H18 n psi)) := by
        rw [hw18Hit]
        simp only [List.append_assoc]


  let rest :=
    (hitSuf ++
      (quiet.drop
          (theorem1H17 n)).drop
        (theorem1H18 n psi)) ++
      pad


  have hglobalFactor :
      word =
        (p ++ (w17 ++ hit)) ++ rest := by
    rw [hphaseQuiet] at hfactor
    calc
      word =
          p ++ quiet ++ pad := hfactor
      _ =
          p ++
            ((w17 ++ hit) ++
              (hitSuf ++
                (quiet.drop
                    (theorem1H17 n)).drop
                  (theorem1H18 n psi))) ++
            pad :=
        congrArg (fun x => p ++ x ++ pad) hquietFactor
      _ =
          (p ++ (w17 ++ hit)) ++ rest := by
        dsimp only [rest]
        simp only [List.append_assoc]


  have hmidHitAtP :
      theorem1ReachesSPL
          ring
          (PPL.Probability.runPPL ring C0 p)
          (w17 ++ hit) =
        true := by
    rw [hpState]
    exact hmidHit


  have hprefixHit :
      theorem1ReachesSPL
          ring C0
          (p ++ (w17 ++ hit)) =
        true :=
    q20203ReachesSPL_append_right
      ring C0 p (w17 ++ hit) hmidHitAtP


  have hfullHit :=
    theorem1ReachesSPL_append_of_left
      ring C0
      (p ++ (w17 ++ hit))
      rest
      hprefixHit


  rw [← hglobalFactor] at hfullHit
  exact hfullHit


/-- The five-event splice with its only open input discharged. -/
theorem theorem1FiveEventSplice_proved :
    Theorem1FiveEventSplice :=
  theorem1FiveEventSplice_of_l18Row
    theorem1L18Row_proved


end PPL.Superseded.LogWindow


#print axioms PPL.Superseded.LogWindow.theorem1L18Row_proved
#print axioms PPL.Superseded.LogWindow.theorem1FiveEventSplice_proved
