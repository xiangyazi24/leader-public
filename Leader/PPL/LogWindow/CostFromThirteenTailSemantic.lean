import Leader.PPL.MainTheorem.CostFromThirteenTail
import Leader.PPL.Convergence.QuietWindow
import Leader.PPL.Convergence.ForcedConstructProtocol
import Leader.Wu.Safety.CorrectedFormulation
import Leader.PPL.MainTheorem.Skeleton
import Leader.PPL.MainTheorem.Statement
import Leader.PPL.MainTheorem.Kappa
import Leader.PPL.MainTheorem.WindowSPLEntryDynamicPadding
import Leader.PPL.Elim.LiteralInterface
import Leader.PPL.MainTheorem.PaddingInterface
import Leader.PPL.MainTheorem.OneLeaderDynamicPadding
import Leader.PPL.MainTheorem.SpliceCounting

/-!
# Superseded (log-window route): whole module `Leader/PPL/Theorem1CostFrom13TailSemantic.lean`

Moved (whole file) from `Leader/PPL/Theorem1CostFrom13TailSemantic.lean` by the P_PL Theorem 1 cleanup, phase 2.
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


open PPLLResearchFormulation


private theorem q20296FoldlAndFalse_existsFalse
    (xs : List Bool)
    (h : xs.foldl (fun a b => a && b) true = false) :
    Exists fun b : Bool =>
      And (b ∈ xs) (b = false) := by
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


private theorem q20296AllLeaderRootsMiss_false_exists_hit
    {n psi : Nat}
    (ring : DirectedRing n)
    (C : Config n psi (theorem1Kappa psi))
    (word : DetSchedule n)
    (hmiss :
      theorem1AllLeaderRootsMissB ring C word = false) :
    Exists fun root : Fin n =>
      And ((C root).leader = true)
        (PPL.Convergence.L18.l18HitsSPL
          ring root C word = true) := by
  unfold theorem1AllLeaderRootsMissB at hmiss
  obtain ⟨b, hbmem, hbfalse⟩ :=
    q20296FoldlAndFalse_existsFalse
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


private theorem q20296L18Hit_exists_prefix
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (word : DetSchedule n)
    (hhit :
      PPL.Convergence.L18.l18HitsSPL
        ring root C word = true) :
    Exists fun pre : DetSchedule n =>
      Exists fun suf : DetSchedule n =>
        And (word = pre ++ suf)
          (SPLAt ring root
            (PPL.Convergence.L18.runPPrime
              ring C pre)) := by
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


private theorem q20296PostConstructAlong_prefix
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
        And
          (PPL.Convergence.ConstructCoupling.PostDetermineModeConstructAt
            ring C e)
          (PPL.Convergence.ConstructCoupling.PostDetermineModeConstructAlong
            ring
            (PPL.Probability.pplStep ring C e)
            (rest ++ v))
        at h
      change
        And
          (PPL.Convergence.ConstructCoupling.PostDetermineModeConstructAt
            ring C e)
          (PPL.Convergence.ConstructCoupling.PostDetermineModeConstructAlong
            ring
            (PPL.Probability.pplStep ring C e)
            rest)
      exact
        ⟨h.1,
          ih
            (C := PPL.Probability.pplStep ring C e)
            h.2⟩


private theorem q20296RunLocalSchedule_eq_runPPL
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (word : DetSchedule n) :
    runLocalSchedule
        ring
        (PPL.protocol psi kappa).transition
        C word =
      PPL.Probability.runPPL ring C word := by
  induction word generalizing C with
  | nil =>
      rfl
  | cons e rest ih =>
      simp only
        [runLocalSchedule,
          PPL.Probability.runPPL,
          PPL.Probability.runPopulationSchedule]
      rw [
        PPLLResearchFormulation.localStep_eq_protocol_step
          (PPL.protocol psi kappa) ring C e
      ]
      simpa [PPL.Probability.runPPL] using
        ih
          (C :=
            PopulationProtocol.step
              (PPL.protocol psi kappa)
              ring C e)


theorem theorem1From13_tailSemanticPrefix_of_jointGood
    {n psi : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hnpow : n <= 2 ^ psi)
    (hpsiK : psi <= theorem1K n)
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (p suffix : DetSchedule n)
    (hstop :
      theorem1L17FirstHitStop
        ring C0 p = true)
    (hsuffix :
      suffix.length =
        theorem1H5ii n psi)
    (h5iiGood :
      theorem1L5iiFirstHitPhaseBad
          ring C0 p suffix = false)
    (h17Good :
      theorem1From13_tailL17Bad
          ring C0 p suffix = false)
    (h18Good :
      theorem1L18FirstHitPhaseBad
          ring C0 p suffix = false) :
    Exists fun k : Nat =>
      And (k <= suffix.length)
        (SPL ring
          (runLocalSchedule
            ring
            (PPL.protocol
              psi (theorem1Kappa psi)).transition
            C0
            (p ++ suffix.take k))) := by
  let Cmid :
      Config n psi (theorem1Kappa psi) :=
    PPL.Probability.runPPL ring C0 p
  let w17 : DetSchedule n :=
    suffix.take (theorem1H17 n)
  let w18 : DetSchedule n :=
    (suffix.drop (theorem1H17 n)).take
      (theorem1H18 n psi)
  let C17 :
      Config n psi (theorem1Kappa psi) :=
    PPL.Convergence.ConstructCoupling.runPrime
      ring Cmid w17

  have hconstruct :
      PPL.Modes.Lemma5.constructAlong
          ring Cmid suffix =
        true := by
    cases hc :
        PPL.Modes.Lemma5.constructAlong
          ring Cmid suffix with
    | false =>
        have hbadTrue :
            theorem1L5iiFirstHitPhaseBad
                ring C0 p suffix =
              true := by
          simp
            [theorem1L5iiFirstHitPhaseBad,
              Cmid, hc]
        rw [hbadTrue] at h5iiGood
        contradiction
    | true =>
        rfl

  have hl1Dec :
      @decide
          (PPL.LiteralL1
            (PPL.Probability.runPopulationSchedule
              PPL.Elim.protocolE ring
              (PPL.Elim.viewConfig Cmid)
              w17))
          (theorem1LiteralL1Decidable _) =
        true := by
    cases hl :
        @decide
          (PPL.LiteralL1
            (PPL.Probability.runPopulationSchedule
              PPL.Elim.protocolE ring
              (PPL.Elim.viewConfig Cmid)
              w17))
          (theorem1LiteralL1Decidable _) with
    | false =>
        have hbadTrue :
            theorem1From13_tailL17Bad
                ring C0 p suffix =
              true := by
          simp
            [theorem1From13_tailL17Bad,
              theorem1L17PhaseBad,
              Cmid, w17, hl]
        rw [hbadTrue] at h17Good
        contradiction
    | true =>
        rfl

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
            theorem1L18FirstHitPhaseBad
                ring C0 p suffix =
              true := by
          simp
            [theorem1L18FirstHitPhaseBad,
              Cmid, w17, w18, C17,
              hconstruct, hl1Dec, hr]
        rw [hbadTrue] at h18Good
        contradiction

  obtain ⟨root, _hleader, hhit⟩ :=
    q20296AllLeaderRootsMiss_false_exists_hit
      ring C17 w18 hroots

  obtain ⟨hit, hitSuf, hw18Hit, hsplPrime⟩ :=
    q20296L18Hit_exists_prefix
      ring root C17 w18 hhit

  have hpostWhole :
      PPL.Convergence.ConstructCoupling.PostDetermineModeConstructAlong
        ring Cmid suffix := by
    exact
      PPL.Convergence.ConstructCoupling.constructAlong_implies_postDetermineModeConstructAlong
          hn3 hpsi ring Cmid suffix hconstruct

  have hsplit17 :
      suffix =
        w17 ++ suffix.drop (theorem1H17 n) := by
    dsimp only [w17]
    exact
      (List.take_append_drop
        (theorem1H17 n) suffix).symm

  have htailSplit18 :
      suffix.drop (theorem1H17 n) =
        w18 ++
          (suffix.drop (theorem1H17 n)).drop
            (theorem1H18 n psi) := by
    dsimp only [w18]
    exact
      (List.take_append_drop
        (theorem1H18 n psi)
        (suffix.drop (theorem1H17 n))).symm

  let pre : DetSchedule n :=
    w17 ++ hit
  let rest : DetSchedule n :=
    hitSuf ++
      (suffix.drop (theorem1H17 n)).drop
        (theorem1H18 n psi)

  have hsuffixFactor :
      suffix = pre ++ rest := by
    calc
      suffix =
          w17 ++
            suffix.drop (theorem1H17 n) :=
        hsplit17
      _ =
          w17 ++
            (w18 ++
              (suffix.drop
                (theorem1H17 n)).drop
                  (theorem1H18 n psi)) :=
        congrArg
          (fun x => w17 ++ x)
          htailSplit18
      _ =
          (w17 ++ hit) ++
            (hitSuf ++
              (suffix.drop
                (theorem1H17 n)).drop
                  (theorem1H18 n psi)) := by
        rw [hw18Hit]
        simp only [List.append_assoc]
      _ = pre ++ rest := by
        rfl

  have hpostInput :
      PPL.Convergence.ConstructCoupling.PostDetermineModeConstructAlong
        ring Cmid (pre ++ rest) := by
    rw [← hsuffixFactor]
    exact hpostWhole

  have hpostPre :
      PPL.Convergence.ConstructCoupling.PostDetermineModeConstructAlong
        ring Cmid pre :=
    q20296PostConstructAlong_prefix
      ring Cmid pre rest hpostInput

  have hcouplePre :
      PPL.Probability.runPPL ring Cmid pre =
        PPL.Convergence.ConstructCoupling.runPrime
          ring Cmid pre :=
    PPL.Convergence.ConstructCoupling.runCoupling
      hpsi ring Cmid pre hpostPre

  have hprime17 :
      PPL.Convergence.L18.runPPrime
          ring Cmid w17 =
        C17 := by
    simpa [C17] using
      PPL.Convergence.PrimeUnify.runPPrime_eq_runPrime
        ring Cmid w17

  have hprimePre :
      PPL.Convergence.ConstructCoupling.runPrime
          ring Cmid pre =
        PPL.Convergence.L18.runPPrime
          ring C17 hit := by
    dsimp only [pre]
    rw [← PPL.Convergence.PrimeUnify.runPPrime_eq_runPrime
          ring Cmid (w17 ++ hit),
      PPL.Convergence.L18.runPPrime_append
          ring Cmid w17 hit,
      hprime17]

  have hphysicalPrime :
      PPL.Probability.runPPL ring Cmid pre =
        PPL.Convergence.L18.runPPrime
          ring C17 hit :=
    hcouplePre.trans hprimePre

  have hsplMid :
      SPL ring
        (PPL.Probability.runPPL
          ring Cmid pre) := by
    have hsplAt :
        SPLAt ring root
          (PPL.Probability.runPPL
            ring Cmid pre) := by
      rw [hphysicalPrime]
      exact hsplPrime
    exact ⟨root, hsplAt⟩

  have hglobalRun :
      PPL.Probability.runPPL
          ring C0 (p ++ pre) =
        PPL.Probability.runPPL
          ring Cmid pre := by
    simpa [Cmid] using
      theorem1L17RunPPL_append
        ring C0 p pre

  have hsplGlobal :
      SPL ring
        (PPL.Probability.runPPL
          ring C0 (p ++ pre)) := by
    rw [hglobalRun]
    exact hsplMid

  have hk :
      pre.length <= suffix.length := by
    have hlen := congrArg List.length hsuffixFactor
    simp only [pre, rest, List.length_append] at hlen
    show (w17 ++ hit).length <= suffix.length
    simp only [List.length_append]
    omega

  have htake :
      suffix.take pre.length = pre := by
    rw [hsuffixFactor]
    exact List.take_append_length

  refine ⟨pre.length, hk, ?_⟩
  rw [htake]
  rw [q20296RunLocalSchedule_eq_runPPL]
  exact hsplGlobal


end PPL.Superseded.LogWindow


#print axioms PPL.Superseded.LogWindow.theorem1From13_tailSemanticPrefix_of_jointGood
