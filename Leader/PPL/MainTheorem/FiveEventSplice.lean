import Leader.PPL.MainTheorem.Statement
import Leader.PPL.Convergence.QuietWindow

/-!
P_PL Theorem 1 cleanup, phase 2: the declarations of this file that served only the old
psi <= log2 n + 1 route to `theorem1Statement_proved` moved to
`Leader/PPL/LogWindow/FiveEventSplice.lean`, namespace `PPL.Superseded.LogWindow`: `theorem1Kappa_eq_decision`, `theorem1_l17_l18_fit`, `theorem1_prime_slice_lengths`, `Theorem1L5iiRow`, `theorem1L5iiRow_proved`, `Theorem1L18Row`, `theorem1FiveEventSplice_of_rows`, `theorem1FiveEventSplice_of_l18Row`.
-/

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-!
# Theorem-1 five-event splice

Relative to the superseded sequential splice
(`Leader/PPL/SequentialClock/Statement.lean`), the change is temporal, not
probabilistic:
* the first-hit cut is unchanged;
* kappa is theorem1Kappa;
* the outer horizon is H16 + H5i + H5ii;
* the H17 and H18 prime words are slices of that one fixed H5ii
  Construct-only window.
-/

/-! ## Generic first-hit facts -/

/-- reachesAux=true gives an actual first-hit cut for the same Boolean. -/
theorem theorem1FirstHitCut_some_of_reachesAux
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (good : Config n psi kappa → Bool)
    (C : Config n psi kappa)
    (word : DetSchedule n)
    (hreach :
      PPL.Modes.Lemma5.reachesAux
        ring good C word = true) :
    ∃ t : Nat,
      theorem1FirstHitCut
        ring good C word = some t := by
  induction word generalizing C with
  | nil =>
      cases hg : good C with
      | false =>
          simp
            [PPL.Modes.Lemma5.reachesAux, hg]
            at hreach
      | true =>
          exact
            ⟨0, by
              simp [theorem1FirstHitCut, hg]⟩
  | cons e rest ih =>
      cases hg : good C with
      | true =>
          exact
            ⟨0, by
              simp [theorem1FirstHitCut, hg]⟩
      | false =>
          have htail :
              PPL.Modes.Lemma5.reachesAux
                  ring good
                  (PPL.Probability.pplStep ring C e)
                  rest =
                true := by
            simpa
              [PPL.Modes.Lemma5.reachesAux, hg]
              using hreach
          obtain ⟨t, ht⟩ :=
            ih
              (C :=
                PPL.Probability.pplStep ring C e)
              htail
          refine ⟨t + 1, ?_⟩
          simp [theorem1FirstHitCut, hg, ht]

/-- A returned first-hit cut never lies past the supplied word. -/
theorem theorem1FirstHitCut_le_length
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (good : Config n psi kappa → Bool)
    (C : Config n psi kappa)
    (word : DetSchedule n)
    (t : Nat)
    (hcut :
      theorem1FirstHitCut
        ring good C word = some t) :
    t ≤ word.length := by
  induction word generalizing C t with
  | nil =>
      cases hg : good C with
      | false =>
          simp [theorem1FirstHitCut, hg] at hcut
      | true =>
          simp [theorem1FirstHitCut, hg] at hcut
          omega
  | cons e rest ih =>
      cases hg : good C with
      | true =>
          simp [theorem1FirstHitCut, hg] at hcut
          simp only [List.length_cons]
          omega
      | false =>
          cases hr :
              theorem1FirstHitCut
                ring good
                (PPL.Probability.pplStep ring C e)
                rest with
          | none =>
              simp
                [theorem1FirstHitCut, hg, hr]
                at hcut
          | some u =>
              have hu :=
                ih
                  (C :=
                    PPL.Probability.pplStep ring C e)
                  (t := u)
                  hr
              simp
                [theorem1FirstHitCut, hg, hr]
                at hcut
              simp only [List.length_cons]
              omega

/-!
A first hit cannot shorten the fixed Lemma-5(ii) window.
The full scheduler word has H16+H5i+H5ii letters and the cut is
inside the H5i block.
-/
theorem theorem1QuietWord_length_of_cut
    {n psi : Nat}
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (word : DetSchedule n)
    (t : Nat)
    (hmem :
      word ∈
        allSchedules n
          (theorem1Horizon n psi))
    (hcut :
      theorem1MidCut ring C0 word = some t) :
    (theorem1QuietWord psi t word).length =
      theorem1H5ii n psi := by
  have htBlock :
      t ≤ (theorem1Block5i psi word).length := by
    apply
      theorem1FirstHitCut_le_length
        ring
        PPL.Modes.Lemma5.midPhysicalB
        (theorem1State16 ring C0 word)
        (theorem1Block5i psi word)
        t
    simpa [theorem1MidCut] using hcut

  have hblock :
      (theorem1Block5i psi word).length ≤
        theorem1H5i n := by
    unfold theorem1Block5i
    simp only [List.length_take]
    exact Nat.min_le_left _ _

  have ht :
      t ≤ theorem1H5i n :=
    Nat.le_trans htBlock hblock

  have hlen :
      word.length =
        theorem1Horizon n psi :=
    allSchedules_schedule_length
      n (theorem1Horizon n psi)
      word hmem

  have havail :
      theorem1H5ii n psi ≤
        word.length -
          (theorem1H16 n psi + t) := by
    rw [hlen, theorem1Horizon_eq_phase_sum]
    omega

  unfold theorem1QuietWord
  rw [List.length_take, List.length_drop]
  exact Nat.min_eq_left havail

/-! ## The five semantic row roles -/

/-- L16 good branch: the first bad Boolean is literally false only when
the L16 block reaches C_PB. -/
def Theorem1L16Row : Prop :=
  ∀ {n psi : Nat}
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (word : DetSchedule n),
    theorem1Bad16B ring C0 word = false →
    PPL.Convergence.ReachCPB.reachesCPB
        ring C0
        (theorem1Block16 psi word) =
      true

theorem theorem1L16Row_proved :
    Theorem1L16Row := by
  unfold Theorem1L16Row
  intro n psi ring C0 word hbad
  cases hcpb :
      PPL.Convergence.ReachCPB.reachesCPB
        ring C0
        (theorem1Block16 psi word) with
  | false =>
      simp [theorem1Bad16B, hcpb] at hbad
  | true =>
      rfl

/-- L5(i) good branch: reaching C_mid supplies the same dynamic first-hit cut
used by all later events. -/
def Theorem1L5iRow : Prop :=
  ∀ {n psi : Nat}
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (word : DetSchedule n),
    PPL.Convergence.ReachCPB.reachesCPB
        ring C0
        (theorem1Block16 psi word) =
      true →
    theorem1Bad5iB ring C0 word = false →
    ∃ t : Nat,
      theorem1MidCut ring C0 word = some t

theorem theorem1L5iRow_proved :
    Theorem1L5iRow := by
  unfold Theorem1L5iRow
  intro n psi ring C0 word hcpb hbad
  cases hreach :
      PPL.Modes.Lemma5.reachesAux
        ring
        PPL.Modes.Lemma5.midPhysicalB
        (theorem1State16 ring C0 word)
        (theorem1Block5i psi word) with
  | false =>
      simp
        [theorem1Bad5iB, hcpb, hreach]
        at hbad
  | true =>
      have hcut :=
        theorem1FirstHitCut_some_of_reachesAux
          ring
          PPL.Modes.Lemma5.midPhysicalB
          (theorem1State16 ring C0 word)
          (theorem1Block5i psi word)
          hreach
      simpa [theorem1MidCut] using hcut

/-- L17 good branch: once the common cut/window premises are fixed, not being
the L17 bad event is exactly LiteralL1 at the H17 endpoint. -/
def Theorem1L17Row : Prop :=
  ∀ {n psi : Nat}
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (word : DetSchedule n)
    (t : Nat)
    (Cmid : Config n psi (theorem1Kappa psi)),
    PPL.Convergence.ReachCPB.reachesCPB
        ring C0
        (theorem1Block16 psi word) =
      true →
    theorem1MidCut ring C0 word = some t →
    theorem1MidState ring C0 word = some Cmid →
    PPL.Modes.Lemma5.constructAlong
        ring Cmid
        (theorem1QuietWord psi t word) =
      true →
    theorem1Bad17B ring C0 word = false →
    decide
        (PPL.LiteralL1
          (theorem1Literal17End
            ring Cmid t word)) =
      true

theorem theorem1L17Row_proved :
    Theorem1L17Row := by
  unfold Theorem1L17Row
  intro n psi ring C0 word t Cmid
  intro hcpb hcut hmid hconstruct hbad
  cases hl1 :
      decide
        (PPL.LiteralL1
          (theorem1Literal17End
            ring Cmid t word)) with
  | false =>
      simp
        [theorem1Bad17B,
          hcut, hmid, hcpb, hconstruct, hl1]
        at hbad
  | true =>
      rfl

end PPL

#print axioms PPL.theorem1FirstHitCut_some_of_reachesAux
#print axioms PPL.theorem1FirstHitCut_le_length
#print axioms PPL.theorem1QuietWord_length_of_cut
#print axioms PPL.theorem1L16Row_proved
#print axioms PPL.theorem1L5iRow_proved
#print axioms PPL.theorem1L17Row_proved
