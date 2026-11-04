import Leader.PPL.MainTheorem.FiveEventSplice
import Leader.PPL.MainTheorem.Statement
import Leader.PPL.Convergence.QuietWindow
import Leader.PPL.LogWindow.Statement

/-!
# Superseded (log-window route): dead declarations of `Leader/PPL/MainTheorem/FiveEventSplice.lean`

Moved out of `Leader/PPL/MainTheorem/FiveEventSplice.lean` by the P_PL Theorem 1 cleanup, phase 2.
These declarations served only the original psi <= log2 n + 1 route to
`PPL.theorem1Statement_proved`, which now goes through
`PPL.theorem1Statement_proved_via_slack` (`Leader/PPL/MainTheorem/PsiWindowSlack.lean`).
Nothing in the live Theorem 1 closure uses them; they are kept, and still build,
as the record of that route.  Every name `PPL.X` became `PPL.Superseded.LogWindow.X`;
see `research-map/RENAME_MAP_PPL.md` (phase 2).
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
namespace PPL.Superseded.LogWindow

/-- The clock decision in the advertised closed form. -/
theorem theorem1Kappa_eq_decision
    (psi : Nat) :
    theorem1Kappa psi =
      (64 * theorem1C17 + 384) * psi := by
  unfold theorem1Kappa theorem1C1 theorem1C17
  omega

/-- The arithmetic seam. -/
theorem theorem1_l17_l18_fit
    {n psi : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi)
    (hpsiK : psi ≤ theorem1K n) :
    theorem1H17 n + theorem1H18 n psi ≤
      theorem1H5ii n psi := by
  exact
    theorem1H17_add_H18_le_H5ii
      hn3 hpsi hnpow hpsiK

/-- The two prime slices are not truncated inside the quiet word. -/
theorem theorem1_prime_slice_lengths
    {n psi : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi)
    (hpsiK : psi ≤ theorem1K n)
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
    (theorem1L17Word psi t word).length =
        theorem1H17 n ∧
      (theorem1L18Word psi t word).length =
        theorem1H18 n psi := by
  have hquiet :=
    theorem1QuietWord_length_of_cut
      ring C0 word t hmem hcut
  have hfit :=
    theorem1_l17_l18_fit
      hn3 hpsi hnpow hpsiK
  have h17 :
      theorem1H17 n ≤
        theorem1H5ii n psi := by
    omega
  have h18 :
      theorem1H18 n psi ≤
        theorem1H5ii n psi -
          theorem1H17 n := by
    omega

  constructor
  · unfold theorem1L17Word
    rw [List.length_take, hquiet]
    exact Nat.min_eq_left h17
  · unfold theorem1L18Word
    rw [List.length_take, List.length_drop, hquiet]
    exact Nat.min_eq_left h18

/--
Changed row.

The superseded sequential splice could only ask for an H17+H18 suffix. This splice instead uses
the full fixed H5ii word. Therefore the already-proved deterministic
constructAlong coupling applies directly, and `theorem1_l17_l18_fit` supplies exact room for
both prime slices.
-/
def Theorem1L5iiRow : Prop :=
  ∀ {n psi : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi)
    (hpsiK : psi ≤ theorem1K n)
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (word : DetSchedule n)
    (t : Nat)
    (Cmid : Config n psi (theorem1Kappa psi)),
    word ∈
        allSchedules n
          (theorem1Horizon n psi) →
    PPL.Convergence.ReachCPB.reachesCPB
        ring C0
        (theorem1Block16 psi word) =
      true →
    theorem1MidCut ring C0 word = some t →
    theorem1MidState ring C0 word = some Cmid →
    theorem1Bad5iiB ring C0 word = false →
    PPL.Modes.Lemma5.constructAlong
        ring Cmid
        (theorem1QuietWord psi t word) =
      true ∧
      PPL.Probability.runPPL
          ring Cmid
          (theorem1QuietWord psi t word) =
        PPL.Convergence.ConstructCoupling.runPrime
          ring Cmid
          (theorem1QuietWord psi t word) ∧
      (theorem1L17Word psi t word).length =
        theorem1H17 n ∧
      (theorem1L18Word psi t word).length =
        theorem1H18 n psi

theorem theorem1L5iiRow_proved :
    Theorem1L5iiRow := by
  unfold Theorem1L5iiRow
  intro n psi
  intro hn3 hpsi hnpow hpsiK
  intro ring C0 word t Cmid
  intro hmem hcpb hcut hmid hbad

  have hconstruct :
      PPL.Modes.Lemma5.constructAlong
          ring Cmid
          (theorem1QuietWord psi t word) =
        true := by
    cases hc :
        PPL.Modes.Lemma5.constructAlong
          ring Cmid
          (theorem1QuietWord psi t word) with
    | false =>
        simp
          [theorem1Bad5iiB,
            hcut, hmid, hcpb, hc]
          at hbad
    | true =>
        rfl

  have hpost :=
    PPL.Convergence.ConstructCoupling.constructAlong_implies_postDetermineModeConstructAlong
      hn3 hpsi ring Cmid
      (theorem1QuietWord psi t word)
      hconstruct

  have hcouple :=
    PPL.Convergence.ConstructCoupling.runCoupling
      hpsi ring Cmid
      (theorem1QuietWord psi t word)
      hpost

  have hlens :=
    theorem1_prime_slice_lengths
      hn3 hpsi hnpow hpsiK
      ring C0 word t hmem hcut

  exact
    ⟨hconstruct, hcouple,
      hlens.1, hlens.2⟩

/--
The remaining semantic tail row.

This is the same Lemma-19 role as in the frozen reduction: a successful L17
one-leader endpoint followed by a successful L18 rooted prime run must lift,
through the common Construct coupling, to a full-P_PL S_PL hit. This splice changes
only the clock type/window and supplies exact H17/H18 slice lengths.
-/
def Theorem1L18Row : Prop :=
  ∀ {n psi : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi)
    (hpsiK : psi ≤ theorem1K n)
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (word : DetSchedule n)
    (t : Nat)
    (Cmid : Config n psi (theorem1Kappa psi)),
    word ∈
        allSchedules n
          (theorem1Horizon n psi) →
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
    PPL.Probability.runPPL
        ring Cmid
        (theorem1QuietWord psi t word) =
      PPL.Convergence.ConstructCoupling.runPrime
        ring Cmid
        (theorem1QuietWord psi t word) →
    decide
        (PPL.LiteralL1
          (theorem1Literal17End
            ring Cmid t word)) =
      true →
    (theorem1L17Word psi t word).length =
      theorem1H17 n →
    (theorem1L18Word psi t word).length =
      theorem1H18 n psi →
    theorem1Bad18B ring C0 word = false →
    theorem1ReachesSPL ring C0 word = true

theorem theorem1FiveEventSplice_of_rows
    (h16 : Theorem1L16Row)
    (h5i : Theorem1L5iRow)
    (h5ii : Theorem1L5iiRow)
    (h17 : Theorem1L17Row)
    (h18 : Theorem1L18Row) :
    Theorem1FiveEventSplice := by
  unfold Theorem1FiveEventSplice
  intro n psi
  intro hn3 hpsi hnpow hpsiK
  intro ring C0 word hmem hfail

  cases hb16 :
      theorem1Bad16B ring C0 word with
  | true =>
      exact Or.inl rfl
  | false =>
      have hcpb :=
        h16 ring C0 word hb16

      cases hb5i :
          theorem1Bad5iB ring C0 word with
      | true =>
          exact Or.inr (Or.inl rfl)
      | false =>
          obtain ⟨t, hcut⟩ :=
            h5i ring C0 word hcpb hb5i

          let Cmid :
              Config n psi
                (theorem1Kappa psi) :=
            PPL.Probability.runPPL
              ring
              (theorem1State16 ring C0 word)
              ((theorem1Block5i psi word).take t)

          have hmid :
              theorem1MidState ring C0 word =
                some Cmid := by
            simp
              [theorem1MidState,
                hcut, Cmid]

          cases hb5ii :
              theorem1Bad5iiB ring C0 word with
          | true =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inl rfl))
          | false =>
              have hwindow :=
                h5ii
                  hn3 hpsi hnpow hpsiK
                  ring C0 word t Cmid
                  hmem hcpb hcut hmid hb5ii

              cases hb17 :
                  theorem1Bad17B
                    ring C0 word with
              | true =>
                  exact
                    Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inl rfl)))
              | false =>
                  have hl1 :=
                    h17
                      ring C0 word t Cmid
                      hcpb hcut hmid
                      hwindow.1 hb17

                  cases hb18 :
                      theorem1Bad18B
                        ring C0 word with
                  | true =>
                      exact
                        Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr rfl)))
                  | false =>
                      have hspl :=
                        h18
                          hn3 hpsi hnpow hpsiK
                          ring C0 word t Cmid
                          hmem hcpb hcut hmid
                          hwindow.1
                          hwindow.2.1
                          hl1
                          hwindow.2.2.1
                          hwindow.2.2.2
                          hb18
                      simp [hspl] at hfail

/-- In this port, four of the five phase-row roles above are bookkeeping or
already-proved Construct coupling. The old semantic L17/L18 lift remains the
only row hypothesis in this source-visible reduction. -/
theorem theorem1FiveEventSplice_of_l18Row
    (h18 : Theorem1L18Row) :
    Theorem1FiveEventSplice :=
  theorem1FiveEventSplice_of_rows
    theorem1L16Row_proved
    theorem1L5iRow_proved
    theorem1L5iiRow_proved
    theorem1L17Row_proved
    h18

end PPL.Superseded.LogWindow
end
