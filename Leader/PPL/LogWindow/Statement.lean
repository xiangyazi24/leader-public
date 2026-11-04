import Leader.PPL.MainTheorem.Statement
import Leader.PPL.MainTheorem.Kappa
import Leader.PPL.MainTheorem.SpliceCounting
import Leader.PPL.LogWindow.Kappa

/-!
# Superseded (log-window route): dead declarations of `Leader/PPL/MainTheorem/Statement.lean`

Moved out of `Leader/PPL/MainTheorem/Statement.lean` by the P_PL Theorem 1 cleanup, phase 2.
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

theorem theorem1H17_add_H18_le_H5ii
    {n psi : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hnpow : n <= 2 ^ psi)
    (hpsiK : psi <= theorem1K n) :
    theorem1H17 n + theorem1H18 n psi <=
      theorem1H5ii n psi := by
  simpa
    [theorem1H17, theorem1H18, theorem1H5ii]
    using
      theorem1_quietWindow_covers_run
        hn3 hpsi hnpow hpsiK

/--
the earlier five-event semantic splice, retargeted to theorem1Kappa and theorem1Horizon.

The third event is now failure of the full fixed H5ii(theorem1Kappa) Construct
window beginning at the dynamic first C_mid cut.  The L17 and L18 words are
slices of that same quiet word.
-/
def Theorem1FiveEventSplice : Prop :=
  forall {n psi : Nat},
    3 <= n ->
    2 <= psi ->
    n <= 2 ^ psi ->
    psi <= theorem1K n ->
    forall
      (ring : DirectedRing n)
      (C0 : Config n psi (theorem1Kappa psi))
      (word : DetSchedule n),
      word ∈ allSchedules n
        (theorem1Horizon n psi) ->
      !(theorem1ReachesSPL ring C0 word) = true ->
      Or
        (theorem1Bad16B ring C0 word = true)
        (Or
          (theorem1Bad5iB ring C0 word = true)
          (Or
            (theorem1Bad5iiB ring C0 word = true)
            (Or
              (theorem1Bad17B ring C0 word = true)
              (theorem1Bad18B ring C0 word = true))))

def Theorem1L5iPaddedBound : Prop :=
  forall {n psi : Nat},
    3 <= n ->
    2 <= psi ->
    n <= 2 ^ psi ->
    psi <= theorem1K n ->
    forall
      (ring : DirectedRing n)
      (C0 : Config n psi (theorem1Kappa psi)),
      n *
          (allSchedules n
            (theorem1Horizon n psi)).countP
              (theorem1Bad5iB ring C0) <=
        8 * n ^ theorem1Horizon n psi

def Theorem1L5iiDynamicPaddedBound : Prop :=
  forall {n psi : Nat},
    3 <= n ->
    2 <= psi ->
    n <= 2 ^ psi ->
    psi <= theorem1K n ->
    forall
      (ring : DirectedRing n)
      (C0 : Config n psi (theorem1Kappa psi)),
      n *
          (allSchedules n
            (theorem1Horizon n psi)).countP
              (theorem1Bad5iiB ring C0) <=
        4 * n ^ theorem1Horizon n psi

def Theorem1L17DynamicPaddedBound : Prop :=
  forall {n psi : Nat},
    3 <= n ->
    2 <= psi ->
    n <= 2 ^ psi ->
    psi <= theorem1K n ->
    forall
      (ring : DirectedRing n)
      (C0 : Config n psi (theorem1Kappa psi)),
      n *
          (allSchedules n
            (theorem1Horizon n psi)).countP
              (theorem1Bad17B ring C0) <=
        n ^ theorem1Horizon n psi

def Theorem1L18DynamicPaddedBound : Prop :=
  forall {n psi : Nat},
    3 <= n ->
    2 <= psi ->
    n <= 2 ^ psi ->
    psi <= theorem1K n ->
    forall
      (ring : DirectedRing n)
      (C0 : Config n psi (theorem1Kappa psi)),
      n *
          (allSchedules n
            (theorem1Horizon n psi)).countP
              (theorem1Bad18B ring C0) <=
        n ^ theorem1Horizon n psi

/--
The WHP conjunct follows from the semantic splice and the five padded
phase bounds.  The finite union and coefficient arithmetic are reused
verbatim from Superseded.Theorem1FiveEventSplice.
-/
theorem theorem1_whp_of_splice
    (hsplice : Theorem1FiveEventSplice)
    (h16 : Theorem1L16PaddedBound)
    (h5i : Theorem1L5iPaddedBound)
    (h5ii : Theorem1L5iiDynamicPaddedBound)
    (h17 : Theorem1L17DynamicPaddedBound)
    (h18 : Theorem1L18DynamicPaddedBound)
    {n psi : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hnpow : n <= 2 ^ psi)
    (hpsiK : psi <= theorem1K n)
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi)) :
    let H := theorem1Horizon n psi
    n * theorem1FailureNumerator ring C0 H <=
      64 * n ^ H := by
  dsimp only

  have hb16 :=
    h16 hn3 hpsi hnpow hpsiK ring C0
  have hb5i :=
    h5i hn3 hpsi hnpow hpsiK ring C0
  have hb5ii :=
    h5ii hn3 hpsi hnpow hpsiK ring C0
  have hb17 :=
    h17 hn3 hpsi hnpow hpsiK ring C0
  have hb18 :=
    h18 hn3 hpsi hnpow hpsiK ring C0

  have hfailure :
      theorem1FailureNumerator
          ring C0
          (theorem1Horizon n psi) <=
        (allSchedules n
            (theorem1Horizon n psi)).countP
              (theorem1Bad16B ring C0) +
        (allSchedules n
            (theorem1Horizon n psi)).countP
              (theorem1Bad5iB ring C0) +
        (allSchedules n
            (theorem1Horizon n psi)).countP
              (theorem1Bad5iiB ring C0) +
        (allSchedules n
            (theorem1Horizon n psi)).countP
              (theorem1Bad17B ring C0) +
        (allSchedules n
            (theorem1Horizon n psi)).countP
              (theorem1Bad18B ring C0) := by
    unfold theorem1FailureNumerator
    exact
      theorem1_countP_five_union_le
        (allSchedules n
          (theorem1Horizon n psi))
        (fun word =>
          !(theorem1ReachesSPL
            ring C0 word))
        (theorem1Bad16B ring C0)
        (theorem1Bad5iB ring C0)
        (theorem1Bad5iiB ring C0)
        (theorem1Bad17B ring C0)
        (theorem1Bad18B ring C0)
        (fun word hmem hbad =>
          hsplice
            hn3 hpsi hnpow hpsiK
            ring C0 word hmem
            (by simpa using hbad))

  have hscaled :=
    Nat.mul_le_mul_left n hfailure

  have hphase :
      n *
          (allSchedules n
            (theorem1Horizon n psi)).countP
              (theorem1Bad16B ring C0) +
        n *
          (allSchedules n
            (theorem1Horizon n psi)).countP
              (theorem1Bad5iB ring C0) +
        n *
          (allSchedules n
            (theorem1Horizon n psi)).countP
              (theorem1Bad5iiB ring C0) +
        n *
          (allSchedules n
            (theorem1Horizon n psi)).countP
              (theorem1Bad17B ring C0) +
        n *
          (allSchedules n
            (theorem1Horizon n psi)).countP
              (theorem1Bad18B ring C0) <=
      12 * n ^ theorem1Horizon n psi +
        8 * n ^ theorem1Horizon n psi +
        4 * n ^ theorem1Horizon n psi +
        n ^ theorem1Horizon n psi +
        n ^ theorem1Horizon n psi := by
    exact
      Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add
            (Nat.add_le_add hb16 hb5i)
            hb5ii)
          hb17)
        hb18

  calc
    n *
          theorem1FailureNumerator
            ring C0
            (theorem1Horizon n psi) <=
        n *
          ((allSchedules n
              (theorem1Horizon n psi)).countP
                (theorem1Bad16B ring C0) +
            (allSchedules n
              (theorem1Horizon n psi)).countP
                (theorem1Bad5iB ring C0) +
            (allSchedules n
              (theorem1Horizon n psi)).countP
                (theorem1Bad5iiB ring C0) +
            (allSchedules n
              (theorem1Horizon n psi)).countP
                (theorem1Bad17B ring C0) +
            (allSchedules n
              (theorem1Horizon n psi)).countP
                (theorem1Bad18B ring C0)) :=
      hscaled
    _ =
        n *
            (allSchedules n
              (theorem1Horizon n psi)).countP
                (theorem1Bad16B ring C0) +
          n *
            (allSchedules n
              (theorem1Horizon n psi)).countP
                (theorem1Bad5iB ring C0) +
          n *
            (allSchedules n
              (theorem1Horizon n psi)).countP
                (theorem1Bad5iiB ring C0) +
          n *
            (allSchedules n
              (theorem1Horizon n psi)).countP
                (theorem1Bad17B ring C0) +
          n *
            (allSchedules n
              (theorem1Horizon n psi)).countP
                (theorem1Bad18B ring C0) := by
      simp only [Nat.mul_add]
    _ <=
        12 * n ^ theorem1Horizon n psi +
          8 * n ^ theorem1Horizon n psi +
          4 * n ^ theorem1Horizon n psi +
          n ^ theorem1Horizon n psi +
          n ^ theorem1Horizon n psi :=
      hphase
    _ <=
        64 * n ^ theorem1Horizon n psi :=
      theorem1_five_event_constants
        n (theorem1Horizon n psi)

end PPL.Superseded.LogWindow
end
