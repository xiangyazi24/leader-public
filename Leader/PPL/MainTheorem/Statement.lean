import Leader.PPL.MainTheorem.Kappa
import Leader.PPL.MainTheorem.SpliceCounting

/-!
P_PL Theorem 1 cleanup, phase 2: the declarations of this file that served only the old
psi <= log2 n + 1 route to `theorem1Statement_proved` moved to
`Leader/PPL/LogWindow/Statement.lean`, namespace `PPL.Superseded.LogWindow`: `theorem1H17_add_H18_le_H5ii`, `Theorem1FiveEventSplice`, `Theorem1L5iPaddedBound`, `Theorem1L5iiDynamicPaddedBound`, `Theorem1L17DynamicPaddedBound`, `Theorem1L18DynamicPaddedBound`, `theorem1_whp_of_splice`.
-/

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-! ## Statement -/

/--
Theorem 1 with the enlarged absolute clock constant and the paper-faithful
fixed Lemma-5(ii) quiet window.
-/
def Theorem1Statement : Prop :=
  Exists fun cExpected : Nat =>
    And (0 < cExpected)
      (And (32 * theorem1C17 + 352 <= theorem1C1)
        (And (theorem1C1 % 16 = 0)
          (forall {n psi : Nat},
            3 <= n ->
            2 <= psi ->
            n <= 2 ^ psi ->
            psi <= theorem1K n ->
            forall
              (ring : DirectedRing n)
              (C0 : Config n psi (theorem1Kappa psi)),
              let H := theorem1Horizon n psi
              And
                (forall C : Config n psi (theorem1Kappa psi),
                  SPL ring C ->
                    PopulationProtocol.IsSafe
                      (protocol psi (theorem1Kappa psi))
                      ring C PPL.Safety.SPL.output)
                (And
                  (n * theorem1FailureNumerator ring C0 H <=
                    64 * n ^ H)
                  (forall T : Nat,
                    theorem1CostNumerator ring C0 T <=
                      n ^ T * (cExpected * H))))))

/-! ## Phase horizons -/

def theorem1H16 (n psi : Nat) : Nat :=
  PPL.Convergence.ReachCPB.lemma16Horizon
    n psi (theorem1Kappa psi)

def theorem1H5i (n : Nat) : Nat :=
  PPL.Modes.Lemma5.lemma5iHorizon n

def theorem1H5ii (n psi : Nat) : Nat :=
  PPL.Modes.Lemma5.lemma5iiHorizon
    n psi (theorem1Kappa psi)

def theorem1H17 (n : Nat) : Nat :=
  PPL.Convergence.L17.H17 theorem1C17 n

def theorem1H18 (n psi : Nat) : Nat :=
  PPL.Convergence.L18.l18Horizon n psi

theorem theorem1Horizon_eq_phase_sum
    (n psi : Nat) :
    theorem1Horizon n psi =
      theorem1H16 n psi +
        theorem1H5i n +
        theorem1H5ii n psi := by
  rfl

/-! ## Dynamic C_mid cut at theorem1Kappa -/

def theorem1Block16
    {n : Nat}
    (psi : Nat)
    (word : DetSchedule n) :
    DetSchedule n :=
  word.take (theorem1H16 n psi)

def theorem1Block5i
    {n : Nat}
    (psi : Nat)
    (word : DetSchedule n) :
    DetSchedule n :=
  (word.drop (theorem1H16 n psi)).take
    (theorem1H5i n)

def theorem1State16
    {n psi : Nat}
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (word : DetSchedule n) :
    Config n psi (theorem1Kappa psi) :=
  PPL.Probability.runPPL
    ring C0 (theorem1Block16 psi word)

def theorem1MidCut
    {n psi : Nat}
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (word : DetSchedule n) :
    Option Nat :=
  theorem1FirstHitCut
    ring
    PPL.Modes.Lemma5.midPhysicalB
    (theorem1State16 ring C0 word)
    (theorem1Block5i psi word)

def theorem1MidState
    {n psi : Nat}
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (word : DetSchedule n) :
    Option (Config n psi (theorem1Kappa psi)) :=
  match theorem1MidCut ring C0 word with
  | none => none
  | some t =>
      some
        (PPL.Probability.runPPL
          ring
          (theorem1State16 ring C0 word)
          ((theorem1Block5i psi word).take t))

/--
The paper-faithful Lemma-5(ii) window starts at the dynamic first C_mid cut.
Its length is the full fixed H5ii(theorem1Kappa), not merely H17+H18.
-/
def theorem1QuietWord
    {n : Nat}
    (psi t : Nat)
    (word : DetSchedule n) :
    DetSchedule n :=
  (word.drop (theorem1H16 n psi + t)).take
    (theorem1H5ii n psi)

/--
L17 and L18 execute inside the same Construct-only window.  The imported
theorem1_quietWindow_covers_run is exactly the arithmetic certificate that
these two slices fit.
-/
def theorem1L17Word
    {n : Nat}
    (psi t : Nat)
    (word : DetSchedule n) :
    DetSchedule n :=
  (theorem1QuietWord psi t word).take
    (theorem1H17 n)

def theorem1L18Word
    {n : Nat}
    (psi t : Nat)
    (word : DetSchedule n) :
    DetSchedule n :=
  ((theorem1QuietWord psi t word).drop
      (theorem1H17 n)).take
    (theorem1H18 n psi)

def theorem1Literal17End
    {n psi : Nat}
    (ring : DirectedRing n)
    (Cmid : Config n psi (theorem1Kappa psi))
    (t : Nat)
    (word : DetSchedule n) :
    PPL.LiteralElimConfig n :=
  PPL.Probability.runPopulationSchedule
    PPL.Elim.protocolE ring
    (PPL.Elim.viewConfig Cmid)
    (theorem1L17Word psi t word)

def theorem1Prime17End
    {n psi : Nat}
    (ring : DirectedRing n)
    (Cmid : Config n psi (theorem1Kappa psi))
    (t : Nat)
    (word : DetSchedule n) :
    Config n psi (theorem1Kappa psi) :=
  PPL.Convergence.ConstructCoupling.runPrime
    ring Cmid
    (theorem1L17Word psi t word)

def theorem1AllLeaderRootsMissB
    {n psi : Nat}
    (ring : DirectedRing n)
    (C : Config n psi (theorem1Kappa psi))
    (word : DetSchedule n) : Bool :=
  (List.ofFn
      (fun root : Fin n =>
        (!(C root).leader) ||
          !(PPL.Convergence.L18.l18HitsSPL
            ring root C word))).foldl
    (fun a b => a && b) true

/-! ## Five bad events -/

def theorem1Bad16B
    {n psi : Nat}
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (word : DetSchedule n) : Bool :=
  !(PPL.Convergence.ReachCPB.reachesCPB
    ring C0 (theorem1Block16 psi word))

def theorem1Bad5iB
    {n psi : Nat}
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (word : DetSchedule n) : Bool :=
  PPL.Convergence.ReachCPB.reachesCPB
      ring C0 (theorem1Block16 psi word) &&
    !(PPL.Modes.Lemma5.reachesAux
      ring
      PPL.Modes.Lemma5.midPhysicalB
      (theorem1State16 ring C0 word)
      (theorem1Block5i psi word))

def theorem1Bad5iiB
    {n psi : Nat}
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (word : DetSchedule n) : Bool :=
  match theorem1MidCut ring C0 word,
      theorem1MidState ring C0 word with
  | some t, some Cmid =>
      PPL.Convergence.ReachCPB.reachesCPB
          ring C0 (theorem1Block16 psi word) &&
        !(PPL.Modes.Lemma5.constructAlong
          ring Cmid
          (theorem1QuietWord psi t word))
  | _, _ => false

def theorem1Bad17B
    {n psi : Nat}
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (word : DetSchedule n) : Bool :=
  match theorem1MidCut ring C0 word,
      theorem1MidState ring C0 word with
  | some t, some Cmid =>
      PPL.Convergence.ReachCPB.reachesCPB
          ring C0 (theorem1Block16 psi word) &&
        PPL.Modes.Lemma5.constructAlong
          ring Cmid
          (theorem1QuietWord psi t word) &&
        !(decide
          (PPL.LiteralL1
            (theorem1Literal17End
              ring Cmid t word)))
  | _, _ => false

def theorem1Bad18B
    {n psi : Nat}
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (word : DetSchedule n) : Bool :=
  match theorem1MidCut ring C0 word,
      theorem1MidState ring C0 word with
  | some t, some Cmid =>
      let C17 :=
        theorem1Prime17End ring Cmid t word
      PPL.Convergence.ReachCPB.reachesCPB
          ring C0 (theorem1Block16 psi word) &&
        PPL.Modes.Lemma5.constructAlong
          ring Cmid
          (theorem1QuietWord psi t word) &&
        decide
          (PPL.LiteralL1
            (theorem1Literal17End
              ring Cmid t word)) &&
        theorem1AllLeaderRootsMissB
          ring C17
          (theorem1L18Word psi t word)
  | _, _ => false

/-! ## Five padded counting interfaces -/

def Theorem1L16PaddedBound : Prop :=
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
              (theorem1Bad16B ring C0) <=
        12 * n ^ theorem1Horizon n psi

end PPL

#print axioms PPL.theorem1Horizon_eq_phase_sum
