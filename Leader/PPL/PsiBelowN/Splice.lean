import Leader.PPL.PsiBelowN.Rows
import Leader.PPL.MainTheorem.GeneralSplice

/-!
# P_PL Theorem 1 on `psi < n`: the five-event splice

The splice rows that carry the psi window (`Theorem1L5iiRow`,
`Theorem1L18Row`), the five-way assembly, and the proved L18 row, for the
target `S_PL`.  The window premise `psi < n` is carried in the statements and
never used; the L16, L5(i) and L17 rows have no window premise and are reused
from `PPL`.

P_PL Theorem 1 cleanup, phase 2, step 6b: every proof here is a special case
of `Leader/PPL/MainTheorem/GeneralSplice.lean` (target `S_PL`, rooted `S_PL`);
the statements are unchanged.  The private `q20203*` helper copies are gone;
their general versions are in that module.
-/

namespace PPL.PsiBelowN

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-- The arithmetic seam (the window premise is unused;
`PPL.Theorem1General.theorem1H17_add_H18_le_H5ii`). -/
theorem theorem1_l17_l18_fit
    {n psi : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi)
    (_hpsiK : psi < n) :
    theorem1H17 n + theorem1H18 n psi ≤
      theorem1H5ii n psi :=
  PPL.Theorem1General.theorem1H17_add_H18_le_H5ii hn3 hpsi hnpow

/-- The two prime slices are not truncated inside the quiet word
(`PPL.Theorem1General.theorem1_prime_slice_lengths`). -/
theorem theorem1_prime_slice_lengths
    {n psi : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi)
    (_hpsiK : psi < n)
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
        theorem1H18 n psi :=
  PPL.Theorem1General.theorem1_prime_slice_lengths
    hn3 hpsi hnpow ring C0 word t hmem hcut

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
    (hpsiK : psi < n)
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


/-- The L5(ii) row (`PPL.Theorem1General.theorem1L5iiRow_at`). -/
theorem theorem1L5iiRow_proved :
    Theorem1L5iiRow := by
  unfold Theorem1L5iiRow
  intro n psi hn3 hpsi hnpow _hpsiK ring C0 word t Cmid
  exact
    PPL.Theorem1General.theorem1L5iiRow_at
      hn3 hpsi hnpow ring C0 word t Cmid

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
    (hpsiK : psi < n)
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


/-- The five-way assembly (`PPL.Theorem1General.theorem1FiveEventSplice_at`
with the global test `theorem1ReachesSPL` and the L18 event
`theorem1Bad18B`). -/
theorem theorem1FiveEventSplice_of_rows
    (h16 : Theorem1L16Row)
    (h5i : Theorem1L5iRow)
    (h5ii : Theorem1L5iiRow)
    (h17 : Theorem1L17Row)
    (h18 : Theorem1L18Row) :
    Theorem1FiveEventSplice := by
  unfold Theorem1FiveEventSplice
  intro n psi hn3 hpsi hnpow hpsiK ring C0 word hmem hfail
  exact
    PPL.Theorem1General.theorem1FiveEventSplice_at
      theorem1ReachesSPL theorem1Bad18B
      h16 h5i h17
      (h5ii hn3 hpsi hnpow hpsiK)
      (h18 hn3 hpsi hnpow hpsiK)
      ring C0 word hmem hfail

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



/-- The L18 row (`PPL.Theorem1General.theorem1L18RowSPL_at`). -/
theorem theorem1L18Row_proved :
    Theorem1L18Row := by
  unfold Theorem1L18Row
  intro n psi hn3 hpsi _hnpow _hpsiK ring C0 word t Cmid
  intro hmem hcpb hcut hmid hconstruct _hwholeCoupling hl1 _hlen17 _hlen18
  intro hbad
  exact
    PPL.Theorem1General.theorem1L18RowSPL_at
      hn3 hpsi ring C0 word t Cmid
      hmem hcpb hcut hmid hconstruct hl1 hbad

/-- The five-event splice with its only open input discharged. -/
theorem theorem1FiveEventSplice_proved :
    Theorem1FiveEventSplice :=
  theorem1FiveEventSplice_of_l18Row
    theorem1L18Row_proved

end PPL.PsiBelowN

#print axioms PPL.PsiBelowN.theorem1FiveEventSplice_proved
