import Leader.PPL.PsiAtLeastN.SafeFirstHit
import Leader.PPL.MainTheorem.GeneralSplice

/-!
# P_PL Theorem 1 on `n ≤ psi`: the safe five-event splice

The splice rows of `Leader/PPL/PsiBelowN/Splice.lean` with the domain premise
`n ≤ psi` and the safe target.  The L16, L5(i) and L17 rows have no domain
premise and are reused from `PPL`; the L5(ii) row carries the premise and
never uses it.  The L18 row (`Theorem1L18SafeRow`) is the one place where
`n ≤ psi` is used: a rooted `C_DL` endpoint of the coupled `P_PL` run is in
`Theorem1SafeTarget` because `n ≤ psi` gives one segment
(`theorem1SafeTarget_of_l18SafeAt`).

P_PL Theorem 1 cleanup, phase 2, step 6b: every proof here is a special case
of `Leader/PPL/MainTheorem/GeneralSplice.lean` with the global test
`theorem1ReachesSafeTarget` and the rooted predicate `L18SafeAt`, through the
bridging equalities of `SafeRows.lean`; the statements are unchanged and the private
`q20203*` helper copies are gone.
-/

namespace PPL.PsiAtLeastN

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-! ## Safe-target hitting helpers -/

/-- On `1 ≤ n ≤ psi`, a rooted safe configuration (rooted `S_PL` or rooted
`C_DL`) is in `Theorem1SafeTarget`. -/
theorem theorem1SafeTarget_of_l18SafeAt
    {n psi kappa : Nat} (hn : 1 ≤ n) (hge : n ≤ psi)
    {ring : DirectedRing n} {root : Fin n} {C : Config n psi kappa}
    (h : L18SafeAt ring root C) :
    Theorem1SafeTarget ring C := by
  rcases h with hspl | hcdl
  · exact Or.inl ⟨root, hspl⟩
  · exact Or.inr ⟨segmentCount_eq_one_of_le hn hge, root, hcdl⟩

/-- Prefix hitting of the safe target is monotone under appending a suffix
(`PPL.Theorem1General.theorem1ReachesB_append_of_left`). -/
theorem theorem1ReachesSafeTarget_append_of_left
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (pre suf : DetSchedule n)
    (hpre : theorem1ReachesSafeTarget ring C pre = true) :
    theorem1ReachesSafeTarget ring C (pre ++ suf) = true := by
  rw [theorem1ReachesSafeTarget_eq] at hpre ⊢
  exact
    PPL.Theorem1General.theorem1ReachesB_append_of_left
      ring _ C pre suf hpre

/-- The arithmetic seam (the domain premise is unused;
`PPL.Theorem1General.theorem1H17_add_H18_le_H5ii`). -/
theorem theorem1_l17_l18_fit
    {n psi : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi)
    (_hge : n ≤ psi) :
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
    (_hge : n ≤ psi)
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
    (hge : n ≤ psi)
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
  intro n psi hn3 hpsi hnpow _hge ring C0 word t Cmid
  exact
    PPL.Theorem1General.theorem1L5iiRow_at
      hn3 hpsi hnpow ring C0 word t Cmid

/--
The remaining semantic tail row.

Safe version, on `n ≤ psi`: a successful L17 one-leader endpoint followed
by an L18 rooted prime run that hits rooted `S_PL` or rooted `C_DL` lifts,
through the common Construct coupling, to a full-P_PL hit of
`Theorem1SafeTarget` (one segment, so rooted `C_DL` is in the target).
-/
def Theorem1L18SafeRow : Prop :=
  ∀ {n psi : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi)
    (hge : n ≤ psi)
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
    theorem1Bad18SafeB ring C0 word = false →
    theorem1ReachesSafeTarget ring C0 word = true


/-- The five-way assembly (`PPL.Theorem1General.theorem1FiveEventSplice_at`
with the global test `theorem1ReachesSafeTarget` and the L18 event
`theorem1Bad18SafeB`). -/
theorem theorem1SafeFiveEventSplice_of_rows
    (h16 : Theorem1L16Row)
    (h5i : Theorem1L5iRow)
    (h5ii : Theorem1L5iiRow)
    (h17 : Theorem1L17Row)
    (h18 : Theorem1L18SafeRow) :
    Theorem1SafeFiveEventSplice := by
  unfold Theorem1SafeFiveEventSplice
  intro n psi hn3 hpsi hnpow hge ring C0 word hmem hfail
  exact
    PPL.Theorem1General.theorem1FiveEventSplice_at
      theorem1ReachesSafeTarget theorem1Bad18SafeB
      h16 h5i h17
      (h5ii hn3 hpsi hnpow hge)
      (h18 hn3 hpsi hnpow hge)
      ring C0 word hmem hfail

/-- In this port, four of the five phase-row roles above are bookkeeping or
already-proved Construct coupling. The old semantic L17/L18 lift remains the
only row hypothesis in this source-visible reduction. -/
theorem theorem1SafeFiveEventSplice_of_l18Row
    (h18 : Theorem1L18SafeRow) :
    Theorem1SafeFiveEventSplice :=
  theorem1SafeFiveEventSplice_of_rows
    theorem1L16Row_proved
    theorem1L5iRow_proved
    theorem1L5iiRow_proved
    theorem1L17Row_proved
    h18



/-- The safe L18 row (`PPL.Theorem1General.theorem1L18Row_at` with the
rooted predicate `L18SafeAt` and the global target `Theorem1SafeTarget`; a
rooted hit is a global hit on `n ≤ psi` by
`theorem1SafeTarget_of_l18SafeAt`). -/
theorem theorem1L18SafeRow_proved :
    Theorem1L18SafeRow := by
  unfold Theorem1L18SafeRow
  intro n psi hn3 hpsi _hnpow hge ring C0 word t Cmid
  intro hmem hcpb hcut hmid hconstruct _hwholeCoupling hl1 _hlen17 _hlen18
  intro hbad
  rw [theorem1ReachesSafeTarget_eq]
  rw [theorem1Bad18SafeB_eq] at hbad
  exact
    PPL.Theorem1General.theorem1L18Row_at ring
      (fun root C => decide (L18SafeAt ring root C))
      (fun C => decide (Theorem1SafeTarget ring C))
      (fun _root _C h =>
        decide_eq_true
          (theorem1SafeTarget_of_l18SafeAt (by omega) hge
            (of_decide_eq_true h)))
      hn3 hpsi C0 word t Cmid
      hmem hcpb hcut hmid hconstruct hl1 hbad

/-- The safe five-event splice on `n ≤ psi`, unconditionally. -/
theorem theorem1SafeFiveEventSplice_proved :
    Theorem1SafeFiveEventSplice :=
  theorem1SafeFiveEventSplice_of_l18Row
    theorem1L18SafeRow_proved

end PPL.PsiAtLeastN

#print axioms PPL.PsiAtLeastN.theorem1ReachesSafeTarget_append_of_left
#print axioms PPL.PsiAtLeastN.theorem1L18SafeRow_proved
#print axioms PPL.PsiAtLeastN.theorem1SafeFiveEventSplice_proved
