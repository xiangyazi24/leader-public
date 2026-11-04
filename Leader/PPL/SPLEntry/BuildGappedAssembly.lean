import Leader.PPL.SPLEntry.ForcingWord
import Init.Data.List.Sublist
import Init.Omega

namespace PPL.Convergence.L18

set_option autoImplicit false
set_option Elab.async false

def L18BuildPairOK
    {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa) (seg : Nat) : Prop :=
  And
    (rootedSegmentId ring root C (seg + 1) =
      (rootedSegmentId ring root C seg + 1) % (2 ^ psi))
    (forall i : Fin n,
      And
        ((And
            (ValidToken .black C i)
            (WorkingFor ring root C i .black seg)) ->
          CorrectToken ring root C i .black seg)
        ((And
            (ValidToken .white C i)
            (WorkingFor ring root C i .white seg)) ->
          CorrectToken ring root C i .white seg))

def L18BuildPrefixAt
    {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (b : Nat) (C : Config n psi kappa) : Prop :=
  And
    (CDLAt ring root C)
    (And
      (L18NoRiskyAt ring root C)
      (forall seg : Fin (l18BlockCount n psi),
        seg.val < b ->
          L18BuildPairOK ring root C seg.val))

def L18BuildBlockAdvanceRow : Prop :=
  forall {n psi kappa : Nat}
    (hn3 : 3 <= n) (hpsi : 2 <= psi)
    (ring : DirectedRing n) (root : Fin n)
    (b : Nat)
    (C : Config n psi kappa)
    (schedule : DetSchedule n)
    (hlemma4 : PPL.lemma4_deterministic_core),
    b < l18BlockCount n psi ->
    L18BuildPrefixAt ring root b C ->
    (PPL.lemma4Word ring
      (shiftRight ring root (b * psi)) psi).Sublist schedule ->
    Or
      (l18HitsSPL ring root C schedule = true)
      (L18BuildPrefixAt ring root (b + 1)
        (runPPrime ring C schedule))

private theorem l18BuildPrefixAt_zero
    {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa)
    (hCDL : CDLAt ring root C)
    (hRisk : L18NoRiskyAt ring root C) :
    L18BuildPrefixAt ring root 0 C := by
  refine And.intro hCDL (And.intro hRisk ?_)
  intro seg hlt
  omega

private theorem l18BuildPrefixAt_full_spl
    {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa)
    (h :
      L18BuildPrefixAt ring root
        (l18BlockCount n psi) C) :
    SPLAt ring root C := by
  change
    And
      (CDLAt ring root C)
      (And
        (L18NoRiskyAt ring root C)
        (forall seg : Fin (l18BlockCount n psi),
          L18BuildPairOK ring root C seg.val))
  exact
    And.intro h.1
      (And.intro h.2.1
        (fun seg => h.2.2 seg seg.isLt))

private theorem l18HitsSPL_of_initial
    {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa)
    (schedule : DetSchedule n)
    (hS : SPLAt ring root C) :
    l18HitsSPL ring root C schedule = true := by
  cases schedule with
  | nil =>
      simp [l18HitsSPL, hS]
  | cons e rest =>
      simp [l18HitsSPL, hS]

private theorem l18HitsSPL_append_left_true
    {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa)
    (pre0 suffix : DetSchedule n)
    (h :
      l18HitsSPL ring root C pre0 = true) :
    l18HitsSPL ring root C (pre0 ++ suffix) = true := by
  induction pre0 generalizing C with
  | nil =>
      cases suffix with
      | nil =>
          simpa only [List.nil_append] using h
      | cons e rest =>
          have hC :
              decide (SPLAt ring root C) = true := by
            simpa only [l18HitsSPL] using h
          simp only [List.nil_append, l18HitsSPL, hC, Bool.true_or]
  | cons e rest ih =>
      simp only [l18HitsSPL] at h
      simp only [List.cons_append, l18HitsSPL]
      cases hs : decide (SPLAt ring root C) with
      | false =>
          simp only [hs, Bool.false_or] at h
          simp only [hs, Bool.false_or]
          exact
            ih (C := pprimeStep ring C e) h
      | true =>
          simp only [hs, Bool.true_or]

private theorem l18HitsSPL_append_right_true
    {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa)
    (pre0 suffix : DetSchedule n)
    (h :
      l18HitsSPL ring root
        (runPPrime ring C pre0) suffix = true) :
    l18HitsSPL ring root C (pre0 ++ suffix) = true := by
  induction pre0 generalizing C with
  | nil =>
      simpa only [runPPrime, List.nil_append] using h
  | cons e rest ih =>
      simp only [runPPrime] at h
      simp only [List.cons_append, l18HitsSPL]
      cases hs : decide (SPLAt ring root C) with
      | false =>
          simp only [hs, Bool.false_or]
          exact
            ih (C := pprimeStep ring C e) h
      | true =>
          simp only [hs, Bool.true_or]

private theorem l18BuildPositiveBlocks_of_rows
    (hBlock : L18BuildBlockAdvanceRow)
    {n psi kappa : Nat}
    (hn3 : 3 <= n) (hpsi : 2 <= psi)
    (ring : DirectedRing n) (root : Fin n)
    (m : Nat)
    (C : Config n psi kappa)
    (schedule : DetSchedule n)
    (hmPos : 0 < m)
    (hmLe : m <= l18BlockCount n psi)
    (hlemma4 : PPL.lemma4_deterministic_core)
    (hPrefix : L18BuildPrefixAt ring root 0 C)
    (hsub :
      (l18Lemma4Blocks ring root psi m).Sublist schedule) :
    Or
      (l18HitsSPL ring root C schedule = true)
      (L18BuildPrefixAt ring root m
        (runPPrime ring C schedule)) := by
  induction m generalizing C schedule with
  | zero =>
      omega
  | succ m ih =>
      cases m with
      | zero =>
          have hbound :
              0 < l18BlockCount n psi := by
            omega
          change
            (PPL.lemma4Word ring
              (shiftRight ring root (0 * psi)) psi).Sublist
                schedule
            at hsub
          exact
            hBlock hn3 hpsi ring root 0
              C schedule hlemma4 hbound hPrefix hsub
      | succ p =>
          change
            (l18Lemma4Blocks ring root psi (Nat.succ p) ++
              PPL.lemma4Word ring
                (shiftRight ring root (Nat.succ p * psi)) psi).Sublist
                  schedule
            at hsub
          rcases List.append_sublist_iff.mp hsub with
            ⟨pre, suf, hschedule, hpre, hsuf⟩
          subst schedule
          have hfirst :
              Or
                (l18HitsSPL ring root C pre = true)
                (L18BuildPrefixAt ring root (Nat.succ p)
                  (runPPrime ring C pre)) := by
            apply ih (C := C) (schedule := pre)
            · omega
            · omega
            · exact hPrefix
            · exact hpre
          cases hfirst with
          | inl hhit =>
              exact
                Or.inl
                  (l18HitsSPL_append_left_true
                    ring root C pre suf hhit)
          | inr hprefix =>
              have hnext :=
                hBlock hn3 hpsi ring root (Nat.succ p)
                  (runPPrime ring C pre) suf hlemma4
                  (by omega) hprefix hsuf
              cases hnext with
              | inl hhit =>
                  exact
                    Or.inl
                      (l18HitsSPL_append_right_true
                        ring root C pre suf hhit)
              | inr hprefixNext =>
                  apply Or.inr
                  simpa only
                    [runPPrime_append, Nat.succ_eq_add_one]
                    using hprefixNext

theorem l18GappedLemma4BuildPhase_of_rows
    (hBlock : L18BuildBlockAdvanceRow)
    {n psi kappa : Nat}
    (hn3 : 3 <= n) (hpsi : 2 <= psi)
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa)
    (schedule : DetSchedule n)
    (hlemma4 : PPL.lemma4_deterministic_core) :
    CDLAt ring root C ->
    L18NoRiskyAt ring root C ->
    (l18BuildWord ring root psi).Sublist schedule ->
    Or
      (l18HitsSPL ring root C schedule = true)
      (SPLAt ring root
        (runPPrime ring C schedule)) := by
  intro hCDL hRisk hsub
  have hstart :
      L18BuildPrefixAt ring root 0 C :=
    l18BuildPrefixAt_zero ring root C hCDL hRisk
  cases hcount : l18BlockCount n psi with
  | zero =>
      have hfull :
          L18BuildPrefixAt ring root
            (l18BlockCount n psi) C := by
        simpa only [hcount] using hstart
      have hS :
          SPLAt ring root C :=
        l18BuildPrefixAt_full_spl ring root C hfull
      exact
        Or.inl
          (l18HitsSPL_of_initial
            ring root C schedule hS)
  | succ count =>
      have hmPos :
          0 < l18BlockCount n psi := by
        omega
      change
        (l18Lemma4Blocks ring root psi
          (l18BlockCount n psi)).Sublist schedule
        at hsub
      have hprogress :=
        l18BuildPositiveBlocks_of_rows
          hBlock hn3 hpsi ring root
          (l18BlockCount n psi)
          C schedule hmPos (Nat.le_refl _)
          hlemma4 hstart hsub
      cases hprogress with
      | inl hhit =>
          exact Or.inl hhit
      | inr hfull =>
          exact
            Or.inr
              (l18BuildPrefixAt_full_spl
                ring root
                (runPPrime ring C schedule)
                hfull)

end PPL.Convergence.L18

#print axioms PPL.Convergence.L18.l18GappedLemma4BuildPhase_of_rows
