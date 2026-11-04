import Leader.PPL.TokenCompletion.HalfPowerDynamics
import Init.Omega

namespace PPL

set_option autoImplicit false
set_option Elab.async false

/-!
# Machine refutation of the old Lemma4HalfPowerDynamics

This file machine-checks the n=4, psi=2 revived-unowned-token witness from
TokenCorrectnessLemma4Dynamics.lean.

The repair relative to the earlier version is deliberately computational:

* every semantic proposition used by an `if` has an explicit Decidable;
* the three larger witness checks use pure Bool mirrors over finite domains,
  rather than asking `decide` to normalize semantic propositions;
* CdTrace is mirrored by an executable recursion, avoiding recursive
  instDecidableAnd plumbing;
* GhostConfig equality uses an explicit four-field extensionality lemma,
  because the structure has no generated theorem named GhostConfig.ext.
-/

/-! ## 1. Small finite Bool quantifiers -/

private def anyFinBool : (n : Nat) -> (Fin n -> Bool) -> Bool
  | 0, _ => false
  | n + 1, p => p 0 || anyFinBool n (fun i => p i.succ)

private theorem anyFinBool_true_iff
    (n : Nat) (p : Fin n -> Bool) :
    anyFinBool n p = true ↔ Exists fun i => p i = true := by
  induction n with
  | zero =>
      simp [anyFinBool]
  | succ n ih =>
      constructor
      · intro h
        cases h0 : p 0 with
        | false =>
            have ht :
                anyFinBool n (fun i : Fin n => p i.succ) = true := by
              simpa [anyFinBool, h0] using h
            obtain ⟨i, hi⟩ :=
              (ih (fun i : Fin n => p i.succ)).1 ht
            exact ⟨i.succ, hi⟩
        | true =>
            exact ⟨0, h0⟩
      · rintro ⟨i, hi⟩
        cases i using Fin.cases with
        | zero =>
            simp [anyFinBool, hi]
        | succ i =>
            have ht :
                anyFinBool n (fun j : Fin n => p j.succ) = true :=
              (ih (fun j : Fin n => p j.succ)).2 ⟨i, hi⟩
            simp [anyFinBool, ht]

private def allFinBool : (n : Nat) -> (Fin n -> Bool) -> Bool
  | 0, _ => true
  | n + 1, p => p 0 && allFinBool n (fun i => p i.succ)

private theorem allFinBool_true_iff
    (n : Nat) (p : Fin n -> Bool) :
    allFinBool n p = true ↔ forall i, p i = true := by
  induction n with
  | zero =>
      simp [allFinBool]
  | succ n ih =>
      constructor
      · intro h
        cases h0 : p 0 with
        | false =>
            simp [allFinBool, h0] at h
        | true =>
            have ht :
                allFinBool n (fun i : Fin n => p i.succ) = true := by
              simpa [allFinBool, h0] using h
            have htail :=
              (ih (fun i : Fin n => p i.succ)).1 ht
            intro i
            cases i using Fin.cases with
            | zero => exact h0
            | succ i => exact htail i
      · intro h
        have h0 : p 0 = true := h 0
        have ht :
            allFinBool n (fun i : Fin n => p i.succ) = true :=
          (ih (fun i : Fin n => p i.succ)).2
            (fun i => h i.succ)
        simp [allFinBool, h0, ht]

/-! ## 2. Executable mirrors of local validity and freshness -/

private def refuteLocalValid {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa)
    (t : TokenData psi) : Prop :=
  let c := decodeOffset psi (tokenCode t)
  let target := tokenTargetCoordinate kind q t
  Or
    (And (0 < c)
      (And (((psi : Nat) : Int) <= target)
        (target <= (((2 * psi - 1 : Nat)) : Int))))
    (And (c < 0)
      (And (1 <= target)
        (target <= (((psi - 1 : Nat)) : Int))))

private def refuteLocalValidB {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa)
    (t : TokenData psi) : Bool :=
  let c := decodeOffset psi (tokenCode t)
  let target := tokenTargetCoordinate kind q t
  (decide (0 < c) &&
      (decide (((psi : Nat) : Int) <= target) &&
        decide (target <= (((2 * psi - 1 : Nat)) : Int)))) ||
    (decide (c < 0) &&
      (decide (1 <= target) &&
        decide (target <= (((psi - 1 : Nat)) : Int))))

private theorem refuteLocalValidB_true_iff
    {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa)
    (t : TokenData psi) :
    refuteLocalValidB kind q t = true ↔
      refuteLocalValid kind q t := by
  unfold refuteLocalValidB refuteLocalValid
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]

private instance instDecidableRefuteLocalValid
    {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa)
    (t : TokenData psi) :
    Decidable (refuteLocalValid kind q t) :=
  decidable_of_iff
    (refuteLocalValidB kind q t = true)
    (refuteLocalValidB_true_iff kind q t)

private noncomputable def refuteInitialOwned
    {n psi kappa : Nat}
    (kind : TokenKind) (C : Config n psi kappa)
    (i : Fin n) : Option (GhostToken n psi) := by
  classical
  exact
    match tokenAt kind (C i) with
    | none => none
    | some t =>
        if refuteLocalValid kind (C i) t then
          some
            { value := t
              lmeta :=
                { id := .initial kind i
                  birthSite := i
                  birthStep := 0
                  moves := 0 } }
        else none

private theorem ghostTokenAt_initial_eq_refute
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (kind : TokenKind) (i : Fin n) :
    ghostTokenAt kind (initialGhost C) i =
      refuteInitialOwned kind C i := by
  cases kind <;> rfl

private def FreshAtFinite {n : Nat}
    (kind : TokenKind) (k : Fin n)
    (m : LineageMeta n) : Prop :=
  match m.id with
  | .initial _ _ => False
  | .born kind' _ =>
      And (kind' = kind) (m.birthSite = k)

private instance instDecidableFreshAtFiniteRefute
    {n : Nat} (kind : TokenKind) (k : Fin n)
    (m : LineageMeta n) :
    Decidable (FreshAtFinite kind k m) := by
  unfold FreshAtFinite
  cases m.id <;> infer_instance

private theorem freshAt_iff_finite
    {n : Nat} (kind : TokenKind) (k : Fin n)
    (m : LineageMeta n) :
    FreshAt kind k m ↔ FreshAtFinite kind k m := by
  unfold FreshAt FreshAtFinite
  cases h : m.id <;> simp [h]

private def freshAtB {n : Nat}
    (kind : TokenKind) (k : Fin n)
    (m : LineageMeta n) : Bool :=
  match m.id with
  | .initial _ _ => false
  | .born kind' _ =>
      decide (kind' = kind) &&
        decide (m.birthSite = k)

private theorem freshAtB_true_iff
    {n : Nat} (kind : TokenKind) (k : Fin n)
    (m : LineageMeta n) :
    freshAtB kind k m = true ↔ FreshAt kind k m := by
  cases h : m.id <;>
    simp [freshAtB, FreshAt, h, Bool.and_eq_true, decide_eq_true_eq]

private instance instDecidableFreshAtRefute
    {n : Nat} (kind : TokenKind) (k : Fin n)
    (m : LineageMeta n) :
    Decidable (FreshAt kind k m) :=
  decidable_of_iff
    (freshAtB kind k m = true)
    (freshAtB_true_iff kind k m)

private def lemma4InWindowB {n : Nat}
    (ring : DirectedRing n) (k : Fin n)
    (psi : Nat) (i : Fin n) : Bool :=
  anyFinBool (2 * psi)
    (fun x : Fin (2 * psi) =>
      decide (i = shiftRight ring k x.val))

private theorem lemma4InWindowB_true_iff
    {n : Nat}
    (ring : DirectedRing n) (k : Fin n)
    (psi : Nat) (i : Fin n) :
    lemma4InWindowB ring k psi i = true ↔
      Lemma4InWindow ring k psi i := by
  unfold lemma4InWindowB Lemma4InWindow
  rw [anyFinBool_true_iff]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, of_decide_eq_true hx⟩
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    simpa only [decide_eq_true_eq] using hx

private instance instDecidableLemma4InWindowRefute
    {n : Nat}
    (ring : DirectedRing n) (k : Fin n)
    (psi : Nat) (i : Fin n) :
    Decidable (Lemma4InWindow ring k psi i) :=
  decidable_of_iff
    (lemma4InWindowB ring k psi i = true)
    (lemma4InWindowB_true_iff ring k psi i)

private def validTokenB
    {n psi kappa : Nat}
    (kind : TokenKind) (C : Config n psi kappa)
    (i : Fin n) : Bool :=
  match tokenAt kind (C i) with
  | none => false
  | some t => refuteLocalValidB kind (C i) t

private theorem validTokenB_true_iff
    {n psi kappa : Nat}
    (kind : TokenKind) (C : Config n psi kappa)
    (i : Fin n) :
    validTokenB kind C i = true ↔ ValidToken kind C i := by
  unfold validTokenB ValidToken
  cases h : tokenAt kind (C i) with
  | none =>
      simp [h]
  | some t =>
      simp only [h]
      simpa [refuteLocalValid] using
        (refuteLocalValidB_true_iff kind (C i) t)

/-! ## 3. Fresh-window Bool mirror and finite decidability -/

private def Lemma4FreshWindowFinite
    {n psi kappa : Nat}
    (ring : DirectedRing n) (k : Fin n)
    (kind : TokenKind) (G : GhostConfig n psi kappa) : Prop :=
  forall i : Fin n,
    Lemma4InWindow ring k psi i ->
      match ghostTokenAt kind G i with
      | none => True
      | some z => FreshAt kind k z.lmeta

private theorem lemma4FreshWindow_iff_finite
    {n psi kappa : Nat}
    (ring : DirectedRing n) (k : Fin n)
    (kind : TokenKind) (G : GhostConfig n psi kappa) :
    Lemma4FreshWindow ring k kind G ↔
      Lemma4FreshWindowFinite ring k kind G := by
  constructor
  · intro h i hin
    cases ho : ghostTokenAt kind G i with
    | none =>
        trivial
    | some z =>
        exact h i z hin ho
  · intro h i z hin ho
    have hi := h i hin
    rw [ho] at hi
    exact hi

private def lemma4FreshWindowB
    {n psi kappa : Nat}
    (ring : DirectedRing n) (k : Fin n)
    (kind : TokenKind) (G : GhostConfig n psi kappa) : Bool :=
  allFinBool n (fun i =>
    if lemma4InWindowB ring k psi i then
      match ghostTokenAt kind G i with
      | none => true
      | some z => freshAtB kind k z.lmeta
    else true)

private theorem lemma4FreshWindowB_true_iff
    {n psi kappa : Nat}
    (ring : DirectedRing n) (k : Fin n)
    (kind : TokenKind) (G : GhostConfig n psi kappa) :
    lemma4FreshWindowB ring k kind G = true ↔
      Lemma4FreshWindow ring k kind G := by
  unfold lemma4FreshWindowB
  rw [allFinBool_true_iff]
  constructor
  · intro hall i z hin ho
    have hwin :
        lemma4InWindowB ring k psi i = true :=
      (lemma4InWindowB_true_iff ring k psi i).2 hin
    have hi := hall i
    rw [hwin] at hi
    rw [ho] at hi
    exact (freshAtB_true_iff kind k z.lmeta).1 hi
  · intro h i
    cases hwin : lemma4InWindowB ring k psi i with
    | false =>
        simp [hwin]
    | true =>
        have hin :
            Lemma4InWindow ring k psi i :=
          (lemma4InWindowB_true_iff ring k psi i).1 hwin
        cases ho : ghostTokenAt kind G i with
        | none =>
            simp [hwin, ho]
        | some z =>
            have hfresh : FreshAt kind k z.lmeta :=
              h i z hin ho
            have hb :
                freshAtB kind k z.lmeta = true :=
              (freshAtB_true_iff kind k z.lmeta).2 hfresh
            simpa [hwin, ho] using hb

private instance instDecidableLemma4FreshWindowFiniteRefute
    {n psi kappa : Nat}
    (ring : DirectedRing n) (k : Fin n)
    (kind : TokenKind) (G : GhostConfig n psi kappa) :
    Decidable (Lemma4FreshWindowFinite ring k kind G) :=
  decidable_of_iff
    (lemma4FreshWindowB ring k kind G = true)
    ((lemma4FreshWindowB_true_iff ring k kind G).trans
      (lemma4FreshWindow_iff_finite ring k kind G))

private instance instDecidableLemma4FreshWindowRefute
    {n psi kappa : Nat}
    (ring : DirectedRing n) (k : Fin n)
    (kind : TokenKind) (G : GhostConfig n psi kappa) :
    Decidable (Lemma4FreshWindow ring k kind G) :=
  decidable_of_iff
    (lemma4FreshWindowB ring k kind G = true)
    (lemma4FreshWindowB_true_iff ring k kind G)

/-! ## 4. Ghost-coverage Bool mirror and finite decidability -/

private def Lemma4GhostCoveredWindowFinite
    {n psi kappa : Nat}
    (ring : DirectedRing n) (k : Fin n)
    (kind : TokenKind) (G : GhostConfig n psi kappa) : Prop :=
  forall i : Fin n,
    Lemma4InWindow ring k psi i ->
      ValidToken kind G.phys i ->
        ghostTokenAt kind G i ≠ none

private theorem lemma4GhostCoveredWindow_iff_finite
    {n psi kappa : Nat}
    (ring : DirectedRing n) (k : Fin n)
    (kind : TokenKind) (G : GhostConfig n psi kappa) :
    Lemma4GhostCoveredWindow ring k kind G ↔
      Lemma4GhostCoveredWindowFinite ring k kind G := by
  constructor
  · intro h i hin hvalid hnone
    obtain ⟨z, hz⟩ := h i hin hvalid
    rw [hnone] at hz
    cases hz
  · intro h i hin hvalid
    cases ho : ghostTokenAt kind G i with
    | none =>
        exact False.elim ((h i hin hvalid) ho)
    | some z =>
        exact ⟨z, rfl⟩

private def lemma4GhostCoveredWindowB
    {n psi kappa : Nat}
    (ring : DirectedRing n) (k : Fin n)
    (kind : TokenKind) (G : GhostConfig n psi kappa) : Bool :=
  allFinBool n (fun i =>
    if lemma4InWindowB ring k psi i then
      if validTokenB kind G.phys i then
        match ghostTokenAt kind G i with
        | none => false
        | some _ => true
      else true
    else true)

private theorem lemma4GhostCoveredWindowB_true_iff
    {n psi kappa : Nat}
    (ring : DirectedRing n) (k : Fin n)
    (kind : TokenKind) (G : GhostConfig n psi kappa) :
    lemma4GhostCoveredWindowB ring k kind G = true ↔
      Lemma4GhostCoveredWindow ring k kind G := by
  unfold lemma4GhostCoveredWindowB
  rw [allFinBool_true_iff]
  constructor
  · intro hall i hin hvalid
    have hwin :
        lemma4InWindowB ring k psi i = true :=
      (lemma4InWindowB_true_iff ring k psi i).2 hin
    have hv :
        validTokenB kind G.phys i = true :=
      (validTokenB_true_iff kind G.phys i).2 hvalid
    have hi := hall i
    rw [hwin, hv] at hi
    cases ho : ghostTokenAt kind G i with
    | none =>
        simp [ho] at hi
    | some z =>
        exact ⟨z, rfl⟩
  · intro h i
    cases hwin : lemma4InWindowB ring k psi i with
    | false =>
        simp [hwin]
    | true =>
        have hin :
            Lemma4InWindow ring k psi i :=
          (lemma4InWindowB_true_iff ring k psi i).1 hwin
        cases hv : validTokenB kind G.phys i with
        | false =>
            simp [hwin, hv]
        | true =>
            have hvalid :
                ValidToken kind G.phys i :=
              (validTokenB_true_iff kind G.phys i).1 hv
            cases ho : ghostTokenAt kind G i with
            | none =>
                obtain ⟨z, hz⟩ := h i hin hvalid
                rw [ho] at hz
                cases hz
            | some z =>
                simp [hwin, hv, ho]

private instance instDecidableLemma4GhostCoveredWindowFiniteRefute
    {n psi kappa : Nat}
    (ring : DirectedRing n) (k : Fin n)
    (kind : TokenKind) (G : GhostConfig n psi kappa) :
    Decidable (Lemma4GhostCoveredWindowFinite ring k kind G) :=
  decidable_of_iff
    (lemma4GhostCoveredWindowB ring k kind G = true)
    ((lemma4GhostCoveredWindowB_true_iff ring k kind G).trans
      (lemma4GhostCoveredWindow_iff_finite ring k kind G))

private instance instDecidableLemma4GhostCoveredWindowRefute
    {n psi kappa : Nat}
    (ring : DirectedRing n) (k : Fin n)
    (kind : TokenKind) (G : GhostConfig n psi kappa) :
    Decidable (Lemma4GhostCoveredWindow ring k kind G) :=
  decidable_of_iff
    (lemma4GhostCoveredWindowB ring k kind G = true)
    (lemma4GhostCoveredWindowB_true_iff ring k kind G)

private def lemma4CoveredFreshWindowB
    {n psi kappa : Nat}
    (ring : DirectedRing n) (k : Fin n)
    (kind : TokenKind) (G : GhostConfig n psi kappa) : Bool :=
  lemma4FreshWindowB ring k kind G &&
    lemma4GhostCoveredWindowB ring k kind G

private theorem lemma4CoveredFreshWindowB_true_iff
    {n psi kappa : Nat}
    (ring : DirectedRing n) (k : Fin n)
    (kind : TokenKind) (G : GhostConfig n psi kappa) :
    lemma4CoveredFreshWindowB ring k kind G = true ↔
      Lemma4CoveredFreshWindow ring k kind G := by
  unfold lemma4CoveredFreshWindowB Lemma4CoveredFreshWindow
  rw [Bool.and_eq_true_iff,
    lemma4FreshWindowB_true_iff,
    lemma4GhostCoveredWindowB_true_iff]

private instance instDecidableLemma4CoveredFreshWindowRefute
    {n psi kappa : Nat}
    (ring : DirectedRing n) (k : Fin n)
    (kind : TokenKind) (G : GhostConfig n psi kappa) :
    Decidable (Lemma4CoveredFreshWindow ring k kind G) :=
  decidable_of_iff
    (lemma4CoveredFreshWindowB ring k kind G = true)
    (lemma4CoveredFreshWindowB_true_iff ring k kind G)

/-! ## 5. Fresh completion Bool mirror -/

private def freshCompletionB
    {n psi : Nat}
    (kind : TokenKind) (k : Fin n)
    (m : LineageMeta n) : Bool :=
  freshAtB kind k m &&
    decide (m.moves = tokenTrajectoryMoves psi)

private theorem freshCompletionB_true_iff
    {n psi : Nat}
    (kind : TokenKind) (k : Fin n)
    (m : LineageMeta n) :
    freshCompletionB (psi := psi) kind k m = true ↔
      FreshCompletion (psi := psi) kind k m := by
  unfold freshCompletionB FreshCompletion
  rw [Bool.and_eq_true_iff]
  constructor
  · rintro ⟨hfresh, hmoves⟩
    exact
      ⟨(freshAtB_true_iff kind k m).1 hfresh,
        of_decide_eq_true hmoves⟩
  · rintro ⟨hfresh, hmoves⟩
    refine
      ⟨(freshAtB_true_iff kind k m).2 hfresh, ?_⟩
    simpa only [decide_eq_true_eq] using hmoves

private instance instDecidableFreshCompletionRefute
    {n psi : Nat}
    (kind : TokenKind) (k : Fin n)
    (m : LineageMeta n) :
    Decidable (FreshCompletion (psi := psi) kind k m) :=
  decidable_of_iff
    (freshCompletionB (psi := psi) kind k m = true)
    (freshCompletionB_true_iff (psi := psi) kind k m)

private def hasFreshCompletionB
    {n psi kappa : Nat}
    (kind : TokenKind) (k : Fin n)
    (G : GhostConfig n psi kappa) : Bool :=
  G.completed.any
    (fun m => freshCompletionB (psi := psi) kind k m)

private theorem hasFreshCompletionB_true_iff
    {n psi kappa : Nat}
    (kind : TokenKind) (k : Fin n)
    (G : GhostConfig n psi kappa) :
    hasFreshCompletionB kind k G = true ↔
      HasFreshCompletion kind k G := by
  unfold hasFreshCompletionB HasFreshCompletion
  rw [List.any_eq_true]
  constructor
  · rintro ⟨m, hm, hb⟩
    exact
      ⟨m, hm,
        (freshCompletionB_true_iff (psi := psi) kind k m).1 hb⟩
  · rintro ⟨m, hm, hfresh⟩
    exact
      ⟨m, hm,
        (freshCompletionB_true_iff (psi := psi) kind k m).2 hfresh⟩

/-! ## 6. Executable C_d and C_d-trace mirrors -/

private def cdPointB
    {n psi kappa : Nat}
    (ring : DirectedRing n) (k : Fin n)
    (kind : TokenKind) (C : Config n psi kappa)
    (x : Fin (2 * psi)) : Bool :=
  let v := shiftRight ring k x.val
  decide
      ((C v).dist.val =
        (x.val + tokenD' psi kind) % (2 * psi)) &&
    decide ((C v).last = false)

private def cdB
    {n psi kappa : Nat}
    (ring : DirectedRing n) (k : Fin n)
    (kind : TokenKind) (C : Config n psi kappa) : Bool :=
  allFinBool (2 * psi)
    (cdPointB ring k kind C)

private theorem cdB_true_iff
    {n psi kappa : Nat}
    (ring : DirectedRing n) (k : Fin n)
    (kind : TokenKind) (C : Config n psi kappa) :
    cdB ring k kind C = true ↔
      Cd ring k kind C := by
  unfold cdB Cd
  rw [allFinBool_true_iff]
  constructor
  · intro hall x
    have hx := hall x
    unfold cdPointB at hx
    have hp := Bool.and_eq_true_iff.mp hx
    dsimp only
    exact
      ⟨of_decide_eq_true hp.1,
        of_decide_eq_true hp.2⟩
  · intro h x
    have hx := h x
    dsimp only at hx
    unfold cdPointB
    apply Bool.and_eq_true_iff.mpr
    constructor
    · simpa only [decide_eq_true_eq] using hx.1
    · simpa only [decide_eq_true_eq] using hx.2

private instance instDecidableCdRefute
    {n psi kappa : Nat}
    (ring : DirectedRing n) (k : Fin n)
    (kind : TokenKind) (C : Config n psi kappa) :
    Decidable (Cd ring k kind C) :=
  decidable_of_iff
    (cdB ring k kind C = true)
    (cdB_true_iff ring k kind C)

private def cdTraceB
    {n psi kappa : Nat} (hpsi : 2 <= psi)
    (ring : DirectedRing n) (k : Fin n)
    (kind : TokenKind) :
    Config n psi kappa -> DetSchedule n -> Bool
  | C, [] =>
      cdB ring k kind C
  | C, e :: es =>
      cdB ring k kind C &&
        cdTraceB hpsi ring k kind
          (PopulationProtocol.step
            (protocol psi kappa) ring C e) es

private theorem cdTraceB_true_iff
    {n psi kappa : Nat} (hpsi : 2 <= psi)
    (ring : DirectedRing n) (k : Fin n)
    (kind : TokenKind)
    (C : Config n psi kappa)
    (s : DetSchedule n) :
    cdTraceB hpsi ring k kind C s = true ↔
      CdTrace hpsi ring k kind C s := by
  induction s generalizing C with
  | nil =>
      simpa [cdTraceB, CdTrace] using
        (cdB_true_iff ring k kind C)
  | cons e es ih =>
      simp only [cdTraceB, CdTrace, Bool.and_eq_true_iff]
      rw [cdB_true_iff, ih]

private instance instDecidableCdTraceRefute
    {n psi kappa : Nat} (hpsi : 2 <= psi)
    (ring : DirectedRing n) (k : Fin n)
    (kind : TokenKind)
    (C : Config n psi kappa)
    (s : DetSchedule n) :
    Decidable (CdTrace hpsi ring k kind C s) :=
  decidable_of_iff
    (cdTraceB hpsi ring k kind C s = true)
    (cdTraceB_true_iff hpsi ring k kind C s)

/-! ## 7. Explicit GhostConfig extensionality -/

private theorem ghostConfig_ext_refute
    {n psi kappa : Nat}
    {G H : GhostConfig n psi kappa}
    (hphys : G.phys = H.phys)
    (hblack : forall i, G.black i = H.black i)
    (hwhite : forall i, G.white i = H.white i)
    (hcompleted : G.completed = H.completed) :
    G = H := by
  cases G with
  | mk gphys gblack gwhite gcompleted =>
      cases H with
      | mk hphys' hblack' hwhite' hcompleted' =>
          dsimp only at hphys hblack hwhite hcompleted
          have hb : gblack = hblack' := funext hblack
          have hw : gwhite = hwhite' := funext hwhite
          cases hphys
          cases hb
          cases hw
          cases hcompleted
          rfl

/-! ## 8. The concrete revived-unowned-token witness -/

private theorem refuteHpsi : 2 <= 2 := by decide

private def refuteRing : DirectedRing 4 :=
  ⟨by decide⟩

private def refuteE0 : Fin 4 :=
  ⟨0, by decide⟩

private def refuteE1 : Fin 4 :=
  ⟨1, by decide⟩

private def refuteE2 : Fin 4 :=
  ⟨2, by decide⟩

private def refuteK : Fin 4 :=
  refuteE0

private def refuteToken : TokenData 2 :=
  ((offsetOneCode 2 refuteHpsi, (0 : Fin 2)),
    (0 : Fin 2))

private def refuteState (i : Fin 4) : State 2 32 :=
  { leader := false
    id := false
    dist :=
      if i.val = 0 then
        (0 : Fin 4)
      else if i.val = 1 then
        (0 : Fin 4)
      else
        ⟨i.val, i.isLt⟩
    last := false
    tokenB :=
      if i.val = 1 then
        some refuteToken
      else
        none
    tokenW := none
    mode := false
    clock := (0 : Fin 33)
    signalR := (0 : Fin 33)
    hits := (0 : Fin 3)
    bullet := (0 : Fin 3)
    shield := false
    signalB := false }

private def refuteC : Config 4 2 32 :=
  refuteState

private def refutePrefix : DetSchedule 4 :=
  [refuteE0]

private def refuteHalf : DetSchedule 4 :=
  [ refuteE0, refuteE1, refuteE2,
    refuteE2, refuteE1, refuteE0,
    refuteE0, refuteE1, refuteE2,
    refuteE2, refuteE1, refuteE0 ]

private def refuteInitialExplicit : GhostConfig 4 2 32 :=
  { phys := refuteC
    black := fun _ => none
    white := fun _ => none
    completed := [] }

private theorem refute_initial_black_none
    (i : Fin 4) :
    ghostTokenAt .black (initialGhost refuteC) i = none := by
  rw [ghostTokenAt_initial_eq_refute]
  by_cases hi : i.val = 1
  · have hie : i = refuteE1 := by
      apply Fin.ext
      simpa [refuteE1] using hi
    subst i
    have hb :
        refuteLocalValidB .black
            (refuteC refuteE1) refuteToken = false := by
      decide
    have hinvalid :
        ¬ refuteLocalValid .black
            (refuteC refuteE1) refuteToken := by
      intro hvalid
      have ht :
          refuteLocalValidB .black
              (refuteC refuteE1) refuteToken = true :=
        (refuteLocalValidB_true_iff
          .black (refuteC refuteE1) refuteToken).2 hvalid
      rw [hb] at ht
      cases ht
    have htok :
        tokenAt .black (refuteC refuteE1) =
          some refuteToken := by
      simp [refuteC, refuteState, refuteE1, tokenAt]
    unfold refuteInitialOwned
    rw [htok]
    exact if_neg hinvalid
  · have htok :
        tokenAt .black (refuteC i) = none := by
      simp [refuteC, refuteState, tokenAt, hi]
    unfold refuteInitialOwned
    rw [htok]

private theorem refute_initial_white_none
    (i : Fin 4) :
    ghostTokenAt .white (initialGhost refuteC) i = none := by
  rw [ghostTokenAt_initial_eq_refute]
  have htok :
      tokenAt .white (refuteC i) = none := by
    simp [refuteC, refuteState, tokenAt]
  unfold refuteInitialOwned
  rw [htok]

private theorem refute_initialGhost_eq :
    initialGhost refuteC = refuteInitialExplicit := by
  apply ghostConfig_ext_refute
  · rfl
  · intro i
    simpa [ghostTokenAt, refuteInitialExplicit] using
      refute_initial_black_none i
  · intro i
    simpa [ghostTokenAt, refuteInitialExplicit] using
      refute_initial_white_none i
  · rfl

private def refuteMid : GhostConfig 4 2 32 :=
  ghostRun refuteHpsi refuteRing 0
    refuteInitialExplicit refutePrefix

private def refuteEnd : GhostConfig 4 2 32 :=
  ghostRun refuteHpsi refuteRing
    refutePrefix.length refuteMid refuteHalf

private theorem refute_mid_is_actual_prefix :
    refuteMid =
      ghostRun refuteHpsi refuteRing 0
        (initialGhost refuteC) refutePrefix := by
  unfold refuteMid
  rw [refute_initialGhost_eq]

private theorem refute_half_is_lemma4HalfWord :
    lemma4HalfWord refuteRing refuteK 2 =
      refuteHalf := by
  set_option maxHeartbeats 4000000 in
    decide

private theorem refute_mid_fresh :
    Lemma4FreshWindow refuteRing refuteK .black
      refuteMid := by
  have hb :
      lemma4FreshWindowB
          refuteRing refuteK .black refuteMid = true := by
    set_option maxHeartbeats 4000000 in
      decide
  exact
    (lemma4FreshWindowB_true_iff
      refuteRing refuteK .black refuteMid).1 hb

private theorem refute_secondHalf_cd :
    CdTrace refuteHpsi refuteRing refuteK .black
      refuteMid.phys refuteHalf := by
  have hb :
      cdTraceB refuteHpsi refuteRing refuteK .black
          refuteMid.phys refuteHalf = true := by
    set_option maxHeartbeats 8000000 in
      decide
  exact
    (cdTraceB_true_iff
      refuteHpsi refuteRing refuteK .black
      refuteMid.phys refuteHalf).1 hb

private theorem refute_end_no_completionB :
    hasFreshCompletionB .black refuteK refuteEnd =
      false := by
  set_option maxHeartbeats 8000000 in
    decide

private theorem refute_end_no_completion :
    ¬ HasFreshCompletion .black refuteK refuteEnd := by
  intro h
  have hb :
      hasFreshCompletionB .black refuteK refuteEnd =
        true :=
    (hasFreshCompletionB_true_iff
      .black refuteK refuteEnd).2 h
  rw [refute_end_no_completionB] at hb
  cases hb

private theorem refute_half_sublist :
    (lemma4HalfWord refuteRing refuteK 2).Sublist
      refuteHalf := by
  rw [refute_half_is_lemma4HalfWord]
  exact List.Sublist.refl _

/-!
The old second conjunct accepts refuteMid because it asks only
Lemma4FreshWindow.  The selected-color ghost map is fresh/vacuous, but the
physical black token revived at u1 is not ghost-covered.  The exact second
half remains in C_0 and does not complete a fresh lineage.
-/
theorem lemma4HalfPowerDynamics_false :
    ¬ Lemma4HalfPowerDynamics := by
  intro hdyn
  have hsecond :=
    (hdyn
      (n := 4) (psi := 2) (kappa := 32)
      refuteHpsi refuteRing refuteK .black).2
  have hcompletion :
      HasFreshCompletion .black refuteK refuteEnd := by
    have h :=
      hsecond
        refuteC
        refutePrefix
        refuteMid
        refuteHalf
        refute_mid_is_actual_prefix
        refute_mid_fresh
        refute_secondHalf_cd
        refute_half_sublist
    simpa [refuteEnd] using h
  exact refute_end_no_completion hcompletion

/-! ## 9. The corrected midpoint premise is nonempty -/

private def coveredWitnessState
    (i : Fin 4) : State 2 32 :=
  { leader := false
    id := false
    dist := ⟨i.val, by omega⟩
    last := false
    tokenB := none
    tokenW := none
    mode := false
    clock := (0 : Fin 33)
    signalR := (0 : Fin 33)
    hits := (0 : Fin 3)
    bullet := (0 : Fin 3)
    shield := false
    signalB := false }

private def coveredWitnessC : Config 4 2 32 :=
  coveredWitnessState

private def coveredInitialExplicit : GhostConfig 4 2 32 :=
  { phys := coveredWitnessC
    black := fun _ => none
    white := fun _ => none
    completed := [] }

private theorem covered_initial_black_none
    (i : Fin 4) :
    ghostTokenAt .black
        (initialGhost coveredWitnessC) i = none := by
  rw [ghostTokenAt_initial_eq_refute]
  have htok :
      tokenAt .black (coveredWitnessC i) = none := by
    simp [coveredWitnessC, coveredWitnessState, tokenAt]
  unfold refuteInitialOwned
  rw [htok]

private theorem covered_initial_white_none
    (i : Fin 4) :
    ghostTokenAt .white
        (initialGhost coveredWitnessC) i = none := by
  rw [ghostTokenAt_initial_eq_refute]
  have htok :
      tokenAt .white (coveredWitnessC i) = none := by
    simp [coveredWitnessC, coveredWitnessState, tokenAt]
  unfold refuteInitialOwned
  rw [htok]

private theorem covered_initialGhost_eq :
    initialGhost coveredWitnessC =
      coveredInitialExplicit := by
  apply ghostConfig_ext_refute
  · rfl
  · intro i
    simpa [ghostTokenAt, coveredInitialExplicit] using
      covered_initial_black_none i
  · intro i
    simpa [ghostTokenAt, coveredInitialExplicit] using
      covered_initial_white_none i
  · rfl

/--
The corrected midpoint predicate is satisfiable already at the initial ghost
of the exact configuration used by lemma4_premises_nonvacuous.
-/
theorem lemma4Witness_initial_covered :
    Lemma4CoveredFreshWindow
      refuteRing refuteK .black
      (initialGhost coveredWitnessC) := by
  rw [covered_initialGhost_eq]
  have hb :
      lemma4CoveredFreshWindowB
          refuteRing refuteK .black
          coveredInitialExplicit = true := by
    set_option maxHeartbeats 4000000 in
      decide
  exact
    (lemma4CoveredFreshWindowB_true_iff
      refuteRing refuteK .black
      coveredInitialExplicit).1 hb

end PPL

#print axioms PPL.lemma4HalfPowerDynamics_false
#print axioms PPL.lemma4Witness_initial_covered
