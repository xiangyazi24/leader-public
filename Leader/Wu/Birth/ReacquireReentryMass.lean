import Leader.Wu.Birth.IncreaseOrCapReacquireEvent

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace BirthB1ReacquireReentryMass

open PPLL PPLLRepair PPLLResearchFormulation
  PPLLExpiringComparisonRepair
open FiniteUniformStoppingTree

variable {n psi kappa tau : Nat}

abbrev FC (n psi kappa tau : Nat) :=
  BirthPhaseWait2BlockProgress.FC n psi kappa tau

abbrev reentryHorizon (n : Nat) : Nat := 2 * n
abbrev local3Horizon (n : Nat) : Nat := 4 * n

/-- Endpoint after a literal original-scheduler prefix. -/
def prefixEndpoint
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n)
    (C : FC n psi kappa tau) (u : List (Fin n)) :
    FC n psi kappa tau :=
  BirthPhaseGenericRenewal.rawEndpoint
    (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring) C u

/-- Width two has requested length six, hence B4's physical block splits as
    `2*n + 4*n`. -/
theorem L_eq_reentry_add_local3 (n : Nat) :
    BirthPhaseWait2BlockProgress.L n =
      reentryHorizon n + local3Horizon n := by
  change
    n * BirthWaitClockMass.DirtyMass.requestedLength 2 =
      2 * n + 4 * n
  rw [show BirthWaitClockMass.DirtyMass.requestedLength 2 = 6 by decide]
  omega

/-- The literal prefix event: by time `2*n`, either a cap has already
    occurred or the endpoint is Local3 at the tracked anchor. -/
def ReentryOrTarget
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (pre : List (Fin n)) : Prop :=
  BirthPhaseWait2BlockProgress.target
      hpsi h2 kappa ring C pre = true \/
    BirthShortDoneTerminalPassiveLocal3Rotation.LocalLine3At
      hpsi hn ring anchor
        (prefixEndpoint hpsi h2 ring C pre)

noncomputable def ReentryOrTargetBit
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (pre : List (Fin n)) : Nat :=
  @ite Nat
    (ReentryOrTarget hpsi h2 hn kappa tau ring anchor C pre)
    (Classical.propDecidable _) 1 0

/-- The requested `2*n,1/8` mass leaf, stated on the original scheduler words. -/
def ReacquireReentryMass
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n) : Prop :=
  forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Reacquire
        hpsi h2 hn kappa tau ring anchor C ->
      n ^ reentryHorizon n <=
        8 * FixedSpanRenewalPayload.wordSum n (reentryHorizon n)
          (ReentryOrTargetBit
            hpsi h2 hn kappa tau ring anchor C)

/-- Missing semantic bridge on current main.  The Local3 sixteenth counts a
    stopped event with arbitrary trailing letters; this says that every such
    counted suffix is nevertheless a final B3 `Resolves` word relative to the
    original Reacquire start. -/
def Local3SuffixResolvesBridge
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n) : Prop :=
  forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Reacquire
        hpsi h2 hn kappa tau ring anchor C ->
    forall pre : List (Fin n),
      pre.length = reentryHorizon n ->
      let D := prefixEndpoint hpsi h2 ring C pre
      BirthShortDoneTerminalPassiveLocal3Rotation.LocalLine3At
          hpsi hn ring anchor D ->
        forall post : List (Fin n),
          post.length = local3Horizon n ->
          BirthShortDoneTerminalPassiveLocal3Rotation.actualEventBitAt
              h2 hn kappa tau ring anchor D post = 1 ->
            BirthPhaseB3ReacquireEvent.Resolves
              hpsi h2 kappa ring anchor C (pre ++ post)

/-- The genuinely composable prefix event.  Its Local3 arm records exactly the
    continuation property that is absent from the current interfaces. -/
def ReentryReady
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (pre : List (Fin n)) : Prop :=
  BirthPhaseWait2BlockProgress.target
      hpsi h2 kappa ring C pre = true \/
    let D := prefixEndpoint hpsi h2 ring C pre
    BirthShortDoneTerminalPassiveLocal3Rotation.LocalLine3At
        hpsi hn ring anchor D /\
      forall post : List (Fin n),
        post.length = local3Horizon n ->
        BirthShortDoneTerminalPassiveLocal3Rotation.actualEventBitAt
            h2 hn kappa tau ring anchor D post = 1 ->
          BirthPhaseB3ReacquireEvent.Resolves
            hpsi h2 kappa ring anchor C (pre ++ post)

noncomputable def ReentryReadyBit
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (pre : List (Fin n)) : Nat :=
  @ite Nat
    (ReentryReady hpsi h2 hn kappa tau ring anchor C pre)
    (Classical.propDecidable _) 1 0

def ReacquireReadyMass
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n) : Prop :=
  forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Reacquire
        hpsi h2 hn kappa tau ring anchor C ->
      n ^ reentryHorizon n <=
        8 * FixedSpanRenewalPayload.wordSum n (reentryHorizon n)
          (ReentryReadyBit
            hpsi h2 hn kappa tau ring anchor C)

private theorem wordSum_congr_length
    {n T : Nat} (f g : List (Fin n) -> Nat)
    (h : forall u : List (Fin n), u.length = T -> f u = g u) :
    FixedSpanRenewalPayload.wordSum n T f =
      FixedSpanRenewalPayload.wordSum n T g := by
  rw [<- FixedSpanRenewalPayload.rawWord_sum n T f,
    <- FixedSpanRenewalPayload.rawWord_sum n T g]
  apply FiniteUniformStoppingTree.ofFn_sum_eq
  intro i
  exact h _ (FixedSpanRenewalPayload.rawWord_length n T i)

private theorem wordSum_mono_length
    {n T : Nat} (f g : List (Fin n) -> Nat)
    (h : forall u : List (Fin n), u.length = T -> f u <= g u) :
    FixedSpanRenewalPayload.wordSum n T f <=
      FixedSpanRenewalPayload.wordSum n T g := by
  rw [<- FixedSpanRenewalPayload.rawWord_sum n T f,
    <- FixedSpanRenewalPayload.rawWord_sum n T g]
  apply FiniteUniformStoppingTree.ofFn_sum_le
  intro i
  exact h _ (FixedSpanRenewalPayload.rawWord_length n T i)

private theorem wordSum_one (n T : Nat) :
    FixedSpanRenewalPayload.wordSum n T (fun _ => 1) = n ^ T := by
  rw [<- FixedSpanRenewalPayload.rawWord_sum n T (fun _ => 1)]
  simpa only [FiniteUniformStoppingTree.ofFn_sum_const, Nat.mul_one]

private theorem wordSum_mul_left
    (n T c : Nat) (f : List (Fin n) -> Nat) :
    FixedSpanRenewalPayload.wordSum n T (fun u => c * f u) =
      c * FixedSpanRenewalPayload.wordSum n T f := by
  rw [<- FixedSpanRenewalPayload.rawWord_sum n T (fun u => c * f u),
    <- FixedSpanRenewalPayload.rawWord_sum n T f]
  exact FiniteUniformStoppingTree.ofFn_sum_mul_left c _

private theorem wordSum_mul_right
    (n T c : Nat) (f : List (Fin n) -> Nat) :
    FixedSpanRenewalPayload.wordSum n T (fun u => f u * c) =
      FixedSpanRenewalPayload.wordSum n T f * c := by
  calc
    FixedSpanRenewalPayload.wordSum n T (fun u => f u * c) =
        FixedSpanRenewalPayload.wordSum n T (fun u => c * f u) := by
      apply wordSum_congr_length
      intro u _
      exact Nat.mul_comm _ _
    _ = c * FixedSpanRenewalPayload.wordSum n T f :=
      wordSum_mul_left n T c f
    _ = FixedSpanRenewalPayload.wordSum n T f * c :=
      Nat.mul_comm _ _

/-- Exact product enumeration on literal original scheduler words. -/
private theorem wordSum_horizon_add
    (n T U : Nat) (f : List (Fin n) -> Nat) :
    FixedSpanRenewalPayload.wordSum n (T + U) f =
      FixedSpanRenewalPayload.wordSum n T
        (fun u => FixedSpanRenewalPayload.wordSum n U
          (fun v => f (u ++ v))) := by
  induction T generalizing f with
  | zero =>
      simp [FixedSpanRenewalPayload.wordSum, allSchedules]
  | succ T ih =>
      rw [Nat.succ_add]
      change
        FixedSpanRenewalPayload.wordSum n (T + U + 1) f =
          FixedSpanRenewalPayload.wordSum n (T + 1)
            (fun u => FixedSpanRenewalPayload.wordSum n U
              (fun v => f (u ++ v)))
      rw [FixedSpanRenewalPayload.wordSum_succ,
        FixedSpanRenewalPayload.wordSum_succ]
      apply FiniteUniformStoppingTree.ofFn_sum_eq
      intro e
      simpa only [List.cons_append] using
        ih (f := fun w => f (e :: w))

private theorem firstCapWithin_append
    (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (u v : List (Fin n))
    (hcap : BirthPhaseWait2BlockProgress.FirstCapWithin
      hpsi h2 kappa ring C u) :
    BirthPhaseWait2BlockProgress.FirstCapWithin
      hpsi h2 kappa ring C (u ++ v) := by
  rcases hcap with ⟨pre, e, post, hword, hrow⟩
  refine ⟨pre, e, post ++ v, ?_, hrow⟩
  rw [hword]
  simp only [List.append_assoc, List.cons_append]

private theorem target_true_append
    (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (u v : List (Fin n))
    (ht : BirthPhaseWait2BlockProgress.target
      hpsi h2 kappa ring C u = true) :
    BirthPhaseWait2BlockProgress.target
      hpsi h2 kappa ring C (u ++ v) = true := by
  apply (BirthPhaseWait2BlockProgress.target_true_iff
    hpsi h2 kappa ring C (u ++ v)).2
  exact firstCapWithin_append hpsi h2 kappa ring C u v
    ((BirthPhaseWait2BlockProgress.target_true_iff
      hpsi h2 kappa ring C u).1 ht)

private theorem actualEventBitAt_zero_of_ne_one
    (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (u : List (Fin n))
    (h : BirthShortDoneTerminalPassiveLocal3Rotation.actualEventBitAt
      h2 hn kappa tau ring anchor C u ≠ 1) :
    BirthShortDoneTerminalPassiveLocal3Rotation.actualEventBitAt
      h2 hn kappa tau ring anchor C u = 0 := by
  classical
  unfold BirthShortDoneTerminalPassiveLocal3Rotation.actualEventBitAt at h ⊢
  unfold BirthShortDoneTerminalPassiveLocal3Mass.actualEventBit at h ⊢
  split <;> simp_all

private theorem reacquireSuccessBit_one
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (kappa : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (u : List (Fin n))
    (hlen : u.length = BirthPhaseWait2BlockProgress.L n)
    (hres : BirthPhaseB3ReacquireEvent.Resolves
      hpsi h2 kappa ring anchor C u) :
    BirthPhaseB3ReacquireEvent.ReacquireSuccessBit
      hpsi h2 kappa ring anchor C u = 1 := by
  classical
  simp [BirthPhaseB3ReacquireEvent.ReacquireSuccessBit,
    BirthPhaseB3ReacquireEvent.ReacquireSuccess, hlen, hres]

/-- The plain prefix mass becomes the composable prefix mass exactly when the
    missing Local3 continuation bridge is supplied. -/
theorem reacquireReadyMass_of_reentryMass
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (hmass : ReacquireReentryMass
      hpsi h2 hn kappa tau ring anchor)
    (hbridge : Local3SuffixResolvesBridge
      hpsi h2 hn kappa tau ring anchor) :
    ReacquireReadyMass hpsi h2 hn kappa tau ring anchor := by
  unfold ReacquireReentryMass at hmass
  unfold Local3SuffixResolvesBridge at hbridge
  unfold ReacquireReadyMass
  intro C hR
  have hp := hmass C hR
  apply Nat.le_trans hp
  apply Nat.mul_le_mul_left 8
  apply wordSum_mono_length
  intro pre hpre
  by_cases hplain :
      ReentryOrTarget hpsi h2 hn kappa tau ring anchor C pre
  · have hready :
        ReentryReady hpsi h2 hn kappa tau ring anchor C pre := by
      unfold ReentryOrTarget at hplain
      unfold ReentryReady
      rcases hplain with ht | hline
      · exact Or.inl ht
      · refine Or.inr ?_
        dsimp only
        refine ⟨hline, ?_⟩
        intro post hpost hbit
        have hb := hbridge C hR pre hpre
        dsimp only at hb
        exact hb hline post hpost hbit
    simp [ReentryOrTargetBit, ReentryReadyBit, hplain, hready]
  · simp [ReentryOrTargetBit, hplain]

private theorem suffix_success_mass_of_target
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (kappa : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (pre : List (Fin n))
    (hpre : pre.length = reentryHorizon n)
    (ht : BirthPhaseWait2BlockProgress.target
      hpsi h2 kappa ring C pre = true) :
    n ^ local3Horizon n <=
      16 * FixedSpanRenewalPayload.wordSum n (local3Horizon n)
        (fun post => BirthPhaseB3ReacquireEvent.ReacquireSuccessBit
          hpsi h2 kappa ring anchor C (pre ++ post)) := by
  have hall :
      FixedSpanRenewalPayload.wordSum n (local3Horizon n)
          (fun post => BirthPhaseB3ReacquireEvent.ReacquireSuccessBit
            hpsi h2 kappa ring anchor C (pre ++ post)) =
        n ^ local3Horizon n := by
    calc
      _ = FixedSpanRenewalPayload.wordSum n (local3Horizon n)
          (fun _ => 1) := by
        apply wordSum_congr_length
        intro post hpost
        apply reacquireSuccessBit_one hpsi h2 kappa ring anchor C
        · calc
            (pre ++ post).length =
                reentryHorizon n + local3Horizon n := by
              simp only [List.length_append, hpre, hpost]
            _ = BirthPhaseWait2BlockProgress.L n :=
              (L_eq_reentry_add_local3 n).symm
        · exact Or.inl
            (target_true_append hpsi h2 kappa ring C pre post ht)
      _ = n ^ local3Horizon n := wordSum_one n (local3Horizon n)
  rw [hall]
  have hnum : 1 <= 16 := by decide
  simpa using Nat.mul_le_mul_right (n ^ local3Horizon n) hnum

private theorem suffix_success_mass_of_local3
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (pre : List (Fin n))
    (hpre : pre.length = reentryHorizon n)
    (hline : BirthShortDoneTerminalPassiveLocal3Rotation.LocalLine3At
      hpsi hn ring anchor (prefixEndpoint hpsi h2 ring C pre))
    (hcont : forall post : List (Fin n),
      post.length = local3Horizon n ->
      BirthShortDoneTerminalPassiveLocal3Rotation.actualEventBitAt
          h2 hn kappa tau ring anchor
            (prefixEndpoint hpsi h2 ring C pre) post = 1 ->
        BirthPhaseB3ReacquireEvent.Resolves
          hpsi h2 kappa ring anchor C (pre ++ post)) :
    n ^ local3Horizon n <=
      16 * FixedSpanRenewalPayload.wordSum n (local3Horizon n)
        (fun post => BirthPhaseB3ReacquireEvent.ReacquireSuccessBit
          hpsi h2 kappa ring anchor C (pre ++ post)) := by
  have hlocal :=
    BirthShortDoneTerminalPassiveLocal3Rotation.local3_entry_or_cap_sixteenth_at
      h2 hn kappa tau ring anchor
        (prefixEndpoint hpsi h2 ring C pre) hline
  have hcount :
      BirthShortDoneTerminalPassiveLocal3Rotation.actualEventCountAt
          h2 hn kappa tau ring anchor
            (prefixEndpoint hpsi h2 ring C pre) (local3Horizon n) <=
        FixedSpanRenewalPayload.wordSum n (local3Horizon n)
          (fun post => BirthPhaseB3ReacquireEvent.ReacquireSuccessBit
            hpsi h2 kappa ring anchor C (pre ++ post)) := by
    unfold BirthShortDoneTerminalPassiveLocal3Rotation.actualEventCountAt
    apply wordSum_mono_length
    intro post hpost
    by_cases hone :
        BirthShortDoneTerminalPassiveLocal3Rotation.actualEventBitAt
          h2 hn kappa tau ring anchor
            (prefixEndpoint hpsi h2 ring C pre) post = 1
    · have hres := hcont post hpost hone
      have hlen : (pre ++ post).length =
          BirthPhaseWait2BlockProgress.L n := by
        calc
          (pre ++ post).length =
              reentryHorizon n + local3Horizon n := by
            simp only [List.length_append, hpre, hpost]
          _ = BirthPhaseWait2BlockProgress.L n :=
            (L_eq_reentry_add_local3 n).symm
      have hs := reacquireSuccessBit_one
        hpsi h2 kappa ring anchor C (pre ++ post) hlen hres
      rw [hone, hs]
      exact Nat.le_refl _
    · have hzero := actualEventBitAt_zero_of_ne_one
        h2 hn kappa tau ring anchor
          (prefixEndpoint hpsi h2 ring C pre) post hone
      rw [hzero]
      exact Nat.zero_le _
  exact Nat.le_trans hlocal (Nat.mul_le_mul_left 16 hcount)

/-- Pure finite-word composition: `1/8 * 1/16 = 1/128`, with the exact
    `2*n | 4*n` split of the original scheduler word. -/
theorem reacquireReadyMass_composes
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (hmass : ReacquireReadyMass
      hpsi h2 hn kappa tau ring anchor) :
    BirthPhaseB3ReacquireEvent.ReacquireSuccessMass
      hpsi h2 hn kappa tau ring anchor := by
  unfold ReacquireReadyMass at hmass
  unfold BirthPhaseB3ReacquireEvent.ReacquireSuccessMass
  intro C hR
  have hp := hmass C hR
  have hsum :
      FixedSpanRenewalPayload.wordSum n (reentryHorizon n)
          (ReentryReadyBit hpsi h2 hn kappa tau ring anchor C) *
          n ^ local3Horizon n <=
        16 * FixedSpanRenewalPayload.wordSum n (reentryHorizon n)
          (fun pre => FixedSpanRenewalPayload.wordSum n (local3Horizon n)
            (fun post => BirthPhaseB3ReacquireEvent.ReacquireSuccessBit
              hpsi h2 kappa ring anchor C (pre ++ post))) := by
    calc
      _ = FixedSpanRenewalPayload.wordSum n (reentryHorizon n)
          (fun pre =>
            ReentryReadyBit hpsi h2 hn kappa tau ring anchor C pre *
              n ^ local3Horizon n) :=
        (wordSum_mul_right n (reentryHorizon n)
          (n ^ local3Horizon n)
          (ReentryReadyBit hpsi h2 hn kappa tau ring anchor C)).symm
      _ <= FixedSpanRenewalPayload.wordSum n (reentryHorizon n)
          (fun pre =>
            16 * FixedSpanRenewalPayload.wordSum n (local3Horizon n)
              (fun post => BirthPhaseB3ReacquireEvent.ReacquireSuccessBit
                hpsi h2 kappa ring anchor C (pre ++ post))) := by
        apply wordSum_mono_length
        intro pre hpre
        by_cases hready :
            ReentryReady hpsi h2 hn kappa tau ring anchor C pre
        · have hbit :
              ReentryReadyBit hpsi h2 hn kappa tau ring anchor C pre = 1 := by
            simp [ReentryReadyBit, hready]
          rw [hbit, Nat.one_mul]
          unfold ReentryReady at hready
          rcases hready with ht | hlocal
          · exact suffix_success_mass_of_target
              hpsi h2 kappa ring anchor C pre hpre ht
          · dsimp only at hlocal
            exact suffix_success_mass_of_local3
              hpsi h2 hn kappa tau ring anchor C pre hpre
                hlocal.1 hlocal.2
        · simp [ReentryReadyBit, hready]
      _ = 16 * FixedSpanRenewalPayload.wordSum n (reentryHorizon n)
          (fun pre => FixedSpanRenewalPayload.wordSum n (local3Horizon n)
            (fun post => BirthPhaseB3ReacquireEvent.ReacquireSuccessBit
              hpsi h2 kappa ring anchor C (pre ++ post))) :=
        wordSum_mul_left n (reentryHorizon n) 16 _
  have hpScaled := Nat.mul_le_mul_right (n ^ local3Horizon n) hp
  have hsScaled := Nat.mul_le_mul_left 8 hsum
  have hcore :
      n ^ reentryHorizon n * n ^ local3Horizon n <=
        128 * FixedSpanRenewalPayload.wordSum n (reentryHorizon n)
          (fun pre => FixedSpanRenewalPayload.wordSum n (local3Horizon n)
            (fun post => BirthPhaseB3ReacquireEvent.ReacquireSuccessBit
              hpsi h2 kappa ring anchor C (pre ++ post))) := by
    calc
      _ <=
          (8 * FixedSpanRenewalPayload.wordSum n (reentryHorizon n)
            (ReentryReadyBit hpsi h2 hn kappa tau ring anchor C)) *
            n ^ local3Horizon n := hpScaled
      _ = 8 *
          (FixedSpanRenewalPayload.wordSum n (reentryHorizon n)
            (ReentryReadyBit hpsi h2 hn kappa tau ring anchor C) *
              n ^ local3Horizon n) := by
        ac_rfl
      _ <= 8 *
          (16 * FixedSpanRenewalPayload.wordSum n (reentryHorizon n)
            (fun pre => FixedSpanRenewalPayload.wordSum n (local3Horizon n)
              (fun post => BirthPhaseB3ReacquireEvent.ReacquireSuccessBit
                hpsi h2 kappa ring anchor C (pre ++ post)))) := hsScaled
      _ = 128 * FixedSpanRenewalPayload.wordSum n (reentryHorizon n)
          (fun pre => FixedSpanRenewalPayload.wordSum n (local3Horizon n)
            (fun post => BirthPhaseB3ReacquireEvent.ReacquireSuccessBit
              hpsi h2 kappa ring anchor C (pre ++ post))) := by
        rw [<- Nat.mul_assoc]
  have hfull :
      FixedSpanRenewalPayload.wordSum n
          (BirthPhaseWait2BlockProgress.L n)
          (fun u => BirthPhaseB3ReacquireEvent.ReacquireSuccessBit
            hpsi h2 kappa ring anchor C u) =
        FixedSpanRenewalPayload.wordSum n (reentryHorizon n)
          (fun pre => FixedSpanRenewalPayload.wordSum n (local3Horizon n)
            (fun post => BirthPhaseB3ReacquireEvent.ReacquireSuccessBit
              hpsi h2 kappa ring anchor C (pre ++ post))) := by
    rw [L_eq_reentry_add_local3 n]
    exact wordSum_horizon_add n (reentryHorizon n) (local3Horizon n) _
  calc
    n ^ BirthPhaseWait2BlockProgress.L n =
        n ^ (reentryHorizon n + local3Horizon n) := by
      rw [L_eq_reentry_add_local3 n]
    _ = n ^ reentryHorizon n * n ^ local3Horizon n := by
      rw [Nat.pow_add]
    _ <= 128 * FixedSpanRenewalPayload.wordSum n (reentryHorizon n)
        (fun pre => FixedSpanRenewalPayload.wordSum n (local3Horizon n)
          (fun post => BirthPhaseB3ReacquireEvent.ReacquireSuccessBit
            hpsi h2 kappa ring anchor C (pre ++ post))) := hcore
    _ = BirthPhaseWait2BlockProgress.Q *
        FixedSpanRenewalPayload.wordSum n
          (BirthPhaseWait2BlockProgress.L n)
          (fun u => BirthPhaseB3ReacquireEvent.ReacquireSuccessBit
            hpsi h2 kappa ring anchor C u) := by
      change
        128 * FixedSpanRenewalPayload.wordSum n (reentryHorizon n)
            (fun pre => FixedSpanRenewalPayload.wordSum n (local3Horizon n)
              (fun post => BirthPhaseB3ReacquireEvent.ReacquireSuccessBit
                hpsi h2 kappa ring anchor C (pre ++ post))) =
          128 * FixedSpanRenewalPayload.wordSum n
            (BirthPhaseWait2BlockProgress.L n)
            (fun u => BirthPhaseB3ReacquireEvent.ReacquireSuccessBit
              hpsi h2 kappa ring anchor C u)
      rw [hfull]

/-- Exact statement of the intended composition, with the continuation premise that
    current main actually needs. -/
theorem reacquireReentryMass_composes
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (hmass : ReacquireReentryMass
      hpsi h2 hn kappa tau ring anchor)
    (hbridge : Local3SuffixResolvesBridge
      hpsi h2 hn kappa tau ring anchor) :
    BirthPhaseB3ReacquireEvent.ReacquireSuccessMass
      hpsi h2 hn kappa tau ring anchor := by
  apply reacquireReadyMass_composes
    hpsi h2 hn kappa tau ring anchor
  exact reacquireReadyMass_of_reentryMass
    hpsi h2 hn kappa tau ring anchor hmass hbridge

/-! ## Two-phase fallback interface -/

/-- Candidate Reacquire macro-block.  This is the quadratic scale demanded by
    the moving-front census; it is deliberately a new leaf, not claimed proved. -/
abbrev fallbackReacquireL (n : Nat) : Nat := 16 * n * n
abbrev fallbackReacquireQ : Nat := 8

/-- Reacquire-phase success is phase exit, not rank drop: cap, or return to the
    ordinary Carrier. -/
def FallbackReacquireExit
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (u : List (Fin n)) : Prop :=
  BirthPhaseWait2BlockProgress.target
      hpsi h2 kappa ring C u = true \/
    BirthPhaseWait2BlockProgress.Carrier
      hpsi h2 hn ring anchor
        (prefixEndpoint hpsi h2 ring C u)

noncomputable def fallbackReacquireExitBit
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (u : List (Fin n)) : Nat :=
  @ite Nat
    (FallbackReacquireExit
      hpsi h2 hn kappa tau ring anchor C u)
    (Classical.propDecidable _) 1 0

/-- B4-R closure: target-free quadratic blocks stay in the two-phase active
    union. -/
def FallbackReacquireClosed
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n) : Prop :=
  forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Reacquire
        hpsi h2 hn kappa tau ring anchor C ->
    forall u : List (Fin n), u.length = fallbackReacquireL n ->
      BirthPhaseWait2BlockProgress.target
          hpsi h2 kappa ring C u = false ->
        BirthPhaseWait2BlockProgress.Allowed
          hpsi h2 hn kappa tau ring anchor
            (prefixEndpoint hpsi h2 ring C u)

/-- B4-R monotonicity: a Reacquire repair block may consume time, but may not
    increase the cap-deficit rank when it misses the target. -/
def FallbackReacquireMono
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n) : Prop :=
  forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Reacquire
        hpsi h2 hn kappa tau ring anchor C ->
    forall u : List (Fin n), u.length = fallbackReacquireL n ->
      BirthPhaseWait2BlockProgress.target
          hpsi h2 kappa ring C u = false ->
        BirthPhaseWait2BlockProgress.rank kappa ring anchor
            (prefixEndpoint hpsi h2 ring C u) <=
          BirthPhaseWait2BlockProgress.rank kappa ring anchor C

/-- B4-R quantitative leaf. -/
def FallbackReacquireMass
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n) : Prop :=
  forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Reacquire
        hpsi h2 hn kappa tau ring anchor C ->
      n ^ fallbackReacquireL n <=
        fallbackReacquireQ *
          FixedSpanRenewalPayload.wordSum n (fallbackReacquireL n)
            (fallbackReacquireExitBit
              hpsi h2 hn kappa tau ring anchor C)

/-- Carrier-only restriction of B4 closure; the old all-Allowed clause is no
    longer the correct interface once block lengths depend on phase. -/
def FallbackCarrierClosed
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n) : Prop :=
  forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Carrier hpsi h2 hn ring anchor C ->
    forall u : List (Fin n),
      u.length = BirthPhaseWait2BlockProgress.L n ->
      BirthPhaseWait2BlockProgress.target
          hpsi h2 kappa ring C u = false ->
        BirthPhaseWait2BlockProgress.Allowed
          hpsi h2 hn kappa tau ring anchor
            (prefixEndpoint hpsi h2 ring C u)

/-- Carrier-only rank monotonicity. -/
def FallbackCarrierMono
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n) : Prop :=
  forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Carrier hpsi h2 hn ring anchor C ->
    forall u : List (Fin n),
      u.length = BirthPhaseWait2BlockProgress.L n ->
      BirthPhaseWait2BlockProgress.target
          hpsi h2 kappa ring C u = false ->
        BirthPhaseWait2BlockProgress.rank kappa ring anchor
            (prefixEndpoint hpsi h2 ring C u) <=
          BirthPhaseWait2BlockProgress.rank kappa ring anchor C

/-- Carrier-only B3 pointwise good statement. -/
def FallbackCarrierGood
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (DirtySuccess :
      BirthPhaseWait2BlockProgress.DirtySuccessRel n psi kappa tau) : Prop :=
  forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Carrier hpsi h2 hn ring anchor C ->
    forall u : List (Fin n),
      u.length = BirthPhaseWait2BlockProgress.L n ->
      BirthPhaseWait2BlockProgress.good DirtySuccess C u = true ->
        BirthPhaseWait2BlockProgress.target
            hpsi h2 kappa ring C u = true \/
          BirthPhaseWait2BlockProgress.rank kappa ring anchor
              (prefixEndpoint hpsi h2 ring C u) <
            BirthPhaseWait2BlockProgress.rank kappa ring anchor C

/-- Carrier-only `1/128` mass. -/
def FallbackCarrierMass
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (DirtySuccess :
      BirthPhaseWait2BlockProgress.DirtySuccessRel n psi kappa tau) : Prop :=
  forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Carrier hpsi h2 hn ring anchor C ->
      n ^ BirthPhaseWait2BlockProgress.L n <=
        BirthPhaseWait2BlockProgress.Q *
          FixedSpanRenewalPayload.wordSum n
            (BirthPhaseWait2BlockProgress.L n)
            (BirthPhaseGenericRenewal.goodWeight
              (BirthPhaseWait2BlockProgress.good DirtySuccess) C)

/-- One exact B4 interface for the two-phase fallback.  `HPos` and `HBound`
    remain the existing proved facts and are intentionally not repeated. -/
def TwoPhaseB4Contract
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (DirtySuccess :
      BirthPhaseWait2BlockProgress.DirtySuccessRel n psi kappa tau) : Prop :=
  FallbackCarrierClosed hpsi h2 hn kappa tau ring anchor /\
  FallbackCarrierMono hpsi h2 hn kappa tau ring anchor /\
  FallbackCarrierGood
    hpsi h2 hn kappa tau ring anchor DirtySuccess /\
  FallbackCarrierMass
    hpsi h2 hn kappa tau ring anchor DirtySuccess /\
  FallbackReacquireClosed hpsi h2 hn kappa tau ring anchor /\
  FallbackReacquireMono hpsi h2 hn kappa tau ring anchor /\
  FallbackReacquireMass hpsi h2 hn kappa tau ring anchor

/-! ## B7 replacement horizon and literal failure numerator -/

/-- `+3` allocates a quarter-budget `1/(4n)` instead of the old half-budget. -/
def quarterBudgetK (n Q : Nat) : Nat :=
  BirthPhaseGenericRenewal.renewalK Q (Nat.log2 n + 3)

/-- Maximum number of Carrier trials in the quarter-budget rank argument. -/
def fallbackCarrierTrials (n kappa : Nat) : Nat :=
  quarterBudgetK n BirthPhaseWait2BlockProgress.Q *
    BirthPhaseWait2BlockProgress.R kappa

/-- Reacquire blocks allowed per excursion.  The logarithm pays for a union
    bound over all possible Carrier trials. -/
def fallbackReacquireBlocks (n kappa : Nat) : Nat :=
  BirthPhaseGenericRenewal.renewalK fallbackReacquireQ
    (Nat.log2 (n * (fallbackCarrierTrials n kappa + 1)) + 3)

/-- Conservative fixed original-word prefix horizon for phase-adaptive B4. -/
def twoPhaseFirstCapHorizon (n kappa : Nat) : Nat :=
  fallbackCarrierTrials n kappa * BirthPhaseWait2BlockProgress.L n +
    fallbackCarrierTrials n kappa * fallbackReacquireBlocks n kappa *
      fallbackReacquireL n

noncomputable def noCapBit
    (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (u : List (Fin n)) : Nat :=
  @ite Nat
    (BirthPhaseWait2BlockProgress.FirstCapWithin
      hpsi h2 kappa ring C u)
    (Classical.propDecidable _) 0 1

/-- B7 can no longer use the single-block generic target-failure numerator.
    Count literal no-cap words directly at the phase-adaptive horizon. -/
noncomputable def twoPhaseFirstCapFailureNumerator
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (kappa : Nat) (ring : DirectedRing n)
    (C : FC n psi kappa tau) : Nat :=
  FixedSpanRenewalPayload.wordSum n (twoPhaseFirstCapHorizon n kappa)
    (noCapBit hpsi h2 kappa ring C)

/-- Replacement for `firstCap_failure_le_half_budget`.  Once proved from
    `TwoPhaseB4Contract`, B6 and the final B7 splice can remain unchanged apart
    from substituting this prefix horizon/numerator. -/
def TwoPhaseFirstCapHalfBudget
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n) : Prop :=
  forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Carrier hpsi h2 hn ring anchor C ->
      2 * n * twoPhaseFirstCapFailureNumerator
        hpsi h2 kappa ring C <=
      n ^ twoPhaseFirstCapHorizon n kappa

end BirthB1ReacquireReentryMass

#print axioms BirthB1ReacquireReentryMass.L_eq_reentry_add_local3
#print axioms BirthB1ReacquireReentryMass.reacquireReadyMass_of_reentryMass
#print axioms BirthB1ReacquireReentryMass.reacquireReadyMass_composes
#print axioms BirthB1ReacquireReentryMass.reacquireReentryMass_composes
