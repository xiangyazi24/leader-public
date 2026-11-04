import Leader.Wu.Seal.ABReadyComposition

/-!
# Fixed-AB stopped drift for the exact seal-sweep quotient

This file discharges the stopped first-Ready producer carried by
`PPartialSealSweepABReadyCompositionSol`.

Fix a directed edge whose endpoint states are exactly `A B`.  Before the first
loaded-home event that bond is invariant.  Weight every front by its clockwise
distance to the fixed `A` site.  Every genuine quotient move then lowers this
queue work by exactly one, all other non-Ready interactions stutter, and the
work is strictly below `n^2`.

The absorbing proof tree stops at the first Ready state; it does not alter the
physical transition system or assert that Ready persists.  At each live node
there is at least one genuine move.  Summing the one-step rank drift over the
uniform scheduler tree and telescoping gives the exact Markov-style tail bound

`(t+1) * readyMissTree(t) <= n^(t+1) * queueWork`.

Taking `t = 2*n^3` proves the requested half-mass producer.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialSealSweepABStoppedDriftSol

open PPLL PPLLResearchFormulation PPLLTraceConvergence
open PPLLSchedulerBlocks PPLLNoCheckBirthConditionTwoGeometry
open PPartialSealSweepHomeFrontQuotientSol
open PPartialSealSweepHomeTrapCurrentSol
open PPartialSealSweepHomeTrapWorkloadSol
open PPartialSealSweepReadySuffixHalfMassSol
open PPartialSealSweepABReadyCompositionSol

set_option autoImplicit false

variable {n psi kappa tau : Nat}

/-! ## Finite sums -/

private def abDriftFinSum {m : Nat} (f : Fin m -> Nat) : Nat :=
  (List.ofFn f).sum

private theorem abDriftFinSum_succ {m : Nat}
    (f : Fin (m + 1) -> Nat) :
    abDriftFinSum f = f 0 + abDriftFinSum (fun i : Fin m => f i.succ) := by
  unfold abDriftFinSum
  rw [List.ofFn_succ, List.sum_cons]

private theorem abDriftFinSum_le {m : Nat}
    (f g : Fin m -> Nat) (hfg : forall i, f i <= g i) :
    abDriftFinSum f <= abDriftFinSum g := by
  induction m with
  | zero => simp [abDriftFinSum]
  | succ m ih =>
      rw [abDriftFinSum_succ, abDriftFinSum_succ]
      exact Nat.add_le_add (hfg 0)
        (ih (fun i => f i.succ) (fun i => g i.succ)
          (fun i => hfg i.succ))

private theorem abDriftFinSum_add {m : Nat} (f g : Fin m -> Nat) :
    abDriftFinSum (fun i => f i + g i) =
      abDriftFinSum f + abDriftFinSum g := by
  induction m with
  | zero => simp [abDriftFinSum]
  | succ m ih =>
      rw [abDriftFinSum_succ, abDriftFinSum_succ,
        abDriftFinSum_succ, ih]
      omega

private theorem abDriftFinSum_mul_left {m : Nat}
    (c : Nat) (f : Fin m -> Nat) :
    abDriftFinSum (fun i => c * f i) = c * abDriftFinSum f := by
  induction m with
  | zero => simp [abDriftFinSum]
  | succ m ih =>
      rw [abDriftFinSum_succ, abDriftFinSum_succ, ih, Nat.mul_add]

private theorem abDriftFinSum_const (m c : Nat) :
    abDriftFinSum (fun _ : Fin m => c) = m * c := by
  induction m with
  | zero => simp [abDriftFinSum]
  | succ m ih =>
      rw [abDriftFinSum_succ, ih, Nat.succ_mul]
      omega

private theorem abDriftFinSum_single_change :
    forall {m : Nat} (f g : Fin m -> Nat) (victim : Fin m),
      (forall i : Fin m, i ≠ victim -> g i = f i) ->
      abDriftFinSum g + f victim = abDriftFinSum f + g victim := by
  intro m
  induction m with
  | zero =>
      intro f g victim _hv
      exact Fin.elim0 victim
  | succ m ih =>
      intro f g victim hv
      rw [abDriftFinSum_succ, abDriftFinSum_succ]
      cases victim using Fin.cases with
      | zero =>
          have htail :
              (fun i : Fin m => g i.succ) =
                fun i : Fin m => f i.succ := by
            funext i
            exact hv i.succ (Fin.succ_ne_zero i)
          rw [htail]
          omega
      | succ victim =>
          have hhead : g 0 = f 0 :=
            hv 0 (fun h => Fin.succ_ne_zero victim h.symm)
          have htail := ih
            (fun i : Fin m => f i.succ)
            (fun i : Fin m => g i.succ)
            victim
            (fun i hi => hv i.succ
              (fun h => hi (Fin.succ_inj.mp h)))
          rw [hhead]
          omega

private theorem abDriftFinSum_pair_change {m : Nat}
    (before after : Fin m -> Nat) (left right : Fin m)
    (hne : left ≠ right)
    (hother : forall i : Fin m, i ≠ left -> i ≠ right ->
      after i = before i) :
    abDriftFinSum after + before left + before right =
      abDriftFinSum before + after left + after right := by
  let middle : Fin m -> Nat := fun i =>
    if i = left then after i else before i
  have hfirst := abDriftFinSum_single_change before middle left (by
    intro i hi
    simp [middle, hi])
  have hmiddleRight : middle right = before right := by
    have hne' : right ≠ left := Ne.symm hne
    simp [middle, hne']
  have hsecond := abDriftFinSum_single_change middle after right (by
    intro i hi
    by_cases hil : i = left
    · subst i
      simp [middle]
    · rw [hother i hil hi]
      simp [middle, hil])
  have hmiddleLeft : middle left = after left := by simp [middle]
  rw [hmiddleLeft] at hfirst
  rw [hmiddleRight] at hsecond
  omega

private theorem abDriftFinSum_add_one_le_mul :
    forall {m : Nat} (f : Fin m -> Nat) (bound : Nat),
      (forall i, f i <= bound) -> forall witness : Fin m,
      f witness + 1 <= bound ->
      abDriftFinSum f + 1 <= m * bound := by
  intro m
  induction m with
  | zero =>
      intro f bound hall witness hwitness
      exact Fin.elim0 witness
  | succ m ih =>
      intro f bound hall witness hwitness
      rw [abDriftFinSum_succ, Nat.succ_mul]
      cases witness using Fin.cases with
      | zero =>
          have htail := abDriftFinSum_le
            (fun i : Fin m => f i.succ)
            (fun _ : Fin m => bound)
            (fun i => hall i.succ)
          rw [abDriftFinSum_const] at htail
          omega
      | succ witness =>
          have htail := ih
            (fun i : Fin m => f i.succ) bound
            (fun i => hall i.succ) witness hwitness
          have hhead := hall (0 : Fin (m + 1))
          omega

/-! ## Fixed-anchor queue work -/

/-- Front mass weighted by clockwise distance to the fixed `A` site. -/
def homeFrontABQueueWork (ring : DirectedRing n) (anchor : Fin n)
    (X : Fin n -> SealSweepHomeFrontSite) : Nat :=
  abDriftFinSum
    (fun i => homeFrontOccupancy X i * cwDist ring i anchor)

@[simp] theorem cwDist_self_abDrift
    (ring : DirectedRing n) (i : Fin n) :
    cwDist ring i i = 0 := by
  exact (cwPos_bounded_unique ring i i 0 ring.hn
    (cwPos_zero ring i)).symm

/-- A clockwise step toward a distinct fixed target removes one distance
unit. -/
theorem cwDist_rightNeighbor_add_one_abDrift
    (ring : DirectedRing n) (i anchor : Fin n) (hne : i ≠ anchor) :
    cwDist ring (ring.rightNeighbor i) anchor + 1 =
      cwDist ring i anchor := by
  let d := cwDist ring i anchor
  have hdlt : d < n := cwDist_lt ring i anchor
  have hdpos : 0 < d := by
    have hdne : d ≠ 0 := by
      intro hd0
      have hpos := cwPos_cwDist ring i anchor
      rw [show cwDist ring i anchor = d by rfl, hd0, cwPos_zero] at hpos
      exact hne hpos
    omega
  let d' := d - 1
  have hd'lt : d' < n := by omega
  have hpos' : cwPos ring (ring.rightNeighbor i) d' = anchor := by
    rw [cwPos_rightNeighbor]
    have hsucc : d' + 1 = d := by omega
    rw [hsucc]
    exact cwPos_cwDist ring i anchor
  have hcanonical := cwPos_bounded_unique ring
    (ring.rightNeighbor i) anchor d' hd'lt hpos'
  dsimp [d'] at hcanonical
  dsimp [d] at hdpos hcanonical
  omega

private theorem homeFrontOccupancy_left_eq_one_of_abDriftMove
    (X : Fin n -> SealSweepHomeFrontSite) (left right : Fin n)
    (hmove : sealSweepFrontMovePair (X left) (X right) = true) :
    homeFrontOccupancy X left = 1 := by
  rcases hl : X left with ⟨lh, lf⟩
  rcases hr : X right with ⟨rh, rf⟩
  cases lh <;> cases lf <;> cases rh <;> cases rf <;>
    simp [homeFrontOccupancy, sealSweepFrontMovePair, hl, hr] at hmove ⊢

private theorem homeFrontOccupancy_right_eq_zero_of_abDriftMove
    (X : Fin n -> SealSweepHomeFrontSite) (left right : Fin n)
    (hmove : sealSweepFrontMovePair (X left) (X right) = true) :
    homeFrontOccupancy X right = 0 := by
  rcases hl : X left with ⟨lh, lf⟩
  rcases hr : X right with ⟨rh, rf⟩
  cases lh <;> cases lf <;> cases rh <;> cases rf <;>
    simp [homeFrontOccupancy, sealSweepFrontMovePair, hl, hr] at hmove ⊢

private theorem homeFrontLocalStep_eq_self_of_abDriftPair_eq
    (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite) (edge : Fin n)
    (hpair : sealSweepHomeFrontPair
        (X edge) (X (ring.rightNeighbor edge)) =
      (X edge, X (ring.rightNeighbor edge))) :
    localStep ring sealSweepHomeFrontPair X edge = X := by
  funext i
  by_cases hie : i = edge
  · subst i
    simp [localStep, hpair]
  · by_cases hij : i = ring.rightNeighbor edge
    · subst i
      have hne : ring.rightNeighbor edge ≠ edge := by
        intro h
        exact hie h
      simp [localStep, hne, hpair]
    · simp [localStep, hie, hij]

/-- A genuine front move before Ready lowers the fixed-anchor queue work by
exactly one. -/
theorem homeFrontABQueueWork_localStep_add_one
    (ring : DirectedRing n) (hn : 1 < n)
    (X : Fin n -> SealSweepHomeFrontSite) (anchor edge : Fin n)
    (hanchor : HomeFrontABAnchor ring X anchor)
    (hmove : sealSweepFrontMovePair
      (X edge) (X (ring.rightNeighbor edge)) = true) :
    homeFrontABQueueWork ring anchor
        (localStep ring sealSweepHomeFrontPair X edge) + 1 =
      homeFrontABQueueWork ring anchor X := by
  let right := ring.rightNeighbor edge
  have her : edge ≠ right :=
    (rightNeighbor_ne_self_of_one_lt ring hn edge).symm
  have hea : edge ≠ anchor := by
    intro h
    subst edge
    simp [HomeFrontABAnchor, hanchor.1, hanchor.2,
      sealSweepFrontMovePair] at hmove
  have hdist := cwDist_rightNeighbor_add_one_abDrift
    ring edge anchor hea
  have hpair := sealSweepHomeFrontPair_eq_move_of_frontMove
    (X edge) (X right) (by simpa [right] using hmove)
  let before : Fin n -> Nat := fun i =>
    homeFrontOccupancy X i * cwDist ring i anchor
  let after : Fin n -> Nat := fun i =>
    homeFrontOccupancy
        (localStep ring sealSweepHomeFrontPair X edge) i *
      cwDist ring i anchor
  have hsum := abDriftFinSum_pair_change before after edge right her (by
    intro i hie hir
    have hir' : i ≠ ring.rightNeighbor edge := by
      simpa [right] using hir
    have hsite :
        localStep ring sealSweepHomeFrontPair X edge i = X i := by
      simp [localStep, hie, hir']
    change homeFrontOccupancy
        (localStep ring sealSweepHomeFrontPair X edge) i *
          cwDist ring i anchor =
      homeFrontOccupancy X i * cwDist ring i anchor
    unfold homeFrontOccupancy
    rw [hsite])
  have hbeforeLeft : before edge = cwDist ring edge anchor := by
    dsimp [before]
    rw [homeFrontOccupancy_left_eq_one_of_abDriftMove X edge right
      (by simpa [right] using hmove)]
    simp
  have hbeforeRight : before right = 0 := by
    dsimp [before]
    rw [homeFrontOccupancy_right_eq_zero_of_abDriftMove X edge right
      (by simpa [right] using hmove)]
    simp
  have hafterLeft : after edge = 0 := by
    have hsite : localStep ring sealSweepHomeFrontPair X edge edge =
        ((X edge).1, false) := by
      simp [localStep, hpair, right]
    simp [after, homeFrontOccupancy, hsite]
  have hafterRight : after right = cwDist ring right anchor := by
    have hsite : localStep ring sealSweepHomeFrontPair X edge right =
        ((X right).1, true) := by
      simp [localStep, right, her.symm, hpair]
    simp [after, homeFrontOccupancy, hsite]
  change abDriftFinSum after + 1 = abDriftFinSum before
  rw [hbeforeLeft, hbeforeRight, hafterLeft, hafterRight] at hsum
  have hdist' : after right + 1 = before edge := by
    rw [hafterRight, hbeforeLeft]
    simpa [right] using hdist
  have hsum' :
      abDriftFinSum after + before edge =
        abDriftFinSum before + after right := by
    omega
  rw [← hdist'] at hsum'
  omega

/-- The exact `A B` bond survives every interaction before first Ready. -/
theorem homeFrontABAnchor_localStep_of_not_ready
    (ring : DirectedRing n) (hn : 1 < n)
    (X : Fin n -> SealSweepHomeFrontSite) (anchor edge : Fin n)
    (hanchor : HomeFrontABAnchor ring X anchor)
    (hnotReady : ¬ HomeFrontHitReady ring X) :
    HomeFrontABAnchor ring
      (localStep ring sealSweepHomeFrontPair X edge) anchor := by
  let anchorRight := ring.rightNeighbor anchor
  let edgeRight := ring.rightNeighbor edge
  have hhit : sealSweepFrontHitsHomePair
      (X edge) (X edgeRight) = false := by
    cases h : sealSweepFrontHitsHomePair (X edge) (X edgeRight)
    · rfl
    · exfalso
      apply hnotReady
      exact ⟨edge, by simpa [edgeRight] using h⟩
  cases hmove : sealSweepFrontMovePair (X edge) (X edgeRight) with
  | false =>
      have hpair := sealSweepHomeFrontPair_eq_self_of_no_move_no_hit
        (X edge) (X edgeRight) hmove hhit
      have hstep := homeFrontLocalStep_eq_self_of_abDriftPair_eq
        ring X edge (by simpa [edgeRight] using hpair)
      simpa [hstep] using hanchor
  | true =>
      have hleftOcc := homeFrontOccupancy_left_eq_one_of_abDriftMove
        X edge edgeRight hmove
      have hrightOcc := homeFrontOccupancy_right_eq_zero_of_abDriftMove
        X edge edgeRight hmove
      have hea : edge ≠ anchor := by
        intro h
        subst edge
        simp [hanchor.1, hanchor.2,
          sealSweepFrontMovePair, edgeRight] at hmove
      have hra : edgeRight ≠ anchor := by
        intro h
        have hzero : homeFrontOccupancy X anchor = 0 := by
          simpa [edgeRight, h] using hrightOcc
        have : False := by
          simpa [homeFrontOccupancy, hanchor.1] using hzero
        exact this.elim
      have heb : edge ≠ anchorRight := by
        intro h
        subst edge
        have hone : homeFrontOccupancy X anchorRight = 1 := hleftOcc
        have hsite : X anchorRight = (true, false) := by
          simpa [anchorRight] using hanchor.2
        have : False := by
          simpa [homeFrontOccupancy, hsite] using hone
        exact this.elim
      have hrb : edgeRight ≠ anchorRight := by
        intro h
        have hneighbors : ring.rightNeighbor edge =
            ring.rightNeighbor anchor := by
          simpa [edgeRight, anchorRight] using h
        exact hea (rightNeighbor_injective ring hneighbors)
      constructor
      · simpa [localStep, edgeRight, hea.symm, hra.symm] using hanchor.1
      · simpa [localStep, edgeRight, anchorRight, heb.symm, hrb.symm]
          using hanchor.2

/-- Before Ready, no scheduler edge increases the fixed-anchor work. -/
theorem homeFrontABQueueWork_localStep_le_of_not_ready
    (ring : DirectedRing n) (hn : 1 < n)
    (X : Fin n -> SealSweepHomeFrontSite) (anchor edge : Fin n)
    (hanchor : HomeFrontABAnchor ring X anchor)
    (hnotReady : ¬ HomeFrontHitReady ring X) :
    homeFrontABQueueWork ring anchor
        (localStep ring sealSweepHomeFrontPair X edge) <=
      homeFrontABQueueWork ring anchor X := by
  cases hmove : sealSweepFrontMovePair
      (X edge) (X (ring.rightNeighbor edge)) with
  | true =>
      have hexact := homeFrontABQueueWork_localStep_add_one
        ring hn X anchor edge hanchor hmove
      omega
  | false =>
      have hhit : sealSweepFrontHitsHomePair
          (X edge) (X (ring.rightNeighbor edge)) = false := by
        cases h : sealSweepFrontHitsHomePair
            (X edge) (X (ring.rightNeighbor edge))
        · rfl
        · exact False.elim (hnotReady ⟨edge, h⟩)
      have hpair := sealSweepHomeFrontPair_eq_self_of_no_move_no_hit
        (X edge) (X (ring.rightNeighbor edge)) hmove hhit
      rw [homeFrontLocalStep_eq_self_of_abDriftPair_eq
        ring X edge hpair]
      exact Nat.le_refl _

/-- Every positive exact non-Ready anchored state has a scheduler edge that
decreases queue work by exactly one. -/
theorem positiveHomeFrontABAnchor_exists_exact_descent
    (ring : DirectedRing n) (hn : 1 < n)
    (X : Fin n -> SealSweepHomeFrontSite) (anchor : Fin n)
    (hX : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring X)
    (hanchor : HomeFrontABAnchor ring X anchor)
    (hnotReady : ¬ HomeFrontHitReady ring X) :
    exists edge : Fin n,
      sealSweepFrontMovePair
          (X edge) (X (ring.rightNeighbor edge)) = true /\
        homeFrontABQueueWork ring anchor
            (localStep ring sealSweepHomeFrontPair X edge) + 1 =
          homeFrontABQueueWork ring anchor X := by
  obtain hready | ⟨edge, hmove⟩ :=
    positiveHomeFrontState_ready_or_successfulMove ring X hX
  · exact False.elim (hnotReady hready)
  · exact ⟨edge, hmove,
      homeFrontABQueueWork_localStep_add_one
        ring hn X anchor edge hanchor hmove⟩

theorem positiveHomeFrontABQueueWork_pos
    (ring : DirectedRing n) (hn : 1 < n)
    (X : Fin n -> SealSweepHomeFrontSite) (anchor : Fin n)
    (hX : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring X)
    (hanchor : HomeFrontABAnchor ring X anchor)
    (hnotReady : ¬ HomeFrontHitReady ring X) :
    0 < homeFrontABQueueWork ring anchor X := by
  obtain ⟨edge, _hmove, hexact⟩ :=
    positiveHomeFrontABAnchor_exists_exact_descent
      ring hn X anchor hX hanchor hnotReady
  omega

/-- The queue work is strictly below `n^2` on every quotient word. -/
theorem homeFrontABQueueWork_lt_square
    (ring : DirectedRing n) (hn : 1 < n) (anchor : Fin n)
    (X : Fin n -> SealSweepHomeFrontSite) :
    homeFrontABQueueWork ring anchor X < n ^ 2 := by
  have hterms : forall i : Fin n,
      homeFrontOccupancy X i * cwDist ring i anchor <= n - 1 := by
    intro i
    unfold homeFrontOccupancy
    cases hfront : (X i).2
    · simp [hfront]
    · simp [hfront]
      have hdist := cwDist_lt ring i anchor
      omega
  have hsum := abDriftFinSum_le
    (fun i => homeFrontOccupancy X i * cwDist ring i anchor)
    (fun _ : Fin n => n - 1) hterms
  rw [abDriftFinSum_const] at hsum
  change homeFrontABQueueWork ring anchor X <= n * (n - 1) at hsum
  have hfactor : n * (n - 1) < n * n :=
    (Nat.mul_lt_mul_left (by omega : 0 < n)).2 (by omega)
  simpa [Nat.pow_two] using Nat.lt_of_le_of_lt hsum hfactor

/-! ## Absorbing scheduler tree -/

/-- Total fixed-anchor queue work over the leaves that have not yet visited
Ready. -/
noncomputable def homeFrontABStoppedWorkTree
    (ring : DirectedRing n) (anchor : Fin n) :
    (Fin n -> SealSweepHomeFrontSite) -> Nat -> Nat
  | X, 0 =>
      @ite Nat (HomeFrontHitReady ring X) (Classical.propDecidable _) 0
        (homeFrontABQueueWork ring anchor X)
  | X, t + 1 =>
      @ite Nat (HomeFrontHitReady ring X) (Classical.propDecidable _) 0
        (abDriftFinSum (fun edge => homeFrontABStoppedWorkTree ring anchor
          (localStep ring sealSweepHomeFrontPair X edge) t))

/-- The private finite sum used inside the imported stopped-miss tree is
definitionally the same `List.ofFn` sum as `abDriftFinSum`. -/
private theorem homeFrontABReadyMissTree_succ_eq_abDriftFinSum
    (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite) (t : Nat)
    (hnotReady : ¬ HomeFrontHitReady ring X) :
    homeFrontABReadyMissTree ring X (t + 1) =
      abDriftFinSum (fun edge => homeFrontABReadyMissTree ring
        (localStep ring sealSweepHomeFrontPair X edge) t) := by
  simp only [homeFrontABReadyMissTree]
  rw [if_neg hnotReady]
  rfl

private theorem homeFrontStoppedWork_le_queueWork
    (ring : DirectedRing n) (anchor : Fin n)
    (X : Fin n -> SealSweepHomeFrontSite) :
    homeFrontABStoppedWorkTree ring anchor X 0 <=
      homeFrontABQueueWork ring anchor X := by
  simp only [homeFrontABStoppedWorkTree]
  split <;> omega

/-- One scheduler generation pays one unit for every live anchored node. -/
theorem positiveHomeFrontABAnchor_oneStep_drift
    (ring : DirectedRing n) (hn : 1 < n)
    (X : Fin n -> SealSweepHomeFrontSite) (anchor : Fin n)
    (hX : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring X)
    (hanchor : HomeFrontABAnchor ring X anchor)
    (hnotReady : ¬ HomeFrontHitReady ring X) :
    abDriftFinSum (fun edge => homeFrontABStoppedWorkTree ring anchor
        (localStep ring sealSweepHomeFrontPair X edge) 0) + 1 <=
      n * homeFrontABQueueWork ring anchor X := by
  obtain ⟨witness, _hmove, hwitnessExact⟩ :=
    positiveHomeFrontABAnchor_exists_exact_descent
      ring hn X anchor hX hanchor hnotReady
  have hall : forall edge : Fin n,
      homeFrontABStoppedWorkTree ring anchor
          (localStep ring sealSweepHomeFrontPair X edge) 0 <=
        homeFrontABQueueWork ring anchor X := by
    intro edge
    exact Nat.le_trans
      (homeFrontStoppedWork_le_queueWork ring anchor
        (localStep ring sealSweepHomeFrontPair X edge))
      (homeFrontABQueueWork_localStep_le_of_not_ready
        ring hn X anchor edge hanchor hnotReady)
  have hwitness :
      homeFrontABStoppedWorkTree ring anchor
          (localStep ring sealSweepHomeFrontPair X witness) 0 + 1 <=
        homeFrontABQueueWork ring anchor X := by
    have hstop := homeFrontStoppedWork_le_queueWork ring anchor
      (localStep ring sealSweepHomeFrontPair X witness)
    omega
  exact abDriftFinSum_add_one_le_mul
    (fun edge => homeFrontABStoppedWorkTree ring anchor
      (localStep ring sealSweepHomeFrontPair X edge) 0)
    (homeFrontABQueueWork ring anchor X) hall witness hwitness

/-- The stopped work satisfies the absorbing drift inequality at every tree
depth. -/
theorem positiveHomeFrontABStoppedWorkTree_drift
    (ring : DirectedRing n) (hn : 1 < n)
    (X : Fin n -> SealSweepHomeFrontSite) (anchor : Fin n)
    (hX : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring X)
    (hanchor : HomeFrontABAnchor ring X anchor) (t : Nat) :
    homeFrontABStoppedWorkTree ring anchor X (t + 1) +
        homeFrontABReadyMissTree ring X t <=
      n * homeFrontABStoppedWorkTree ring anchor X t := by
  induction t generalizing X with
  | zero =>
      by_cases hready : HomeFrontHitReady ring X
      · simp [homeFrontABStoppedWorkTree, homeFrontABReadyMissTree,
          hready]
      · simpa [homeFrontABStoppedWorkTree, homeFrontABReadyMissTree,
          hready] using
          positiveHomeFrontABAnchor_oneStep_drift
            ring hn X anchor hX hanchor hready
  | succ t ih =>
      by_cases hready : HomeFrontHitReady ring X
      · simp [homeFrontABStoppedWorkTree, homeFrontABReadyMissTree,
          hready]
      · have hanchorStep : forall edge : Fin n,
            HomeFrontABAnchor ring
              (localStep ring sealSweepHomeFrontPair X edge) anchor :=
          fun edge => homeFrontABAnchor_localStep_of_not_ready
            ring hn X anchor edge hanchor hready
        have hchildren := abDriftFinSum_le
          (fun edge =>
            homeFrontABStoppedWorkTree ring anchor
                (localStep ring sealSweepHomeFrontPair X edge) (t + 1) +
              homeFrontABReadyMissTree ring
                (localStep ring sealSweepHomeFrontPair X edge) t)
          (fun edge => n * homeFrontABStoppedWorkTree ring anchor
            (localStep ring sealSweepHomeFrontPair X edge) t)
          (fun edge => ih
            (localStep ring sealSweepHomeFrontPair X edge)
            (positiveHomeFrontState_localStep ring X hX edge)
            (hanchorStep edge))
        rw [abDriftFinSum_add, abDriftFinSum_mul_left] at hchildren
        rw [homeFrontABReadyMissTree_succ_eq_abDriftFinSum
          ring X t hready]
        simpa [homeFrontABStoppedWorkTree, hready] using hchildren

/-- Time-weighted survival sum for the absorbing Ready tree. -/
noncomputable def homeFrontABWeightedMissTotal
    (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite) : Nat -> Nat
  | 0 => 0
  | t + 1 => n * homeFrontABWeightedMissTotal ring X t +
      homeFrontABReadyMissTree ring X t

/-- The stopped queue telescope charges the full weighted survival sum. -/
theorem positiveHomeFrontABStoppedWorkTree_telescope
    (ring : DirectedRing n) (hn : 1 < n)
    (X : Fin n -> SealSweepHomeFrontSite) (anchor : Fin n)
    (hX : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring X)
    (hanchor : HomeFrontABAnchor ring X anchor) (t : Nat) :
    homeFrontABStoppedWorkTree ring anchor X t +
        homeFrontABWeightedMissTotal ring X t <=
      n ^ t * homeFrontABQueueWork ring anchor X := by
  induction t with
  | zero =>
      exact Nat.le_trans
        (Nat.add_le_add_right
          (homeFrontStoppedWork_le_queueWork ring anchor X) 0)
        (by simp [homeFrontABWeightedMissTotal])
  | succ t ih =>
      have hscaled := Nat.mul_le_mul_left n ih
      have hdrift := positiveHomeFrontABStoppedWorkTree_drift
        ring hn X anchor hX hanchor t
      rw [homeFrontABWeightedMissTotal, Nat.pow_succ]
      calc
        homeFrontABStoppedWorkTree ring anchor X (t + 1) +
            (n * homeFrontABWeightedMissTotal ring X t +
              homeFrontABReadyMissTree ring X t) =
            (homeFrontABStoppedWorkTree ring anchor X (t + 1) +
              homeFrontABReadyMissTree ring X t) +
                n * homeFrontABWeightedMissTotal ring X t := by omega
        _ <= n * homeFrontABStoppedWorkTree ring anchor X t +
              n * homeFrontABWeightedMissTotal ring X t :=
            Nat.add_le_add_right hdrift _
        _ = n * (homeFrontABStoppedWorkTree ring anchor X t +
              homeFrontABWeightedMissTotal ring X t) := by
            rw [Nat.mul_add]
        _ <= n * (n ^ t * homeFrontABQueueWork ring anchor X) := hscaled
        _ = n ^ t * n * homeFrontABQueueWork ring anchor X := by
            simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem positiveHomeFrontABWeightedMissTotal_budget
    (ring : DirectedRing n) (hn : 1 < n)
    (X : Fin n -> SealSweepHomeFrontSite) (anchor : Fin n)
    (hX : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring X)
    (hanchor : HomeFrontABAnchor ring X anchor) (t : Nat) :
    homeFrontABWeightedMissTotal ring X t <=
      n ^ t * homeFrontABQueueWork ring anchor X := by
  have h := positiveHomeFrontABStoppedWorkTree_telescope
    ring hn X anchor hX hanchor t
  omega

/-- Every live prefix has at most `n` live extensions. -/
theorem homeFrontABReadyMissTree_succ_le_mul
    (ring : DirectedRing n) (X : Fin n -> SealSweepHomeFrontSite)
    (t : Nat) :
    homeFrontABReadyMissTree ring X (t + 1) <=
      n * homeFrontABReadyMissTree ring X t := by
  induction t generalizing X with
  | zero =>
      by_cases hready : HomeFrontHitReady ring X
      · simp [homeFrontABReadyMissTree, hready]
      · rw [homeFrontABReadyMissTree_succ_eq_abDriftFinSum
          ring X 0 hready]
        have hchildren := abDriftFinSum_le
          (fun edge => @ite Nat
            (HomeFrontHitReady ring
              (localStep ring sealSweepHomeFrontPair X edge))
            (Classical.propDecidable _) 0 1)
          (fun _ : Fin n => 1) (by
            intro edge
            split <;> omega)
        rw [abDriftFinSum_const] at hchildren
        simpa [homeFrontABReadyMissTree, hready] using hchildren
  | succ t ih =>
      by_cases hready : HomeFrontHitReady ring X
      · simp [homeFrontABReadyMissTree, hready]
      · rw [homeFrontABReadyMissTree_succ_eq_abDriftFinSum
          ring X (t + 1) hready]
        have hchildren := abDriftFinSum_le
          (fun edge => homeFrontABReadyMissTree ring
            (localStep ring sealSweepHomeFrontPair X edge) (t + 1))
          (fun edge => n * homeFrontABReadyMissTree ring
            (localStep ring sealSweepHomeFrontPair X edge) t)
          (fun edge => ih (localStep ring sealSweepHomeFrontPair X edge))
        rw [abDriftFinSum_mul_left] at hchildren
        rw [homeFrontABReadyMissTree_succ_eq_abDriftFinSum
          ring X t hready]
        exact hchildren

/-- The last survival layer appears at least `t+1` times in the weighted
survival sum. -/
theorem homeFrontABReadyMissTree_mul_time_le_weighted
    (ring : DirectedRing n) (X : Fin n -> SealSweepHomeFrontSite)
    (t : Nat) :
    (t + 1) * homeFrontABReadyMissTree ring X t <=
      homeFrontABWeightedMissTotal ring X (t + 1) := by
  induction t with
  | zero => simp [homeFrontABWeightedMissTotal]
  | succ t ih =>
      have hmono := homeFrontABReadyMissTree_succ_le_mul ring X t
      have hmonoScaled := Nat.mul_le_mul_left (t + 1) hmono
      have hihScaled := Nat.mul_le_mul_left n ih
      rw [homeFrontABWeightedMissTotal]
      grind

/-- Exact division-free first-Ready tail inequality. -/
theorem positiveHomeFrontABReadyMissTree_tail
    (ring : DirectedRing n) (hn : 1 < n)
    (X : Fin n -> SealSweepHomeFrontSite) (anchor : Fin n)
    (hX : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring X)
    (hanchor : HomeFrontABAnchor ring X anchor) (t : Nat) :
    (t + 1) * homeFrontABReadyMissTree ring X t <=
      n ^ (t + 1) * homeFrontABQueueWork ring anchor X := by
  have hlower := homeFrontABReadyMissTree_mul_time_le_weighted ring X t
  have hbudget := positiveHomeFrontABWeightedMissTotal_budget
    ring hn X anchor hX hanchor (t + 1)
  exact Nat.le_trans hlower hbudget

/-- Cancellation-safe polynomial first-Ready tail. -/
theorem positiveHomeFrontABReadyMissTree_polynomial_tail
    (ring : DirectedRing n) (hn : 1 < n)
    (X : Fin n -> SealSweepHomeFrontSite) (anchor : Fin n)
    (hX : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring X)
    (hanchor : HomeFrontABAnchor ring X anchor)
    (hnotReady : ¬ HomeFrontHitReady ring X)
    (q t : Nat)
    (horizon : q * n * homeFrontABQueueWork ring anchor X <= t + 1) :
    q * homeFrontABReadyMissTree ring X t <= n ^ t := by
  have htail := positiveHomeFrontABReadyMissTree_tail
    ring hn X anchor hX hanchor t
  have hscaled := Nat.mul_le_mul_right
    (homeFrontABReadyMissTree ring X t) horizon
  have hchain := Nat.le_trans hscaled htail
  have hcommon :
      (n * homeFrontABQueueWork ring anchor X) *
          (q * homeFrontABReadyMissTree ring X t) <=
        (n * homeFrontABQueueWork ring anchor X) * n ^ t := by
    simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      using hchain
  have hpositive : 0 < n * homeFrontABQueueWork ring anchor X :=
    Nat.mul_pos ring.hn
      (positiveHomeFrontABQueueWork_pos
        ring hn X anchor hX hanchor hnotReady)
  exact Nat.le_of_mul_le_mul_left hcommon hpositive

/-- At horizon `2*n^3`, at most half of the exact iid scheduler words have
missed first Ready. -/
theorem positiveHomeFrontABReadyMissTree_half_at_twoCubic
    (ring : DirectedRing n) (hn : 1 < n)
    (X : Fin n -> SealSweepHomeFrontSite) (anchor : Fin n)
    (hX : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring X)
    (hanchor : HomeFrontABAnchor ring X anchor)
    (hnotReady : ¬ HomeFrontHitReady ring X) :
    2 * homeFrontABReadyMissTree ring X (2 * n ^ 3) <=
      n ^ (2 * n ^ 3) := by
  apply positiveHomeFrontABReadyMissTree_polynomial_tail
    ring hn X anchor hX hanchor hnotReady 2 (2 * n ^ 3)
  have hwork := homeFrontABQueueWork_lt_square ring hn anchor X
  have hworkLe : homeFrontABQueueWork ring anchor X <= n ^ 2 :=
    Nat.le_of_lt hwork
  have hscaled := Nat.mul_le_mul_left (2 * n) hworkLe
  calc
    2 * n * homeFrontABQueueWork ring anchor X <=
        2 * n * n ^ 2 := hscaled
    _ = 2 * n ^ 3 := by
      simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ <= 2 * n ^ 3 + 1 := by omega

/-- Unconditional producer for the exact stopped-drift interface used by the
AB-to-endpoint composition theorem. -/
theorem positiveHomeFrontABStoppedReadyHalf
    (ring : DirectedRing n) (hn : 1 < n)
    (X : Fin n -> SealSweepHomeFrontSite)
    (hX : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring X)
    (anchor : Fin n) :
    HomeFrontABStoppedReadyHalf ring X anchor := by
  intro hanchor hnotReady
  exact positiveHomeFrontABReadyMissTree_half_at_twoCubic
    ring hn X anchor hX hanchor hnotReady

/-- R116 with its stopped-drift premise discharged.  The inverse-square
`A B` pre-gate is now the sole remaining producer: the horizon, factor, and
dropped-or-ready endpoint event are exactly those of the original composition
theorem. -/
theorem positiveHomeFront_inverseSquareABGate_to_dropOrReady_unconditionalStoppedDrift
    (ring : DirectedRing n) (hn : 1 < n)
    (X : Fin n -> SealSweepHomeFrontSite)
    (hX : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring X)
    (gate : Nat)
    (hgate : HomeFrontInverseSquareABGate ring X gate) :
    n ^ (gate + 2 * n ^ 3) <=
      4 * n ^ 2 * homeFrontDropOrReadyEndpointCount ring X
        (gate + 2 * n ^ 3) := by
  apply positiveHomeFront_inverseSquareABGate_to_dropOrReady
    (psi := psi) (kappa := kappa) (tau := tau)
    ring hn X hX gate hgate
  intro Y hY anchor
  exact positiveHomeFrontABStoppedReadyHalf ring hn Y hY anchor

#print axioms homeFrontABQueueWork_localStep_add_one
#print axioms homeFrontABAnchor_localStep_of_not_ready
#print axioms positiveHomeFrontABReadyMissTree_half_at_twoCubic
#print axioms positiveHomeFrontABStoppedReadyHalf
#print axioms positiveHomeFront_inverseSquareABGate_to_dropOrReady_unconditionalStoppedDrift

end PPartialSealSweepABStoppedDriftSol
end PPLLCompleteMultiLeaderCleanup
