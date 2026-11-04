import Leader.Wu.Splice.PhysicalHoldWordProjection
import Leader.Wu.Splice.PhysicalHoldProgressStatement

set_option autoImplicit false

/-! # The deterministic projection letter, locality, and same-edge hits with far services between

`letterOf C e` is the extended letter of one V10e service, chosen by its physical effect: a host
letter when the service is physical, a relabel letter when the bases move by the MOVE-COMMIT
relabel, nothing otherwise.  `projWord` maps a service word to its extended word; its host count
is exactly the number of physical services along the word.

A service of an edge far from `e` (neither `e` nor the two edges sharing a site with it) does not
touch the served pair of `e`; so hits of `e` with only far services between them act on the pair
exactly as consecutive services of `e` (`serveIter`), which is the form of the global progress
theorem.  This is the bridge from the three-same-port matcher to the projected word. -/

namespace B9SpliceV10eProjectionLetter

open PPLL PPLLDomain PPLLResearchFormulation PPLLExpiringComparisonRepair
open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV6
  B9SpliceControllerR1TableV7 B9SpliceTableV10e B9SpliceV10eTransparency
  B9SpliceV10ePhysicalIsB7Step B9SpliceV10eProjection B9SpliceV10eWordProjection
  B9SpliceV10eGlobalProgress

variable {n psi width kappa tau : Nat}

/-! ## Locality of one service -/

theorem stepV10e_other (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e i : Fin n)
    (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    stepV10e hpsi hwidth hle ring C e i = C i := by
  unfold stepV10e
  by_cases h : ring.rightNeighbor e = e
  · simp [h]
  · simp [h, hi, hj]

theorem stepV10e_at_left (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    stepV10e hpsi hwidth hle ring C e e =
      (rowV10e hpsi hwidth hle (C e) (C (ring.rightNeighbor e))).1 := by
  simp [stepV10e, hne]

theorem stepV10e_at_right (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    stepV10e hpsi hwidth hle ring C e (ring.rightNeighbor e) =
      (rowV10e hpsi hwidth hle (C e) (C (ring.rightNeighbor e))).2 := by
  simp [stepV10e, hne]

theorem rightNeighbor_ne_self (ring : DirectedRing n) (hn : 2 ≤ n) (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  simp only [DirectedRing.rightNeighbor] at hv
  have he := e.isLt
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv; omega
  · have heq : e.val + 1 = n := by omega
    rw [heq, Nat.mod_self] at hv
    omega

/-- The served pair after a service depends only on the served pair before. -/
theorem step_pair_of_pair (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C C' : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hl : C' e = C e) (hr : C' (ring.rightNeighbor e) = C (ring.rightNeighbor e)) :
    stepV10e hpsi hwidth hle ring C' e e = stepV10e hpsi hwidth hle ring C e e ∧
    stepV10e hpsi hwidth hle ring C' e (ring.rightNeighbor e) =
      stepV10e hpsi hwidth hle ring C e (ring.rightNeighbor e) := by
  rw [stepV10e_at_left hpsi hwidth hle ring C' e hne, stepV10e_at_left hpsi hwidth hle ring C e hne,
    stepV10e_at_right hpsi hwidth hle ring C' e hne, stepV10e_at_right hpsi hwidth hle ring C e hne,
    hl, hr]
  exact ⟨rfl, rfl⟩

/-- Physicality of a service depends only on the served pair. -/
theorem physical_of_pair (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C C' : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hl : C' e = C e) (hr : C' (ring.rightNeighbor e) = C (ring.rightNeighbor e)) :
    PhysicalServiceAt hpsi hwidth hle ring C' (stepV10e hpsi hwidth hle ring C' e) e ↔
    PhysicalServiceAt hpsi hwidth hle ring C (stepV10e hpsi hwidth hle ring C e) e := by
  obtain ⟨h1, h2⟩ := step_pair_of_pair hpsi hwidth hle ring C C' e hne hl hr
  unfold PhysicalServiceAt
  dsimp only
  rw [h1, h2, hl, hr]

/-- Edges that share no site with `e`. -/
def Far (ring : DirectedRing n) (e f : Fin n) : Prop :=
  f ≠ e ∧ f ≠ ring.leftNeighbor e ∧ f ≠ ring.rightNeighbor e

theorem step_far_left (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e f : Fin n) (hf : Far ring e f) :
    stepV10e hpsi hwidth hle ring C f e = C e := by
  apply stepV10e_other hpsi hwidth hle ring C f e (Ne.symm hf.1)
  intro h
  apply hf.2.1
  apply B9OrphanToFence.rightNeighbor_inj ring
  rw [← h, rightNeighbor_leftNeighbor]

theorem step_far_right (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e f : Fin n) (hf : Far ring e f) :
    stepV10e hpsi hwidth hle ring C f (ring.rightNeighbor e) = C (ring.rightNeighbor e) := by
  apply stepV10e_other hpsi hwidth hle ring C f _ (Ne.symm hf.2.2)
  intro h
  apply hf.1
  exact B9OrphanToFence.rightNeighbor_inj ring h.symm

/-- A word of far services leaves the pair of `e` untouched. -/
theorem serveWord_far (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (e : Fin n) (u : List (Fin n)) (hu : ∀ f ∈ u, Far ring e f) :
    ∀ C : R1ConfigV6 n psi kappa tau,
      serveWord hpsi hwidth hle ring u C e = C e ∧
      serveWord hpsi hwidth hle ring u C (ring.rightNeighbor e) = C (ring.rightNeighbor e) := by
  induction u with
  | nil => intro C; exact ⟨rfl, rfl⟩
  | cons f u ih =>
    intro C
    have hf : Far ring e f := hu f (List.mem_cons_self ..)
    have hu' : ∀ g ∈ u, Far ring e g := fun g hg => hu g (List.mem_cons_of_mem f hg)
    obtain ⟨h1, h2⟩ := ih hu' (stepV10e hpsi hwidth hle ring C f)
    show serveWord hpsi hwidth hle ring u (stepV10e hpsi hwidth hle ring C f) e = C e ∧
      serveWord hpsi hwidth hle ring u (stepV10e hpsi hwidth hle ring C f) (ring.rightNeighbor e) =
        C (ring.rightNeighbor e)
    rw [h1, h2, step_far_left hpsi hwidth hle ring C e f hf, step_far_right hpsi hwidth hle ring C e f hf]
    exact ⟨rfl, rfl⟩

/-! ## Hits of `e` with far services between act as consecutive services -/

/-- `hitWord e [u1, …, uk]` = `e u1 e u2 … e uk`: `k` hits of `e`, each followed by a word. -/
def hitWord (e : Fin n) : List (List (Fin n)) → List (Fin n)
  | [] => []
  | u :: us => e :: (u ++ hitWord e us)

theorem serveWord_append (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (a b : List (Fin n)) (C : R1ConfigV6 n psi kappa tau) :
    serveWord hpsi hwidth hle ring (a ++ b) C =
      serveWord hpsi hwidth hle ring b (serveWord hpsi hwidth hle ring a C) := by
  induction a generalizing C with
  | nil => rfl
  | cons f a ih => exact ih _

theorem serveIter_succ_comm (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (e : Fin n) (k : Nat) (C : R1ConfigV6 n psi kappa tau) :
    serveIter hpsi hwidth hle ring e (k + 1) C =
      serveIter hpsi hwidth hle ring e k (stepV10e hpsi hwidth hle ring C e) := by
  induction k generalizing C with
  | zero => rfl
  | succ k ih =>
    show stepV10e hpsi hwidth hle ring (serveIter hpsi hwidth hle ring e (k + 1) C) e = _
    rw [ih]
    rfl

/-- After `k` hits with far words between, the pair of `e` is the pair after `k` consecutive
services of `e`. -/
theorem hitWord_pair (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (e : Fin n) (hne : ring.rightNeighbor e ≠ e)
    (us : List (List (Fin n))) (hus : ∀ u ∈ us, ∀ f ∈ u, Far ring e f) :
    ∀ C : R1ConfigV6 n psi kappa tau,
      serveWord hpsi hwidth hle ring (hitWord e us) C e =
        serveIter hpsi hwidth hle ring e us.length C e ∧
      serveWord hpsi hwidth hle ring (hitWord e us) C (ring.rightNeighbor e) =
        serveIter hpsi hwidth hle ring e us.length C (ring.rightNeighbor e) := by
  induction us with
  | nil => intro C; exact ⟨rfl, rfl⟩
  | cons u us ih =>
    intro C
    have hu : ∀ f ∈ u, Far ring e f := hus u (List.mem_cons_self ..)
    have hus' : ∀ v ∈ us, ∀ f ∈ v, Far ring e f := fun v hv => hus v (List.mem_cons_of_mem u hv)
    -- serveIter (k+1) C = step (serveIter k C) e; hitWord = e :: (u ++ rest)
    show serveWord hpsi hwidth hle ring (u ++ hitWord e us) (stepV10e hpsi hwidth hle ring C e) e =
        serveIter hpsi hwidth hle ring e (us.length + 1) C e ∧
      serveWord hpsi hwidth hle ring (u ++ hitWord e us) (stepV10e hpsi hwidth hle ring C e)
          (ring.rightNeighbor e) =
        serveIter hpsi hwidth hle ring e (us.length + 1) C (ring.rightNeighbor e)
    rw [serveWord_append]
    obtain ⟨h1, h2⟩ := ih hus' (serveWord hpsi hwidth hle ring u (stepV10e hpsi hwidth hle ring C e))
    rw [h1, h2]
    -- serveIter k on a config agreeing with (step C e) on the pair agrees on the pair
    obtain ⟨g1, g2⟩ := serveWord_far hpsi hwidth hle ring e u hu (stepV10e hpsi hwidth hle ring C e)
    have key : ∀ (k : Nat) (D D' : R1ConfigV6 n psi kappa tau),
        D' e = D e → D' (ring.rightNeighbor e) = D (ring.rightNeighbor e) →
        serveIter hpsi hwidth hle ring e k D' e = serveIter hpsi hwidth hle ring e k D e ∧
        serveIter hpsi hwidth hle ring e k D' (ring.rightNeighbor e) =
          serveIter hpsi hwidth hle ring e k D (ring.rightNeighbor e) := by
      intro k
      induction k with
      | zero => intro D D' hl hr; exact ⟨hl, hr⟩
      | succ k ihk =>
        intro D D' hl hr
        obtain ⟨a1, a2⟩ := ihk D D' hl hr
        exact step_pair_of_pair hpsi hwidth hle ring _ _ e hne a1 a2
    obtain ⟨k1, k2⟩ := key us.length (stepV10e hpsi hwidth hle ring C e) _ g1 g2
    rw [k1, k2, serveIter_succ_comm]
    exact ⟨rfl, rfl⟩

/-! ## The deterministic letter -/

/-- A service whose projection is the host step at `e` is a physical service. -/
theorem physical_of_hostStep (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C D : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (h : physicalProj D = BirthShortDoneTerminalConsumer.step hpsi hwidth hle ring (physicalProj C) e) :
    PhysicalServiceAt hpsi hwidth hle ring C D e := by
  have he := congrFun h e
  have hj := congrFun h (ring.rightNeighbor e)
  unfold BirthShortDoneTerminalConsumer.step at he hj
  have se := BirthB1CountStepReduction.step_apply
    (BirthShortDoneTerminalConsumer.protocol hpsi hwidth hle kappa tau) ring
    (physicalProj C : (BirthShortDoneTerminalConsumer.protocol hpsi hwidth hle kappa tau).Configuration n) e e
  have sj := BirthB1CountStepReduction.step_apply
    (BirthShortDoneTerminalConsumer.protocol hpsi hwidth hle kappa tau) ring
    (physicalProj C : (BirthShortDoneTerminalConsumer.protocol hpsi hwidth hle kappa tau).Configuration n)
    e (ring.rightNeighbor e)
  have he' := he.trans se
  have hj' := hj.trans sj
  simp only [if_true] at he'
  simp only [hne, if_false] at hj'
  unfold PhysicalServiceAt
  dsimp only
  exact ⟨he', hj'⟩

/-- The letter of one service, chosen by its effect on the bases. -/
noncomputable def letterOf (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) : Option (ExtLetter n) := by
  classical
  exact if PhysicalServiceAt hpsi hwidth hle ring C (stepV10e hpsi hwidth hle ring C e) e then
      some (.host e)
    else if physicalProj (stepV10e hpsi hwidth hle ring C e) = commitProj hpsi ring C e then
      some (.relabel e)
    else none

/-- The extended word of a service word. -/
noncomputable def projWord (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) : List (Fin n) → R1ConfigV6 n psi kappa tau → List (ExtLetter n)
  | [], _ => []
  | e :: w, C => (letterOf hpsi hwidth hle ring C e).toList ++
      projWord hpsi hwidth hle ring w (stepV10e hpsi hwidth hle ring C e)

/-- Number of physical services along a service word. -/
noncomputable def physCount (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) : List (Fin n) → R1ConfigV6 n psi kappa tau → Nat
  | [], _ => 0
  | e :: w, C => by
      classical
      exact (if PhysicalServiceAt hpsi hwidth hle ring C (stepV10e hpsi hwidth hle ring C e) e
          then 1 else 0) + physCount hpsi hwidth hle ring w (stepV10e hpsi hwidth hle ring C e)

theorem extRun_append (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (a b : List (ExtLetter n))
    (P : Fin n → ExpiringAgentState psi kappa tau) :
    extRun hpsi hwidth hle ring (a ++ b) P =
      extRun hpsi hwidth hle ring b (extRun hpsi hwidth hle ring a P) := by
  induction a generalizing P with
  | nil => rfl
  | cons x a ih =>
    cases x with
    | host e => exact ih _
    | relabel e => exact ih _

theorem hostCount_append (a b : List (ExtLetter n)) :
    hostCount (a ++ b) = hostCount a + hostCount b := by
  induction a with
  | nil => simp [hostCount]
  | cons x a ih =>
    cases x with
    | host e => simp [hostCount, ih]; omega
    | relabel e => simp [hostCount, ih]

/-- One leaderless safe service is correctly described by its letter. -/
theorem letter_correct (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hlead : B9SpliceV10eAssembly.Leaderless C) (hS : SpliceSafeV7 hpsi ring C) :
    physicalProj (stepV10e hpsi hwidth hle ring C e) =
      extRun hpsi hwidth hle ring (letterOf hpsi hwidth hle ring C e).toList (physicalProj C) := by
  unfold letterOf
  by_cases hp : PhysicalServiceAt hpsi hwidth hle ring C (stepV10e hpsi hwidth hle ring C e) e
  · rw [if_pos hp]
    show _ = BirthShortDoneTerminalConsumer.step hpsi hwidth hle ring (physicalProj C) e
    exact physicalService_is_hostStep hpsi hwidth hle ring C _ e hp
      (fun i hi hj => by rw [stepV10e_other hpsi hwidth hle ring C e i hi hj])
  · rw [if_neg hp]
    by_cases hc : physicalProj (stepV10e hpsi hwidth hle ring C e) = commitProj hpsi ring C e
    · rw [if_pos hc]
      show _ = relabelAt hpsi ring (physicalProj C) e
      rw [hc]; rfl
    · rw [if_neg hc]
      show _ = physicalProj C
      rcases projection_trichotomy hpsi hwidth hle ring C e hne hlead hS with h | h | h
      · exact h
      · exact absurd (physical_of_hostStep hpsi hwidth hle ring C _ e hne h) hp
      · exact absurd h.2 hc

/-- The projected word describes the leaderless V10e trajectory on the bases. -/
theorem projWord_correct (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (hn : 2 ≤ n) (w : List (Fin n)) :
    ∀ C : R1ConfigV6 n psi kappa tau,
      SpliceSafeV7 hpsi ring C → LeaderlessAlong hpsi hwidth hle ring w C →
      physicalProj (serveWord hpsi hwidth hle ring w C) =
        extRun hpsi hwidth hle ring (projWord hpsi hwidth hle ring w C) (physicalProj C) := by
  induction w with
  | nil => intro C _ _; rfl
  | cons e w ih =>
    intro C hS hl
    have hS' := B9SpliceV10eAssembly.stepV10e_preserves_spliceSafeV7_leaderless_final
      hpsi hwidth hle ring C e hl.1 hS
    show physicalProj (serveWord hpsi hwidth hle ring w (stepV10e hpsi hwidth hle ring C e)) =
      extRun hpsi hwidth hle ring ((letterOf hpsi hwidth hle ring C e).toList ++
        projWord hpsi hwidth hle ring w (stepV10e hpsi hwidth hle ring C e)) (physicalProj C)
    rw [extRun_append, ← letter_correct hpsi hwidth hle ring C e (rightNeighbor_ne_self ring hn e) hl.1 hS]
    exact ih _ hS' hl.2

/-- The host count of the projected word is the number of physical services. -/
theorem hostCount_projWord (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (w : List (Fin n)) :
    ∀ C : R1ConfigV6 n psi kappa tau,
      hostCount (projWord hpsi hwidth hle ring w C) = physCount hpsi hwidth hle ring w C := by
  induction w with
  | nil => intro C; rfl
  | cons e w ih =>
    intro C
    show hostCount ((letterOf hpsi hwidth hle ring C e).toList ++ _) = _
    rw [hostCount_append, ih]
    classical
    show hostCount (letterOf hpsi hwidth hle ring C e).toList +
        physCount hpsi hwidth hle ring w (stepV10e hpsi hwidth hle ring C e) =
      (if PhysicalServiceAt hpsi hwidth hle ring C (stepV10e hpsi hwidth hle ring C e) e then 1 else 0) +
        physCount hpsi hwidth hle ring w (stepV10e hpsi hwidth hle ring C e)
    unfold letterOf
    by_cases hp : PhysicalServiceAt hpsi hwidth hle ring C (stepV10e hpsi hwidth hle ring C e) e
    · simp [hp, hostCount]
    · by_cases hc : physicalProj (stepV10e hpsi hwidth hle ring C e) = commitProj hpsi ring C e
      · simp [hp, hc, hostCount]
      · simp [hp, hc, hostCount]

theorem physCount_append (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (a b : List (Fin n)) :
    ∀ C : R1ConfigV6 n psi kappa tau,
      physCount hpsi hwidth hle ring (a ++ b) C =
        physCount hpsi hwidth hle ring a C +
          physCount hpsi hwidth hle ring b (serveWord hpsi hwidth hle ring a C) := by
  induction a with
  | nil => intro C; simp [physCount, serveWord]
  | cons e a ih =>
    intro C
    classical
    show (if _ then 1 else 0) + physCount hpsi hwidth hle ring (a ++ b) (stepV10e hpsi hwidth hle ring C e) =
      ((if _ then 1 else 0) + physCount hpsi hwidth hle ring a (stepV10e hpsi hwidth hle ring C e)) + _
    rw [ih]
    show _ = _ + physCount hpsi hwidth hle ring b (serveWord hpsi hwidth hle ring a (stepV10e hpsi hwidth hle ring C e))
    omega

/-- A physical hit among `k` hits of `e` with far words between gives a host letter. -/
theorem physCount_hitWord_pos (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (e : Fin n) (hne : ring.rightNeighbor e ≠ e)
    (us : List (List (Fin n))) (hus : ∀ u ∈ us, ∀ f ∈ u, Far ring e f)
    (C : R1ConfigV6 n psi kappa tau) (m : Nat) (hm : m < us.length)
    (hphys : PhysicalServiceAt hpsi hwidth hle ring
      (serveIter hpsi hwidth hle ring e m C) (serveIter hpsi hwidth hle ring e (m + 1) C) e) :
    1 ≤ physCount hpsi hwidth hle ring (hitWord e us) C := by
  induction us generalizing C m with
  | nil => simp at hm
  | cons u us ih =>
    have hu : ∀ f ∈ u, Far ring e f := hus u (List.mem_cons_self ..)
    have hus' : ∀ v ∈ us, ∀ f ∈ v, Far ring e f := fun v hv => hus v (List.mem_cons_of_mem u hv)
    classical
    show 1 ≤ (if PhysicalServiceAt hpsi hwidth hle ring C (stepV10e hpsi hwidth hle ring C e) e then 1 else 0) +
      physCount hpsi hwidth hle ring (u ++ hitWord e us) (stepV10e hpsi hwidth hle ring C e)
    cases m with
    | zero =>
      have : PhysicalServiceAt hpsi hwidth hle ring C (stepV10e hpsi hwidth hle ring C e) e := hphys
      rw [if_pos this]; omega
    | succ m =>
      have hm' : m < us.length := by simp at hm; omega
      rw [physCount_append]
      -- the pair after `u` agrees with the pair after the first hit
      obtain ⟨g1, g2⟩ := serveWord_far hpsi hwidth hle ring e u hu (stepV10e hpsi hwidth hle ring C e)
      have hphys' : PhysicalServiceAt hpsi hwidth hle ring
          (serveIter hpsi hwidth hle ring e m (serveWord hpsi hwidth hle ring u (stepV10e hpsi hwidth hle ring C e)))
          (serveIter hpsi hwidth hle ring e (m + 1) (serveWord hpsi hwidth hle ring u (stepV10e hpsi hwidth hle ring C e))) e := by
        have key : ∀ (k : Nat) (D D' : R1ConfigV6 n psi kappa tau),
            D' e = D e → D' (ring.rightNeighbor e) = D (ring.rightNeighbor e) →
            serveIter hpsi hwidth hle ring e k D' e = serveIter hpsi hwidth hle ring e k D e ∧
            serveIter hpsi hwidth hle ring e k D' (ring.rightNeighbor e) =
              serveIter hpsi hwidth hle ring e k D (ring.rightNeighbor e) := by
          intro k
          induction k with
          | zero => intro D D' hl hr; exact ⟨hl, hr⟩
          | succ k ihk =>
            intro D D' hl hr
            obtain ⟨a1, a2⟩ := ihk D D' hl hr
            exact step_pair_of_pair hpsi hwidth hle ring _ _ e hne a1 a2
        obtain ⟨k1, k2⟩ := key m (stepV10e hpsi hwidth hle ring C e) _ g1 g2
        rw [serveIter_succ_comm hpsi hwidth hle ring e (m + 1) C,
          serveIter_succ_comm hpsi hwidth hle ring e m C] at hphys
        have hiff := physical_of_pair hpsi hwidth hle ring
          (serveIter hpsi hwidth hle ring e m (stepV10e hpsi hwidth hle ring C e))
          (serveIter hpsi hwidth hle ring e m (serveWord hpsi hwidth hle ring u (stepV10e hpsi hwidth hle ring C e)))
          e hne k1 k2
        exact hiff.2 hphys
      have := ih hus' _ m hm' hphys'
      omega

end B9SpliceV10eProjectionLetter
