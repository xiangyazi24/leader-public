import Leader.Wu.Splice.MatcherMass

set_option autoImplicit false
set_option Elab.async false

/-! # Progress mass for any served-pair-local controller step

The leaderless chain `B9SpliceV10eProjectionLetter` / `B9SpliceV10ePairWeight` / `B9SpliceTripleHitWords` /
`B9SpliceMatcherMass` is stated for `stepV10e`, but it only uses that one service of edge `e` changes nothing
outside `{e, e+1}` and that the new served pair depends only on the old one (`LocalStepG`).  This file proves
the chain for every such step: from a three-service progress statement at some edge (`ProgressWithin3G`), at
least a 1/64 fraction of the `n^(6n)` scheduler words of length `6n` contain a physical service or drop that
edge's pair weight at some prefix (`progress_massG`). -/

namespace B9SpliceLocalStepMass

open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV6
  B9SpliceV10eTransparency B9SpliceV10eProjectionLetter B9SpliceV10ePairWeight
  B9SpliceTripleHitBridge B9SpliceTripleHitWords B9SpliceMatcherMass
  FiniteUniformStoppingTree FixedSpanRenewalPayload ThreePortSerialCount

variable {n psi width kappa tau : Nat}

/-- One service of `e` changes only the served pair, and the new pair depends only on the old one. -/
structure LocalStepG (ring : DirectedRing n)
    (step : R1ConfigV6 n psi kappa tau → Fin n → R1ConfigV6 n psi kappa tau) : Prop where
  other : ∀ C e i, i ≠ e → i ≠ ring.rightNeighbor e → step C e i = C i
  pair : ∀ C C' e, C' e = C e → C' (ring.rightNeighbor e) = C (ring.rightNeighbor e) →
    step C' e e = step C e e ∧ step C' e (ring.rightNeighbor e) = step C e (ring.rightNeighbor e)

section Generic

variable (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (ring : DirectedRing n)
  (step : R1ConfigV6 n psi kappa tau → Fin n → R1ConfigV6 n psi kappa tau)

def serveWordG : List (Fin n) → R1ConfigV6 n psi kappa tau → R1ConfigV6 n psi kappa tau
  | [], C => C
  | f :: w, C => serveWordG w (step C f)

def serveIterG (e : Fin n) : Nat → R1ConfigV6 n psi kappa tau → R1ConfigV6 n psi kappa tau
  | 0, C => C
  | m + 1, C => step (serveIterG e m C) e

noncomputable def physCountG : List (Fin n) → R1ConfigV6 n psi kappa tau → Nat
  | [], _ => 0
  | f :: w, C => by
      classical
      exact (if PhysicalServiceAt hpsi hwidth hle ring C (step C f) f then 1 else 0) + physCountG w (step C f)

/-- Three-service progress at some edge, in pair-weight form. -/
def ProgressWithin3G (C : R1ConfigV6 n psi kappa tau) : Prop :=
  ∃ e : Fin n, ∃ m, m < 3 ∧
    (PhysicalServiceAt hpsi hwidth hle ring (serveIterG step e m C) (serveIterG step e (m + 1) C) e ∨
      pairWeight ring (serveIterG step e (m + 1) C) e < pairWeight ring C e)

noncomputable def progressBitG (C : R1ConfigV6 n psi kappa tau) (e : Fin n) (u : List (Fin n)) : Nat := by
  classical
  exact if (1 ≤ physCountG hpsi hwidth hle ring step u C ∨
      ∃ w' : List (Fin n), w' <+: u ∧ pairWeight ring (serveWordG step w' C) e < pairWeight ring C e)
    then 1 else 0

end Generic

variable {hpsi : 0 < psi} {hwidth : 0 < width} {hle : width ≤ psi} {ring : DirectedRing n}
  {step : R1ConfigV6 n psi kappa tau → Fin n → R1ConfigV6 n psi kappa tau}

theorem serveWordG_append (a b : List (Fin n)) (C : R1ConfigV6 n psi kappa tau) :
    serveWordG step (a ++ b) C = serveWordG step b (serveWordG step a C) := by
  induction a generalizing C with
  | nil => rfl
  | cons f a ih => exact ih _

theorem serveIterG_succ_comm (e : Fin n) (k : Nat) (C : R1ConfigV6 n psi kappa tau) :
    serveIterG step e (k + 1) C = serveIterG step e k (step C e) := by
  induction k generalizing C with
  | zero => rfl
  | succ k ih =>
    show step (serveIterG step e (k + 1) C) e = _
    rw [ih]
    rfl

theorem serveIterG_other (hL : LocalStepG ring step) (e : Fin n) (m : Nat) (C : R1ConfigV6 n psi kappa tau)
    (i : Fin n) (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) : serveIterG step e m C i = C i := by
  induction m with
  | zero => rfl
  | succ m ih =>
    show step (serveIterG step e m C) e i = C i
    rw [hL.other _ e i hi hj, ih]

theorem serveIterG_pair_of_pair (hL : LocalStepG ring step) (e : Fin n) (k : Nat)
    (D D' : R1ConfigV6 n psi kappa tau) (hl : D' e = D e) (hr : D' (ring.rightNeighbor e) = D (ring.rightNeighbor e)) :
    serveIterG step e k D' e = serveIterG step e k D e ∧
    serveIterG step e k D' (ring.rightNeighbor e) = serveIterG step e k D (ring.rightNeighbor e) := by
  induction k with
  | zero => exact ⟨hl, hr⟩
  | succ k ih =>
    obtain ⟨a1, a2⟩ := ih
    exact hL.pair _ _ e a1 a2

theorem physical_of_pairG (hL : LocalStepG ring step) (C C' : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hl : C' e = C e) (hr : C' (ring.rightNeighbor e) = C (ring.rightNeighbor e)) :
    PhysicalServiceAt hpsi hwidth hle ring C' (step C' e) e ↔ PhysicalServiceAt hpsi hwidth hle ring C (step C e) e := by
  obtain ⟨h1, h2⟩ := hL.pair C C' e hl hr
  unfold PhysicalServiceAt
  dsimp only
  rw [h1, h2, hl, hr]

theorem step_far_leftG (hL : LocalStepG ring step) (C : R1ConfigV6 n psi kappa tau) (e f : Fin n)
    (hf : Far ring e f) : step C f e = C e := by
  apply hL.other C f e (Ne.symm hf.1)
  intro h
  apply hf.2.1
  apply B9OrphanToFence.rightNeighbor_inj ring
  rw [← h, B9SpliceV10eGlobalProgress.rightNeighbor_leftNeighbor]

theorem step_far_rightG (hL : LocalStepG ring step) (C : R1ConfigV6 n psi kappa tau) (e f : Fin n)
    (hf : Far ring e f) : step C f (ring.rightNeighbor e) = C (ring.rightNeighbor e) := by
  apply hL.other C f _ (Ne.symm hf.2.2)
  intro h
  apply hf.1
  exact B9OrphanToFence.rightNeighbor_inj ring h.symm

theorem serveWordG_far (hL : LocalStepG ring step) (e : Fin n) (u : List (Fin n)) (hu : ∀ f ∈ u, Far ring e f) :
    ∀ C : R1ConfigV6 n psi kappa tau,
      serveWordG step u C e = C e ∧ serveWordG step u C (ring.rightNeighbor e) = C (ring.rightNeighbor e) := by
  induction u with
  | nil => intro C; exact ⟨rfl, rfl⟩
  | cons f u ih =>
    intro C
    have hf : Far ring e f := hu f (List.mem_cons_self ..)
    have hu' : ∀ g ∈ u, Far ring e g := fun g hg => hu g (List.mem_cons_of_mem f hg)
    obtain ⟨h1, h2⟩ := ih hu' (step C f)
    show serveWordG step u (step C f) e = C e ∧ serveWordG step u (step C f) (ring.rightNeighbor e) = C (ring.rightNeighbor e)
    rw [h1, h2, step_far_leftG hL C e f hf, step_far_rightG hL C e f hf]
    exact ⟨rfl, rfl⟩

theorem hitWord_pairG (hL : LocalStepG ring step) (e : Fin n)
    (us : List (List (Fin n))) (hus : ∀ u ∈ us, ∀ f ∈ u, Far ring e f) :
    ∀ C : R1ConfigV6 n psi kappa tau,
      serveWordG step (hitWord e us) C e = serveIterG step e us.length C e ∧
      serveWordG step (hitWord e us) C (ring.rightNeighbor e) = serveIterG step e us.length C (ring.rightNeighbor e) := by
  induction us with
  | nil => intro C; exact ⟨rfl, rfl⟩
  | cons u us ih =>
    intro C
    have hu : ∀ f ∈ u, Far ring e f := hus u (List.mem_cons_self ..)
    have hus' : ∀ v ∈ us, ∀ f ∈ v, Far ring e f := fun v hv => hus v (List.mem_cons_of_mem u hv)
    show serveWordG step (u ++ hitWord e us) (step C e) e = serveIterG step e (us.length + 1) C e ∧
      serveWordG step (u ++ hitWord e us) (step C e) (ring.rightNeighbor e) =
        serveIterG step e (us.length + 1) C (ring.rightNeighbor e)
    rw [serveWordG_append]
    obtain ⟨h1, h2⟩ := ih hus' (serveWordG step u (step C e))
    rw [h1, h2]
    obtain ⟨g1, g2⟩ := serveWordG_far hL e u hu (step C e)
    obtain ⟨k1, k2⟩ := serveIterG_pair_of_pair hL e us.length (step C e) _ g1 g2
    rw [k1, k2, serveIterG_succ_comm]
    exact ⟨rfl, rfl⟩

theorem physCountG_append (a b : List (Fin n)) :
    ∀ C : R1ConfigV6 n psi kappa tau,
      physCountG hpsi hwidth hle ring step (a ++ b) C =
        physCountG hpsi hwidth hle ring step a C + physCountG hpsi hwidth hle ring step b (serveWordG step a C) := by
  induction a with
  | nil => intro C; simp [physCountG, serveWordG]
  | cons f a ih =>
    intro C
    classical
    show (if _ then 1 else 0) + physCountG hpsi hwidth hle ring step (a ++ b) (step C f) =
      ((if _ then 1 else 0) + physCountG hpsi hwidth hle ring step a (step C f)) + _
    rw [ih]
    show _ = _ + physCountG hpsi hwidth hle ring step b (serveWordG step a (step C f))
    omega

theorem physCountG_hitWord_pos (hL : LocalStepG ring step) (e : Fin n)
    (us : List (List (Fin n))) (hus : ∀ u ∈ us, ∀ f ∈ u, Far ring e f)
    (C : R1ConfigV6 n psi kappa tau) (m : Nat) (hm : m < us.length)
    (hphys : PhysicalServiceAt hpsi hwidth hle ring (serveIterG step e m C) (serveIterG step e (m + 1) C) e) :
    1 ≤ physCountG hpsi hwidth hle ring step (hitWord e us) C := by
  induction us generalizing C m with
  | nil => simp at hm
  | cons u us ih =>
    have hu : ∀ f ∈ u, Far ring e f := hus u (List.mem_cons_self ..)
    have hus' : ∀ v ∈ us, ∀ f ∈ v, Far ring e f := fun v hv => hus v (List.mem_cons_of_mem u hv)
    classical
    show 1 ≤ (if PhysicalServiceAt hpsi hwidth hle ring C (step C e) e then 1 else 0) +
      physCountG hpsi hwidth hle ring step (u ++ hitWord e us) (step C e)
    cases m with
    | zero =>
      have : PhysicalServiceAt hpsi hwidth hle ring C (step C e) e := hphys
      rw [if_pos this]; omega
    | succ m =>
      have hm' : m < us.length := by simp at hm; omega
      rw [physCountG_append]
      obtain ⟨g1, g2⟩ := serveWordG_far hL e u hu (step C e)
      have hphys' : PhysicalServiceAt hpsi hwidth hle ring
          (serveIterG step e m (serveWordG step u (step C e)))
          (serveIterG step e (m + 1) (serveWordG step u (step C e))) e := by
        obtain ⟨k1, k2⟩ := serveIterG_pair_of_pair hL e m (step C e) _ g1 g2
        rw [serveIterG_succ_comm e (m + 1) C, serveIterG_succ_comm e m C] at hphys
        have hiff := physical_of_pairG (hpsi := hpsi) (hwidth := hwidth) (hle := hle) hL
          (serveIterG step e m (step C e)) (serveIterG step e m (serveWordG step u (step C e))) e k1 k2
        exact hiff.2 hphys
      have := ih hus' _ m hm' hphys'
      omega

theorem hitWord_pairWeightG (hL : LocalStepG ring step) (e : Fin n)
    (us : List (List (Fin n))) (hus : ∀ u ∈ us, ∀ f ∈ u, Far ring e f) (C : R1ConfigV6 n psi kappa tau) :
    pairWeight ring (serveWordG step (hitWord e us) C) e = pairWeight ring (serveIterG step e us.length C) e := by
  obtain ⟨h1, h2⟩ := hitWord_pairG hL e us hus C
  unfold pairWeight
  rw [h1, h2]

theorem physCountG_prefix_le (a b : List (Fin n)) (C : R1ConfigV6 n psi kappa tau) :
    physCountG hpsi hwidth hle ring step a C ≤ physCountG hpsi hwidth hle ring step (a ++ b) C := by
  rw [physCountG_append]; omega

theorem matcher_success_progressG (hL : LocalStepG ring step) (hn : 3 ≤ n) (C : R1ConfigV6 n psi kappa tau)
    (e : Fin n) (hprog : ∃ m, m < 3 ∧
      (PhysicalServiceAt hpsi hwidth hle ring (serveIterG step e m C) (serveIterG step e (m + 1) C) e ∨
        pairWeight ring (serveIterG step e (m + 1) C) e < pairWeight ring C e)) :
    ∀ w : List (Fin n),
      runNode (tripleStep (ports ring hn e)) (.active .zero) w = .success →
      1 ≤ physCountG hpsi hwidth hle ring step w C ∨
      ∃ w' : List (Fin n), w' <+: w ∧ pairWeight ring (serveWordG step w' C) e < pairWeight ring C e := by
  obtain ⟨m, hm, h⟩ := hprog
  intro w hw
  obtain ⟨u0, u1, u2, rest, hshape, hu0, hu1, hu2⟩ := success_shape (ports ring hn e) w hw
  have hword : w = u0 ++ (hitWord e [u1, u2, []] ++ rest) := by
    rw [hshape]; simp [hitWord, ports]
  obtain ⟨g1, g2⟩ := serveWordG_far hL e u0 hu0 C
  have hus : ∀ u ∈ [u1, u2, []], ∀ f ∈ u, Far ring e f := by
    intro u hu f hf
    rcases List.mem_cons.1 hu with h1 | hu
    · subst h1; exact hu1 f hf
    rcases List.mem_cons.1 hu with h2 | hu
    · subst h2; exact hu2 f hf
    rcases List.mem_cons.1 hu with h3 | hu
    · subst h3; exact absurd hf List.not_mem_nil
    · exact absurd hu List.not_mem_nil
  rcases h with hphys | hdrop
  · left
    have hphys0 : PhysicalServiceAt hpsi hwidth hle ring
        (serveIterG step e m (serveWordG step u0 C)) (serveIterG step e (m + 1) (serveWordG step u0 C)) e := by
      obtain ⟨k1, k2⟩ := serveIterG_pair_of_pair hL e m C (serveWordG step u0 C) g1 g2
      exact (physical_of_pairG hL (serveIterG step e m C) (serveIterG step e m (serveWordG step u0 C)) e k1 k2).2 hphys
    have h1 := physCountG_hitWord_pos hL e [u1, u2, []] hus (serveWordG step u0 C) m (by simp; omega) hphys0
    rw [hword, physCountG_append]
    have h2 := physCountG_prefix_le (hpsi := hpsi) (hwidth := hwidth) (hle := hle) (ring := ring) (step := step)
      (hitWord e [u1, u2, []]) rest (serveWordG step u0 C)
    omega
  · right
    refine ⟨u0 ++ hitWord e ([u1, u2, []].take (m + 1)), ?_, ?_⟩
    · rw [hword]
      refine ⟨(hitWord e ([u1, u2, []].drop (m + 1)) ++ rest), ?_⟩
      rw [List.append_assoc, ← List.append_assoc (hitWord e _) (hitWord e _) rest, ← hitWord_append,
        List.take_append_drop]
    · rw [serveWordG_append]
      have htake : ∀ u ∈ [u1, u2, []].take (m + 1), ∀ f ∈ u, Far ring e f :=
        fun u hu => hus u (List.mem_of_mem_take hu)
      rw [hitWord_pairWeightG hL e _ htake (serveWordG step u0 C)]
      have hl : ([u1, u2, []].take (m + 1)).length = m + 1 := by
        rw [List.length_take]; simp; omega
      rw [hl]
      have hpw : pairWeight ring (serveWordG step u0 C) e = pairWeight ring C e := by
        unfold pairWeight; rw [g1, g2]
      obtain ⟨k1, k2⟩ := serveIterG_pair_of_pair hL e (m + 1) C (serveWordG step u0 C) g1 g2
      have hpw2 : pairWeight ring (serveIterG step e (m + 1) (serveWordG step u0 C)) e =
          pairWeight ring (serveIterG step e (m + 1) C) e := by
        unfold pairWeight; rw [k1, k2]
      rw [hpw2]
      exact hdrop

theorem progress_massG (hL : LocalStepG ring step) (hn : 3 ≤ n) (C : R1ConfigV6 n psi kappa tau)
    (hprog : ProgressWithin3G hpsi hwidth hle ring step C) :
    ∃ e : Fin n, n ^ (6 * n) ≤ 64 * wordSum n (6 * n) (progressBitG hpsi hwidth hle ring step C e) := by
  obtain ⟨e, he⟩ := hprog
  have hsucc := matcher_success_progressG hL hn C e he
  refine ⟨e, ?_⟩
  have h64 := triple_sixty_fourth (ports ring hn e) hn
  rw [← wordSum_success_eq_successCount] at h64
  have hmono : wordSum n (6 * n)
      (fun u => successWeight (runStopped (tripleStep (ports ring hn e)) (.active .zero) u)) ≤
      wordSum n (6 * n) (progressBitG hpsi hwidth hle ring step C e) := by
    apply wordSum_mono
    intro u
    unfold progressBitG
    by_cases hs : runStopped (tripleStep (ports ring hn e)) (.active .zero) u = .success
    · have hg := hsucc u (by rw [runNode_eq_runStopped]; exact hs)
      rw [hs, if_pos hg]
      exact Nat.le_refl 1
    · have : successWeight (runStopped (tripleStep (ports ring hn e)) (.active .zero) u) = 0 := by
        cases hr : runStopped (tripleStep (ports ring hn e)) (.active .zero) u with
        | active s => rfl
        | success => exact absurd hr hs
        | failure => rfl
      rw [this]
      exact Nat.zero_le _
  omega

end B9SpliceLocalStepMass
