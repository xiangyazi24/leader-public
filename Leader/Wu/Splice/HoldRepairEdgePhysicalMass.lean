import Leader.Wu.Splice.QuadHitCount
import Leader.Wu.Splice.HoldRepairLinearRate
import Leader.Wu.Splice.HoldRepairProgressMass
import Leader.Wu.Splice.TransparentShapeClear
import Leader.Wu.Splice.HoldRepairBirthAtHostEvents

set_option autoImplicit false
set_option Elab.async false

/-! # Leaderless V10j: every edge gets a physical service with constant mass within 8n letters

`serveIterJ_within4`: from a leaderless `SpliceSafeV7g` `ShapeClear` configuration, four consecutive V10j services
of one edge contain a physical service.  While the iterates stay leaderless V10j is V10e and
`B9SpliceTransparentShapeClear.transparentWithin4_shapeClear_final` applies; if a service of the edge creates a
leader it is physical (`B9SpliceV10jBirthOnlyAtHostEvents.stepV10j_birth_needs_event`).

`edge_physical_mass`: for every edge `e` (n ≥ 3), at least `1/256` of the scheduler words of length `8n` contain a
physical V10j service of `e` itself.  A word absorbed in success by the four-hit matcher of `e`
(`B9SpliceQuadHitCount.quadStep`, good port `e`, bad ports `e-1` and `e+1`) serves `e` four times with only far
letters in between, which never touch the served pair, so the pair runs through the four iterates. -/

namespace B9SpliceV10jEdgePhysicalMass

open FiniteUniformStoppingTree ThreePortSerialCount B9SpliceTripleHitBridge B9SpliceTripleHitWords B9SpliceQuadHitCount
open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV6
  B9SpliceTableV10e B9SpliceTableV10g B9SpliceTableV10j B9SpliceV10eTransparency B9SpliceV10eProjectionLetter
  B9SpliceLocalStepMass B9SpliceV10jGlobalProgress B9SpliceV10jProgressMass B9SpliceMatcherMass
  FixedSpanRenewalPayload

variable {n psi width kappa tau : Nat}

/-! ## Shapes of four-hit success words -/

theorem quadStep_wait (p : Ports n) (s : Hits4) (f : Fin n) (hf : Avoids p f) : quadStep p s f = .active s := by
  cases s <;> simp [quadStep, hf.1, hf.2.1, hf.2.2]

theorem quadStep_bad (p : Ports n) (s : Hits4) (f : Fin n) (hf : f = p.b ∨ f = p.c) : quadStep p s f = .failure := by
  rcases hf with hf | hf
  · subst hf; cases s <;> simp [quadStep, p.ab.symm]
  · subst hf; cases s <;> simp [quadStep, p.ac.symm, p.bc.symm]

def down : Hits4 → Hits
  | .zero => .zero
  | .one => .zero
  | .two => .one
  | .three => .two

/-- From one hit on, the four-hit matcher succeeds only if the three-hit matcher does. -/
theorem quad_success_triple (p : Ports n) :
    ∀ (w : List (Fin n)) (s : Hits4), s ≠ .zero →
      runNode (quadStep p) (.active s) w = .success → runNode (tripleStep p) (.active (down s)) w = .success
  | [], _, _, h => by cases h
  | f :: w, s, hs, h => by
      by_cases hfa : f = p.a
      · subst hfa
        cases s with
        | zero => exact absurd rfl hs
        | one =>
            have h1 : runNode (quadStep p) (.active .two) w = .success := by
              have : quadStep p .one p.a = .active .two := by simp [quadStep]
              show runNode (quadStep p) (.active .two) w = .success
              rw [← this]; exact h
            show runNode (tripleStep p) (tripleStep p .zero p.a) w = .success
            rw [show tripleStep p .zero p.a = .active .one by simp [tripleStep]]
            exact quad_success_triple p w .two (by decide) h1
        | two =>
            have h1 : runNode (quadStep p) (.active .three) w = .success := by
              have : quadStep p .two p.a = .active .three := by simp [quadStep]
              show runNode (quadStep p) (.active .three) w = .success
              rw [← this]; exact h
            show runNode (tripleStep p) (tripleStep p .one p.a) w = .success
            rw [show tripleStep p .one p.a = .active .two by simp [tripleStep]]
            exact quad_success_triple p w .three (by decide) h1
        | three =>
            show runNode (tripleStep p) (tripleStep p .two p.a) w = .success
            rw [show tripleStep p .two p.a = .success by simp [tripleStep]]
            exact runNode_success _ w
      · by_cases hfb : f = p.b ∨ f = p.c
        · exfalso
          have : runNode (quadStep p) (.active s) (f :: w) = .failure := by
            show runNode (quadStep p) (quadStep p s f) w = .failure
            rw [quadStep_bad p s f hfb, runNode_failure]
          rw [this] at h; cases h
        · have hav : Avoids p f := ⟨hfa, fun h1 => hfb (Or.inl h1), fun h2 => hfb (Or.inr h2)⟩
          have h' : runNode (quadStep p) (.active s) w = .success := by
            have e1 : runNode (quadStep p) (.active s) (f :: w) = runNode (quadStep p) (.active s) w := by
              show runNode (quadStep p) (quadStep p s f) w = _
              rw [quadStep_wait p s f hav]
            rw [← e1]; exact h
          have ih := quad_success_triple p w s hs h'
          show runNode (tripleStep p) (tripleStep p (down s) f) w = .success
          rw [tripleStep_wait p (down s) f hav]
          exact ih

theorem quad_shape_zero (p : Ports n) (w : List (Fin n))
    (h : runNode (quadStep p) (.active .zero) w = .success) :
    ∃ u rest, w = u ++ p.a :: rest ∧ (∀ f ∈ u, Avoids p f) ∧
      runNode (quadStep p) (.active .one) rest = .success := by
  induction w with
  | nil => cases h
  | cons f w ih =>
    by_cases hfa : f = p.a
    · subst hfa
      refine ⟨[], w, rfl, fun _ h => absurd h (List.not_mem_nil), ?_⟩
      have : quadStep p .zero p.a = .active .one := by simp [quadStep]
      show runNode (quadStep p) (.active .one) w = .success
      rw [← this]; exact h
    · by_cases hfb : f = p.b ∨ f = p.c
      · exfalso
        have : runNode (quadStep p) (.active .zero) (f :: w) = .failure := by
          show runNode (quadStep p) (quadStep p .zero f) w = .failure
          rw [quadStep_bad p .zero f hfb, runNode_failure]
        rw [this] at h; cases h
      · have hav : Avoids p f := ⟨hfa, fun h1 => hfb (Or.inl h1), fun h2 => hfb (Or.inr h2)⟩
        have h' : runNode (quadStep p) (.active .zero) w = .success := by
          have e1 : runNode (quadStep p) (.active .zero) (f :: w) = runNode (quadStep p) (.active .zero) w := by
            show runNode (quadStep p) (quadStep p .zero f) w = _
            rw [quadStep_wait p .zero f hav]
          rw [← e1]; exact h
        obtain ⟨u, rest, hw, hu, hr⟩ := ih h'
        refine ⟨f :: u, rest, by rw [hw]; rfl, ?_, hr⟩
        intro g hg
        rcases List.mem_cons.1 hg with hg | hg
        · subst hg; exact hav
        · exact hu g hg

theorem quad_success_shape (p : Ports n) (w : List (Fin n))
    (h : runNode (quadStep p) (.active .zero) w = .success) :
    ∃ u0 u1 u2 u3 rest, w = u0 ++ p.a :: (u1 ++ p.a :: (u2 ++ p.a :: (u3 ++ p.a :: rest))) ∧
      (∀ f ∈ u0, Avoids p f) ∧ (∀ f ∈ u1, Avoids p f) ∧ (∀ f ∈ u2, Avoids p f) ∧ (∀ f ∈ u3, Avoids p f) := by
  obtain ⟨u0, r0, hw0, hu0, h0⟩ := quad_shape_zero p w h
  have h1 := quad_success_triple p r0 .one (by decide) h0
  obtain ⟨u1, u2, u3, rest, hw1, hu1, hu2, hu3⟩ := success_shape p r0 h1
  exact ⟨u0, u1, u2, u3, rest, by rw [hw0, hw1], hu0, hu1, hu2, hu3⟩

/-! ## Physical services of one edge -/

noncomputable def physEdgeJ (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (ring : DirectedRing n)
    (e : Fin n) : List (Fin n) → R1ConfigV6 n psi kappa tau → Nat
  | [], _ => 0
  | f :: w, C => by
      classical
      exact (if f = e ∧ PhysicalServiceAt hpsi hwidth hle ring C (stepV10j hpsi hwidth hle ring C f) f then 1 else 0) +
        physEdgeJ hpsi hwidth hle ring e w (stepV10j hpsi hwidth hle ring C f)

theorem physEdgeJ_append (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (ring : DirectedRing n)
    (e : Fin n) (a b : List (Fin n)) :
    ∀ C : R1ConfigV6 n psi kappa tau,
      physEdgeJ hpsi hwidth hle ring e (a ++ b) C =
        physEdgeJ hpsi hwidth hle ring e a C +
          physEdgeJ hpsi hwidth hle ring e b (serveWordG (stepV10j hpsi hwidth hle ring) a C) := by
  induction a with
  | nil => intro C; simp [physEdgeJ, serveWordG]
  | cons f a ih =>
    intro C
    classical
    show (if _ then 1 else 0) + physEdgeJ hpsi hwidth hle ring e (a ++ b) (stepV10j hpsi hwidth hle ring C f) =
      ((if _ then 1 else 0) + physEdgeJ hpsi hwidth hle ring e a (stepV10j hpsi hwidth hle ring C f)) + _
    rw [ih]
    show _ = _ + physEdgeJ hpsi hwidth hle ring e b
      (serveWordG (stepV10j hpsi hwidth hle ring) a (stepV10j hpsi hwidth hle ring C f))
    omega

theorem physEdgeJ_hitWord_pos (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (ring : DirectedRing n)
    (e : Fin n) (us : List (List (Fin n))) (hus : ∀ u ∈ us, ∀ f ∈ u, Far ring e f)
    (C : R1ConfigV6 n psi kappa tau) (m : Nat) (hm : m < us.length)
    (hphys : PhysicalServiceAt hpsi hwidth hle ring (serveIterG (stepV10j hpsi hwidth hle ring) e m C)
      (serveIterG (stepV10j hpsi hwidth hle ring) e (m + 1) C) e) :
    1 ≤ physEdgeJ hpsi hwidth hle ring e (hitWord e us) C := by
  have hL := localStep_V10j (kappa := kappa) (tau := tau) hpsi hwidth hle ring
  induction us generalizing C m with
  | nil => simp at hm
  | cons u us ih =>
    have hu : ∀ f ∈ u, Far ring e f := hus u (List.mem_cons_self ..)
    have hus' : ∀ v ∈ us, ∀ f ∈ v, Far ring e f := fun v hv => hus v (List.mem_cons_of_mem u hv)
    classical
    show 1 ≤ (if e = e ∧ PhysicalServiceAt hpsi hwidth hle ring C (stepV10j hpsi hwidth hle ring C e) e then 1 else 0) +
      physEdgeJ hpsi hwidth hle ring e (u ++ hitWord e us) (stepV10j hpsi hwidth hle ring C e)
    cases m with
    | zero =>
      have : PhysicalServiceAt hpsi hwidth hle ring C (stepV10j hpsi hwidth hle ring C e) e := hphys
      rw [if_pos ⟨rfl, this⟩]; omega
    | succ m =>
      have hm' : m < us.length := by simp at hm; omega
      rw [physEdgeJ_append]
      obtain ⟨g1, g2⟩ := serveWordG_far hL e u hu (stepV10j hpsi hwidth hle ring C e)
      have hphys' : PhysicalServiceAt hpsi hwidth hle ring
          (serveIterG (stepV10j hpsi hwidth hle ring) e m
            (serveWordG (stepV10j hpsi hwidth hle ring) u (stepV10j hpsi hwidth hle ring C e)))
          (serveIterG (stepV10j hpsi hwidth hle ring) e (m + 1)
            (serveWordG (stepV10j hpsi hwidth hle ring) u (stepV10j hpsi hwidth hle ring C e))) e := by
        obtain ⟨k1, k2⟩ := serveIterG_pair_of_pair hL e m (stepV10j hpsi hwidth hle ring C e) _ g1 g2
        rw [serveIterG_succ_comm e (m + 1) C, serveIterG_succ_comm e m C] at hphys
        have hiff := physical_of_pairG (hpsi := hpsi) (hwidth := hwidth) (hle := hle) hL
          (serveIterG (stepV10j hpsi hwidth hle ring) e m (stepV10j hpsi hwidth hle ring C e))
          (serveIterG (stepV10j hpsi hwidth hle ring) e m
            (serveWordG (stepV10j hpsi hwidth hle ring) u (stepV10j hpsi hwidth hle ring C e))) e k1 k2
        exact hiff.2 hphys
      have := ih hus' _ m hm' hphys'
      omega

/-! ## Four services of one edge contain a physical one -/

theorem first_fail (P : Nat → Prop) (h0 : P 0) :
    ∀ M, ¬ (∀ j, j ≤ M → P j) → ∃ k, k < M ∧ (∀ j, j ≤ k → P j) ∧ ¬ P (k + 1) := by
  intro M
  induction M with
  | zero =>
      intro h
      exfalso; apply h
      intro j hj
      have : j = 0 := by omega
      rw [this]; exact h0
  | succ M ih =>
      intro h
      classical
      by_cases hM : ∀ j, j ≤ M → P j
      · refine ⟨M, by omega, hM, ?_⟩
        intro hP
        apply h
        intro j hj
        by_cases hjM : j ≤ M
        · exact hM j hjM
        · have : j = M + 1 := by omega
          rw [this]; exact hP
      · obtain ⟨k, hk, hall, hn⟩ := ih hM
        exact ⟨k, by omega, hall, hn⟩

theorem iter_J_eq_V (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (ring : DirectedRing n)
    (e : Fin n) (C : R1ConfigV6 n psi kappa tau) (hS : SpliceSafeV7g hpsi ring C)
    (hSC : B9SpliceComposedEvents.ShapeClear C) :
    ∀ k, (∀ j, j < k → ∀ i, (serveIterJ hpsi hwidth hle ring e j C i).carrier.splice.base.core.core.leader = false) →
      serveIterJ hpsi hwidth hle ring e k C = serveIter hpsi hwidth hle ring e k C ∧
      B9SpliceComposedEvents.ShapeClear (serveIterJ hpsi hwidth hle ring e k C) ∧
      SpliceSafeV7g hpsi ring (serveIterJ hpsi hwidth hle ring e k C)
  | 0, _ => ⟨rfl, hSC, hS⟩
  | k + 1, h => by
      obtain ⟨heq, hsc, hs⟩ := iter_J_eq_V hpsi hwidth hle ring e C hS hSC k (fun j hj => h j (by omega))
      have hlk := h k (by omega)
      have hstep : serveIterJ hpsi hwidth hle ring e (k + 1) C =
          stepV10e hpsi hwidth hle ring (serveIterJ hpsi hwidth hle ring e k C) e :=
        B9SpliceV10jLeaderlessTransfer.stepV10j_eq_stepV10e_of_leaderless_shapeClear hpsi hwidth hle ring _ hlk hsc e
      refine ⟨?_, ?_, ?_⟩
      · rw [hstep, heq]; rfl
      · rw [hstep]
        exact B9SpliceShapeClear.stepV10e_preserves_shapeClear hpsi hwidth hle ring _ e hlk
          ((spliceSafeV7_iff_V7g_of_shapeClear hpsi ring _ hsc).2 hs) hsc
      · exact stepV10j_preserves_spliceSafeV7g hpsi hwidth hle ring _ e hs

theorem serveIterJ_within4 (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (ring : DirectedRing n)
    (hn : 2 ≤ n) (C : R1ConfigV6 n psi kappa tau) (hlead : ∀ i, (C i).carrier.splice.base.core.core.leader = false)
    (hS : SpliceSafeV7g hpsi ring C) (hSC : B9SpliceComposedEvents.ShapeClear C) (e : Fin n) :
    ∃ m, m < 4 ∧ PhysicalServiceAt hpsi hwidth hle ring (serveIterJ hpsi hwidth hle ring e m C)
      (serveIterJ hpsi hwidth hle ring e (m + 1) C) e := by
  classical
  have hne := rightNeighbor_ne_of_two_le ring hn e
  obtain ⟨m0, hm0, hphys⟩ := B9SpliceTransparentShapeClear.transparentWithin4_shapeClear_final hpsi hwidth hle ring
    C e hlead ((spliceSafeV7_iff_V7g_of_shapeClear hpsi ring C hSC).2 hS) hSC hne
  let P : Nat → Prop := fun j => ∀ i, (serveIterJ hpsi hwidth hle ring e j C i).carrier.splice.base.core.core.leader = false
  by_cases hall : ∀ j, j ≤ m0 → P j
  · have h1 := (iter_J_eq_V hpsi hwidth hle ring e C hS hSC m0 (fun j hj => hall j (by omega))).1
    have h2 := (iter_J_eq_V hpsi hwidth hle ring e C hS hSC (m0 + 1) (fun j hj => hall j (by omega))).1
    refine ⟨m0, hm0, ?_⟩
    rw [h1, h2]
    exact hphys
  · obtain ⟨k, hk, hallk, hnot⟩ := first_fail P hlead m0 hall
    have hex : ∃ i, (serveIterJ hpsi hwidth hle ring e (k + 1) C i).carrier.splice.base.core.core.leader = true := by
      apply Classical.byContradiction
      intro hno
      apply hnot
      intro i
      cases hb : (serveIterJ hpsi hwidth hle ring e (k + 1) C i).carrier.splice.base.core.core.leader
      · rfl
      · exact absurd ⟨i, hb⟩ hno
    obtain ⟨i, hi⟩ := hex
    have hbirth := B9SpliceV10jBirthOnlyAtHostEvents.stepV10j_birth_needs_event hpsi hwidth hle ring
      (serveIterJ hpsi hwidth hle ring e k C) e i (hallk k (Nat.le_refl k) i) hi
    exact ⟨k, by omega, hbirth.1⟩

/-! ## Word mass -/

noncomputable def edgeBit (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n) (u : List (Fin n)) : Nat := by
  classical
  exact if 1 ≤ physEdgeJ hpsi hwidth hle ring e u C then 1 else 0

theorem quad_success_physEdge (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (ring : DirectedRing n)
    (hn : 3 ≤ n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hprog : ∃ m, m < 4 ∧ PhysicalServiceAt hpsi hwidth hle ring (serveIterJ hpsi hwidth hle ring e m C)
      (serveIterJ hpsi hwidth hle ring e (m + 1) C) e)
    (w : List (Fin n)) (hw : runNode (quadStep (ports ring hn e)) (.active .zero) w = .success) :
    1 ≤ physEdgeJ hpsi hwidth hle ring e w C := by
  have hL := localStep_V10j (kappa := kappa) (tau := tau) hpsi hwidth hle ring
  obtain ⟨m, hm, hphys⟩ := hprog
  rw [← serveIterG_eq_serveIterJ, ← serveIterG_eq_serveIterJ] at hphys
  obtain ⟨u0, u1, u2, u3, rest, hshape, hu0, hu1, hu2, hu3⟩ := quad_success_shape (ports ring hn e) w hw
  have hword : w = u0 ++ (hitWord e [u1, u2, u3, []] ++ rest) := by
    rw [hshape]; simp [hitWord, ports]
  obtain ⟨g1, g2⟩ := serveWordG_far hL e u0 hu0 C
  have hus : ∀ u ∈ [u1, u2, u3, []], ∀ f ∈ u, Far ring e f := by
    intro u hu f hf
    rcases List.mem_cons.1 hu with h1 | hu
    · subst h1; exact hu1 f hf
    rcases List.mem_cons.1 hu with h2 | hu
    · subst h2; exact hu2 f hf
    rcases List.mem_cons.1 hu with h3 | hu
    · subst h3; exact hu3 f hf
    rcases List.mem_cons.1 hu with h4 | hu
    · subst h4; exact absurd hf List.not_mem_nil
    · exact absurd hu List.not_mem_nil
  have hphys0 : PhysicalServiceAt hpsi hwidth hle ring
      (serveIterG (stepV10j hpsi hwidth hle ring) e m (serveWordG (stepV10j hpsi hwidth hle ring) u0 C))
      (serveIterG (stepV10j hpsi hwidth hle ring) e (m + 1) (serveWordG (stepV10j hpsi hwidth hle ring) u0 C)) e := by
    obtain ⟨k1, k2⟩ := serveIterG_pair_of_pair hL e m C (serveWordG (stepV10j hpsi hwidth hle ring) u0 C) g1 g2
    exact (physical_of_pairG (hpsi := hpsi) (hwidth := hwidth) (hle := hle) hL
      (serveIterG (stepV10j hpsi hwidth hle ring) e m C)
      (serveIterG (stepV10j hpsi hwidth hle ring) e m (serveWordG (stepV10j hpsi hwidth hle ring) u0 C)) e k1 k2).2
      hphys
  have h1 := physEdgeJ_hitWord_pos hpsi hwidth hle ring e [u1, u2, u3, []] hus
    (serveWordG (stepV10j hpsi hwidth hle ring) u0 C) m (by simp; omega) hphys0
  rw [hword, physEdgeJ_append, physEdgeJ_append]
  omega

theorem edge_physical_mass (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (ring : DirectedRing n)
    (hn : 3 ≤ n) (C : R1ConfigV6 n psi kappa tau) (hlead : ∀ i, (C i).carrier.splice.base.core.core.leader = false)
    (hS : SpliceSafeV7g hpsi ring C) (hSC : B9SpliceComposedEvents.ShapeClear C) (e : Fin n) :
    n ^ (8 * n) ≤ 256 * wordSum n (8 * n) (edgeBit hpsi hwidth hle ring C e) := by
  classical
  have hprog := serveIterJ_within4 hpsi hwidth hle ring (by omega) C hlead hS hSC e
  have h256 := quad_two_fifty_sixth (ports ring hn e) hn
  rw [← wordSum_success_eq_successCount] at h256
  have hmono : wordSum n (8 * n)
      (fun u => successWeight (runStopped (quadStep (ports ring hn e)) (.active .zero) u)) ≤
      wordSum n (8 * n) (edgeBit hpsi hwidth hle ring C e) := by
    apply wordSum_mono
    intro u
    unfold edgeBit
    by_cases hs : runStopped (quadStep (ports ring hn e)) (.active .zero) u = .success
    · have hg := quad_success_physEdge hpsi hwidth hle ring hn C e hprog u (by rw [runNode_eq_runStopped]; exact hs)
      rw [hs, if_pos hg]
      exact Nat.le_refl 1
    · have : successWeight (runStopped (quadStep (ports ring hn e)) (.active .zero) u) = 0 := by
        cases hr : runStopped (quadStep (ports ring hn e)) (.active .zero) u with
        | active s => rfl
        | success => exact absurd hr hs
        | failure => rfl
      rw [this]
      exact Nat.zero_le _
  omega

end B9SpliceV10jEdgePhysicalMass
