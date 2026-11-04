import Leader.Wu.Splice.TripleHitCount
import Leader.Wu.Splice.PhysicalHoldPairWeight

set_option autoImplicit false

/-! # Success words of the three-hit matcher are hit words with far services between

A scheduler word absorbed in success by `tripleStep p` has the shape
`u0 a u1 a u2 a rest` with `u0, u1, u2` avoiding all three ports.  With `a = e`,
`b = leftNeighbor e`, `c = rightNeighbor e` the avoided letters are exactly the edges far from
`e`, so the window progress theorem applies: every success word of the matcher for the chosen
edge contains a physical service or a strict pair-weight drop at some prefix. -/

namespace B9SpliceTripleHitWords

open FiniteUniformStoppingTree ThreePortSerialCount B9SpliceTripleHitBridge
open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV6
  B9SpliceControllerR1TableV7 B9SpliceTableV10e B9SpliceV10eTransparency
  B9SpliceV10eWordProjection B9SpliceV10eProjectionLetter B9SpliceV10eGlobalProgress
  B9SpliceV10ePairWeight

variable {n psi width kappa tau : Nat}

/-- Run the absorbing transition along a word. -/
def runNode {S : Type} (step : S → Fin n → StopNode S) : StopNode S → List (Fin n) → StopNode S
  | x, [] => x
  | x, e :: w => runNode step (stepNode step x e) w

theorem runNode_success {S : Type} (step : S → Fin n → StopNode S) (w : List (Fin n)) :
    runNode step .success w = .success := by
  induction w with
  | nil => rfl
  | cons e w ih => exact ih

theorem runNode_failure {S : Type} (step : S → Fin n → StopNode S) (w : List (Fin n)) :
    runNode step .failure w = .failure := by
  induction w with
  | nil => rfl
  | cons e w ih => exact ih

/-- Letters that keep the matcher waiting. -/
def Avoids (p : Ports n) (f : Fin n) : Prop := f ≠ p.a ∧ f ≠ p.b ∧ f ≠ p.c

theorem tripleStep_wait (p : Ports n) (s : Hits) (f : Fin n) (hf : Avoids p f) :
    tripleStep p s f = .active s := by
  cases s <;> simp [tripleStep, hf.1, hf.2.1, hf.2.2]

theorem tripleStep_bad (p : Ports n) (s : Hits) (f : Fin n) (hf : f = p.b ∨ f = p.c) :
    tripleStep p s f = .failure := by
  rcases hf with hf | hf
  · subst hf; cases s <;> simp [tripleStep, p.ab.symm]
  · subst hf; cases s <;> simp [tripleStep, p.ac.symm, p.bc.symm]

/-- From `two`, success needs one more hit of `a` after waiting letters. -/
theorem shape_two (p : Ports n) (w : List (Fin n))
    (h : runNode (tripleStep p) (.active .two) w = .success) :
    ∃ u rest, w = u ++ p.a :: rest ∧ ∀ f ∈ u, Avoids p f := by
  induction w with
  | nil => cases h
  | cons f w ih =>
    by_cases hfa : f = p.a
    · subst hfa; exact ⟨[], w, rfl, fun _ h => absurd h (List.not_mem_nil)⟩
    · by_cases hfb : f = p.b ∨ f = p.c
      · exfalso
        have : runNode (tripleStep p) (.active .two) (f :: w) = .failure := by
          show runNode (tripleStep p) (tripleStep p .two f) w = .failure
          rw [tripleStep_bad p .two f hfb, runNode_failure]
        rw [this] at h; cases h
      · have hav : Avoids p f := ⟨hfa, fun h1 => hfb (Or.inl h1), fun h2 => hfb (Or.inr h2)⟩
        have h' : runNode (tripleStep p) (.active .two) w = .success := by
          have : runNode (tripleStep p) (.active .two) (f :: w) =
              runNode (tripleStep p) (.active .two) w := by
            show runNode (tripleStep p) (tripleStep p .two f) w = _
            rw [tripleStep_wait p .two f hav]
          rw [← this]; exact h
        obtain ⟨u, rest, hw, hu⟩ := ih h'
        refine ⟨f :: u, rest, by rw [hw]; rfl, ?_⟩
        intro g hg
        rcases List.mem_cons.1 hg with hg | hg
        · subst hg; exact hav
        · exact hu g hg

theorem shape_one (p : Ports n) (w : List (Fin n))
    (h : runNode (tripleStep p) (.active .one) w = .success) :
    ∃ u rest, w = u ++ p.a :: rest ∧ (∀ f ∈ u, Avoids p f) ∧
      runNode (tripleStep p) (.active .two) rest = .success := by
  induction w with
  | nil => cases h
  | cons f w ih =>
    by_cases hfa : f = p.a
    · subst hfa
      refine ⟨[], w, rfl, fun _ h => absurd h (List.not_mem_nil), ?_⟩
      have : runNode (tripleStep p) (.active .one) (p.a :: w) =
          runNode (tripleStep p) (.active .two) w := by
        show runNode (tripleStep p) (tripleStep p .one p.a) w = _
        simp [tripleStep]
      rw [← this]; exact h
    · by_cases hfb : f = p.b ∨ f = p.c
      · exfalso
        have : runNode (tripleStep p) (.active .one) (f :: w) = .failure := by
          show runNode (tripleStep p) (tripleStep p .one f) w = .failure
          rw [tripleStep_bad p .one f hfb, runNode_failure]
        rw [this] at h; cases h
      · have hav : Avoids p f := ⟨hfa, fun h1 => hfb (Or.inl h1), fun h2 => hfb (Or.inr h2)⟩
        have h' : runNode (tripleStep p) (.active .one) w = .success := by
          have : runNode (tripleStep p) (.active .one) (f :: w) =
              runNode (tripleStep p) (.active .one) w := by
            show runNode (tripleStep p) (tripleStep p .one f) w = _
            rw [tripleStep_wait p .one f hav]
          rw [← this]; exact h
        obtain ⟨u, rest, hw, hu, hr⟩ := ih h'
        refine ⟨f :: u, rest, by rw [hw]; rfl, ?_, hr⟩
        intro g hg
        rcases List.mem_cons.1 hg with hg | hg
        · subst hg; exact hav
        · exact hu g hg

theorem shape_zero (p : Ports n) (w : List (Fin n))
    (h : runNode (tripleStep p) (.active .zero) w = .success) :
    ∃ u rest, w = u ++ p.a :: rest ∧ (∀ f ∈ u, Avoids p f) ∧
      runNode (tripleStep p) (.active .one) rest = .success := by
  induction w with
  | nil => cases h
  | cons f w ih =>
    by_cases hfa : f = p.a
    · subst hfa
      refine ⟨[], w, rfl, fun _ h => absurd h (List.not_mem_nil), ?_⟩
      have : runNode (tripleStep p) (.active .zero) (p.a :: w) =
          runNode (tripleStep p) (.active .one) w := by
        show runNode (tripleStep p) (tripleStep p .zero p.a) w = _
        simp [tripleStep]
      rw [← this]; exact h
    · by_cases hfb : f = p.b ∨ f = p.c
      · exfalso
        have : runNode (tripleStep p) (.active .zero) (f :: w) = .failure := by
          show runNode (tripleStep p) (tripleStep p .zero f) w = .failure
          rw [tripleStep_bad p .zero f hfb, runNode_failure]
        rw [this] at h; cases h
      · have hav : Avoids p f := ⟨hfa, fun h1 => hfb (Or.inl h1), fun h2 => hfb (Or.inr h2)⟩
        have h' : runNode (tripleStep p) (.active .zero) w = .success := by
          have : runNode (tripleStep p) (.active .zero) (f :: w) =
              runNode (tripleStep p) (.active .zero) w := by
            show runNode (tripleStep p) (tripleStep p .zero f) w = _
            rw [tripleStep_wait p .zero f hav]
          rw [← this]; exact h
        obtain ⟨u, rest, hw, hu, hr⟩ := ih h'
        refine ⟨f :: u, rest, by rw [hw]; rfl, ?_, hr⟩
        intro g hg
        rcases List.mem_cons.1 hg with hg | hg
        · subst hg; exact hav
        · exact hu g hg

/-- A success word of the matcher is `u0 a u1 a u2 a rest` with waiting words `u0 u1 u2`. -/
theorem success_shape (p : Ports n) (w : List (Fin n))
    (h : runNode (tripleStep p) (.active .zero) w = .success) :
    ∃ u0 u1 u2 rest, w = u0 ++ p.a :: (u1 ++ p.a :: (u2 ++ p.a :: rest)) ∧
      (∀ f ∈ u0, Avoids p f) ∧ (∀ f ∈ u1, Avoids p f) ∧ (∀ f ∈ u2, Avoids p f) := by
  obtain ⟨u0, r0, hw0, hu0, h0⟩ := shape_zero p w h
  obtain ⟨u1, r1, hw1, hu1, h1⟩ := shape_one p r0 h0
  obtain ⟨u2, r2, hw2, hu2⟩ := shape_two p r1 h1
  refine ⟨u0, u1, u2, r2, ?_, hu0, hu1, hu2⟩
  rw [hw0, hw1, hw2]

/-! ## The ports of an edge -/

theorem leftNeighbor_ne_self (ring : DirectedRing n) (hn : 2 ≤ n) (e : Fin n) :
    ring.leftNeighbor e ≠ e := by
  intro h
  have := rightNeighbor_leftNeighbor ring e
  rw [h] at this
  exact rightNeighbor_ne_self ring hn e this

theorem leftNeighbor_ne_rightNeighbor (ring : DirectedRing n) (hn : 3 ≤ n) (e : Fin n) :
    ring.leftNeighbor e ≠ ring.rightNeighbor e := by
  intro h
  have h2 := rightNeighbor_leftNeighbor ring e
  rw [h] at h2
  -- rightNeighbor (rightNeighbor e) = e
  have hv := congrArg Fin.val h2
  simp only [DirectedRing.rightNeighbor] at hv
  have he := e.isLt
  by_cases h1 : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt h1] at hv
    by_cases h3 : e.val + 1 + 1 < n
    · rw [Nat.mod_eq_of_lt h3] at hv; omega
    · have : e.val + 1 + 1 = n := by omega
      rw [this, Nat.mod_self] at hv; omega
  · have : e.val + 1 = n := by omega
    rw [this, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (by omega : 1 < n)] at hv
    omega

/-- The matcher ports of edge `e`: good port `e`, bad ports the edges sharing a site with `e`. -/
def ports (ring : DirectedRing n) (hn : 3 ≤ n) (e : Fin n) : Ports n :=
  { a := e, b := ring.leftNeighbor e, c := ring.rightNeighbor e,
    ab := (leftNeighbor_ne_self ring (by omega) e).symm,
    ac := (rightNeighbor_ne_self ring (by omega) e).symm,
    bc := leftNeighbor_ne_rightNeighbor ring hn e }

theorem avoids_iff_far (ring : DirectedRing n) (hn : 3 ≤ n) (e f : Fin n) :
    Avoids (ports ring hn e) f ↔ Far ring e f := Iff.rfl

/-! ## Matcher success gives window progress -/

theorem serveIter_pair_of_pair (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (e : Fin n) (hne : ring.rightNeighbor e ≠ e) (k : Nat)
    (D D' : R1ConfigV6 n psi kappa tau)
    (hl : D' e = D e) (hr : D' (ring.rightNeighbor e) = D (ring.rightNeighbor e)) :
    serveIter hpsi hwidth hle ring e k D' e = serveIter hpsi hwidth hle ring e k D e ∧
    serveIter hpsi hwidth hle ring e k D' (ring.rightNeighbor e) =
      serveIter hpsi hwidth hle ring e k D (ring.rightNeighbor e) := by
  induction k with
  | zero => exact ⟨hl, hr⟩
  | succ k ih =>
    obtain ⟨a1, a2⟩ := ih
    exact step_pair_of_pair hpsi hwidth hle ring _ _ e hne a1 a2

theorem hitWord_append (e : Fin n) (us vs : List (List (Fin n))) :
    hitWord e (us ++ vs) = hitWord e us ++ hitWord e vs := by
  induction us with
  | nil => rfl
  | cons u us ih => simp [hitWord, ih]

theorem physCount_prefix_le (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (a b : List (Fin n)) (C : R1ConfigV6 n psi kappa tau) :
    physCount hpsi hwidth hle ring a C ≤ physCount hpsi hwidth hle ring (a ++ b) C := by
  rw [physCount_append]; omega

/-- For the chosen edge of a leaderless safe non-clear configuration, every word absorbed in
success by the three-hit matcher of that edge contains a physical service or has a prefix after
which the pair weight of the edge is strictly below its starting value. -/
theorem matcher_success_progress (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (hn : 3 ≤ n) (C : R1ConfigV6 n psi kappa tau)
    (hlead : ∀ i, (C i).carrier.splice.base.core.core.leader = false)
    (hS : SpliceSafeV7 hpsi ring C) (hclear : ¬ RolesClearV7 C) :
    ∃ e : Fin n, ∀ w : List (Fin n),
      runNode (tripleStep (ports ring hn e)) (.active .zero) w = .success →
      1 ≤ physCount hpsi hwidth hle ring w C ∨
      ∃ w' : List (Fin n), w' <+: w ∧
        pairWeight ring (serveWord hpsi hwidth hle ring w' C) e < pairWeight ring C e := by
  obtain ⟨e, m, hm, h⟩ := globalProgress_local hpsi hwidth hle ring (by omega) C hlead hS hclear
  have hne := rightNeighbor_ne_self ring (by omega) e
  refine ⟨e, fun w hw => ?_⟩
  obtain ⟨u0, u1, u2, rest, hshape, hu0, hu1, hu2⟩ := success_shape (ports ring hn e) w hw
  -- the word is u0 ++ hitWord e [u1, u2, []] ++ rest
  have hword : w = u0 ++ (hitWord e [u1, u2, []] ++ rest) := by
    rw [hshape]; simp [hitWord, ports]
  -- the pair at the start of the hit word equals the pair of C
  obtain ⟨g1, g2⟩ := serveWord_far hpsi hwidth hle ring e u0 hu0 C
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
        (serveIter hpsi hwidth hle ring e m (serveWord hpsi hwidth hle ring u0 C)) (serveIter hpsi hwidth hle ring e (m + 1) (serveWord hpsi hwidth hle ring u0 C)) e := by
      obtain ⟨k1, k2⟩ := serveIter_pair_of_pair hpsi hwidth hle ring e hne m C (serveWord hpsi hwidth hle ring u0 C) g1 g2
      exact (physical_of_pair hpsi hwidth hle ring _ _ e hne k1 k2).2 hphys
    have h1 := physCount_hitWord_pos hpsi hwidth hle ring e hne [u1, u2, []] hus (serveWord hpsi hwidth hle ring u0 C) m
      (by simp; omega) hphys0
    rw [hword, physCount_append]
    have h2 := physCount_prefix_le hpsi hwidth hle ring (hitWord e [u1, u2, []]) rest (serveWord hpsi hwidth hle ring u0 C)
    omega
  · right
    refine ⟨u0 ++ hitWord e ([u1, u2, []].take (m + 1)), ?_, ?_⟩
    · rw [hword]
      refine ⟨(hitWord e ([u1, u2, []].drop (m + 1)) ++ rest), ?_⟩
      rw [List.append_assoc, ← List.append_assoc (hitWord e _) (hitWord e _) rest, ← hitWord_append,
        List.take_append_drop]
    · rw [serveWord_append]
      have htake : ∀ u ∈ [u1, u2, []].take (m + 1), ∀ f ∈ u, Far ring e f :=
        fun u hu => hus u (List.mem_of_mem_take hu)
      rw [hitWord_pairWeight hpsi hwidth hle ring e hne _ htake (serveWord hpsi hwidth hle ring u0 C)]
      have hl : ([u1, u2, []].take (m + 1)).length = m + 1 := by
        rw [List.length_take]; simp; omega
      rw [hl]
      obtain ⟨k1, k2⟩ := serveIter_pair_of_pair hpsi hwidth hle ring e hne (m + 1) C (serveWord hpsi hwidth hle ring u0 C) g1 g2
      unfold pairWeight
      rw [k1, k2]
      exact hdrop

end B9SpliceTripleHitWords
