import Leader.Wu.Splice.OrderedWindowMatcher
import Leader.Wu.Splice.TripleHitWords

set_option autoImplicit false

/-! # A window run is determined by the window letters

For any pair-local step on `Fin n → X` (one service changes only the served pair, and the new pair depends only on
the old pair) and a window `S` of cells: if two configurations agree on `S` and every letter of a word that touches
`S` is internal to `S`, the two runs still agree on `S` (`run_agree`).  A success word of the ordered window matcher
(`B9OrderedWindowMatcher.ordStep`, touching = sharing a cell with `S`) for a request list of internal edges has a
prefix whose run agrees on `S` with the run of the request list itself (`success_prefix_agrees`).  So a local success
word of internal edges is realised on the ring by every matcher success word. -/

namespace B6WindowLocality

open FiniteUniformStoppingTree ThreePortSerialCount B9SpliceTripleHitWords B9OrderedWindowMatcher

variable {n : Nat} {X : Type}

structure PairLocal (ring : DirectedRing n) (step : (Fin n → X) → Fin n → (Fin n → X)) : Prop where
  other : ∀ C e i, i ≠ e → i ≠ ring.rightNeighbor e → step C e i = C i
  pair : ∀ C D e, D e = C e → D (ring.rightNeighbor e) = C (ring.rightNeighbor e) →
    step D e e = step C e e ∧ step D e (ring.rightNeighbor e) = step C e (ring.rightNeighbor e)

def touchOf (ring : DirectedRing n) (S : Fin n → Bool) (e : Fin n) : Bool := S e || S (ring.rightNeighbor e)

def internalOf (ring : DirectedRing n) (S : Fin n → Bool) (e : Fin n) : Bool := S e && S (ring.rightNeighbor e)

theorem step_agree {ring : DirectedRing n} {step : (Fin n → X) → Fin n → (Fin n → X)} (hL : PairLocal ring step)
    (S : Fin n → Bool) (C D : Fin n → X) (hCD : ∀ i, S i = true → C i = D i) (e : Fin n)
    (he : touchOf ring S e = true → internalOf ring S e = true) :
    ∀ i, S i = true → step C e i = step D e i := by
  intro i hi
  by_cases hie : i = e
  · subst hie
    have hint := he (by simp [touchOf, hi])
    simp only [internalOf, Bool.and_eq_true] at hint
    exact ((hL.pair C D i (hCD _ hint.1).symm (hCD _ hint.2).symm).1).symm
  · by_cases hij : i = ring.rightNeighbor e
    · subst hij
      have hint := he (by simp [touchOf, hi])
      simp only [internalOf, Bool.and_eq_true] at hint
      exact ((hL.pair C D e (hCD _ hint.1).symm (hCD _ hint.2).symm).2).symm
    · rw [hL.other C e i hie hij, hL.other D e i hie hij]
      exact hCD i hi

theorem run_agree {ring : DirectedRing n} {step : (Fin n → X) → Fin n → (Fin n → X)} (hL : PairLocal ring step)
    (S : Fin n → Bool) :
    ∀ (w : List (Fin n)) (C D : Fin n → X), (∀ i, S i = true → C i = D i) →
      (∀ e ∈ w, touchOf ring S e = true → internalOf ring S e = true) →
      ∀ i, S i = true → w.foldl step C i = w.foldl step D i
  | [], _, _, hCD, _ => hCD
  | e :: w, C, D, hCD, hw => by
      apply run_agree hL S w (step C e) (step D e)
      · exact step_agree hL S C D hCD e (hw e List.mem_cons_self)
      · exact fun f hf => hw f (List.mem_cons_of_mem e hf)

theorem run_far {ring : DirectedRing n} {step : (Fin n → X) → Fin n → (Fin n → X)} (hL : PairLocal ring step)
    (S : Fin n → Bool) :
    ∀ (w : List (Fin n)) (C : Fin n → X), (∀ e ∈ w, touchOf ring S e = false) →
      ∀ i, S i = true → w.foldl step C i = C i
  | [], _, _ => fun _ _ => rfl
  | e :: w, C, hw => by
      intro i hi
      have he := hw e List.mem_cons_self
      have ih := run_far hL S w (step C e) (fun f hf => hw f (List.mem_cons_of_mem e hf)) i hi
      show w.foldl step (step C e) i = C i
      rw [ih]
      simp only [touchOf, Bool.or_eq_false_iff] at he
      apply hL.other C e i
      · intro h; subst h; rw [hi] at he; exact absurd he.1 (by decide)
      · intro h; subst h; rw [hi] at he; exact absurd he.2 (by decide)

/-! ## Success words of the ordered matcher -/

theorem ord_shape (touch : Fin n → Bool) (a : Fin n) (rest : List (Fin n)) :
    ∀ (w : List (Fin n)), runNode (ordStep touch) (.active (a :: rest)) w = .success →
      ∃ u r, w = u ++ a :: r ∧ (∀ f ∈ u, touch f = false) ∧
        (rest = [] ∨ runNode (ordStep touch) (.active rest) r = .success)
  | [], h => by cases h
  | f :: w, h => by
      by_cases hfa : f = a
      · subst hfa
        refine ⟨[], w, rfl, fun _ h => absurd h List.not_mem_nil, ?_⟩
        cases rest with
        | nil => exact Or.inl rfl
        | cons b rest =>
            right
            have e1 : ordStep touch (f :: b :: rest) f = .active (b :: rest) := by
              unfold ordStep; simp
            show runNode (ordStep touch) (.active (b :: rest)) w = .success
            rw [← e1]; exact h
      · by_cases ht : touch f = true
        · exfalso
          have e1 : ordStep touch (a :: rest) f = .failure := by
            unfold ordStep; simp [hfa, ht]
          have : runNode (ordStep touch) (.active (a :: rest)) (f :: w) = .failure := by
            show runNode (ordStep touch) (ordStep touch (a :: rest) f) w = .failure
            rw [e1, runNode_failure]
          rw [this] at h; cases h
        · have e1 : ordStep touch (a :: rest) f = .active (a :: rest) := by
            unfold ordStep; simp [hfa, ht]
          have h' : runNode (ordStep touch) (.active (a :: rest)) w = .success := by
            have : runNode (ordStep touch) (.active (a :: rest)) (f :: w) =
                runNode (ordStep touch) (.active (a :: rest)) w := by
              show runNode (ordStep touch) (ordStep touch (a :: rest) f) w = _
              rw [e1]
            rw [← this]; exact h
          obtain ⟨u, r, hw, hu, hr⟩ := ord_shape touch a rest w h'
          refine ⟨f :: u, r, by rw [hw]; rfl, ?_, hr⟩
          intro g hg
          rcases List.mem_cons.1 hg with hg | hg
          · subst hg; simpa using ht
          · exact hu g hg

theorem success_prefix_agrees {ring : DirectedRing n} {step : (Fin n → X) → Fin n → (Fin n → X)}
    (hL : PairLocal ring step) (S : Fin n → Bool) :
    ∀ (req : List (Fin n)), req ≠ [] → (∀ a ∈ req, internalOf ring S a = true) →
      ∀ (w : List (Fin n)), runNode (ordStep (touchOf ring S)) (.active req) w = .success →
        ∀ C : Fin n → X, ∃ p : List (Fin n), p <+: w ∧
          ∀ i, S i = true → p.foldl step C i = req.foldl step C i
  | [], h, _, _, _, _ => absurd rfl h
  | a :: rest, _, hreq, w, hw, C => by
      obtain ⟨u, r, hwu, hu, hr⟩ := ord_shape (touchOf ring S) a rest w hw
      have ha := hreq a List.mem_cons_self
      -- after u ++ [a], the window agrees with one service of a
      have hfar := run_far hL S u C hu
      have hstep : ∀ i, S i = true → (u ++ [a]).foldl step C i = step C a i := by
        intro i hi
        rw [List.foldl_append]
        show step (u.foldl step C) a i = step C a i
        exact step_agree hL S (u.foldl step C) C (fun j hj => hfar j hj) a (fun _ => ha) i hi
      by_cases hrest : rest = []
      · subst hrest
        refine ⟨u ++ [a], ⟨r, by rw [hwu]; simp⟩, ?_⟩
        intro i hi
        rw [hstep i hi]; rfl
      · have hsucc := hr.resolve_left hrest
        obtain ⟨p, ⟨t, ht⟩, hp⟩ := success_prefix_agrees hL S rest hrest
          (fun x hx => hreq x (List.mem_cons_of_mem a hx)) r hsucc ((u ++ [a]).foldl step C)
        refine ⟨u ++ [a] ++ p, ⟨t, by rw [hwu, List.append_assoc, List.append_assoc, ht]; simp⟩, ?_⟩
        intro i hi
        rw [List.foldl_append, hp i hi]
        show rest.foldl step ((u ++ [a]).foldl step C) i = rest.foldl step (step C a) i
        exact run_agree hL S rest _ _ (fun j hj => hstep j hj)
          (fun x hx _ => hreq x (List.mem_cons_of_mem a hx)) i hi

end B6WindowLocality
