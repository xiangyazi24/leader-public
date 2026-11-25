import Leader.L4.ReportFastKernel

namespace L4.ReportAdaptiveFibre
open Height

variable {n : Nat}

/-- The forbidden side maps to its desired corner. The partial map
represents active disjoint pairs, not a probabilistic protocol change. -/
def mergeSide (ban : Fin n→Option (Fin n)) (e : Fin n) : Fin n :=
  (ban e).getD e

structure DisjointPairs (ban : Fin n→Option (Fin n)) : Prop where
  allowed_target : ∀ e a,ban e=some a→ban a=none
  unique_source : ∀ e e' a,ban e=some a→ban e'=some a→e=e'

theorem easy_allowed (ban : Fin n→Option (Fin n)) (a : Fin n) (A : ban a=none) :
    mergeSide ban a=a := by simp [mergeSide,A]

theorem desired_hit (ban : Fin n→Option (Fin n)) (e a : Fin n) (E : ban e=some a) :
    mergeSide ban e=a := by simp [mergeSide,E]

private theorem excluded (ban : Fin n→Option (Fin n)) (F : DisjointPairs ban)
    (a b : Fin n) (A : ban a=some b) (e : Fin n) : mergeSide ban e≠a := by
  intro E
  cases B : ban e with
  | none =>
    have C : e=a := (easy_allowed ban e B).symm.trans E
    rw [C,A] at B
    cases B
  | some c =>
    have C : c=a := (desired_hit ban e c B).symm.trans E
    have K := F.allowed_target e c B
    rw [C,A] at K
    cases K

/-- The one-step multiplicity is 0 for forbidden labels, 2 for desired
ones, and 1 otherwise. In particular, only genuine first choices can
increase the adaptive word weight. -/
theorem gate_fibre (ban : Fin n→Option (Fin n)) (F : DisjointPairs ban) (a : Fin n) :
    fibre (fun _ : Unit=>mergeSide ban) () a =
      if ban a=none then (if ∃ b,ban b=some a then 2 else 1) else 0 := by
  classical
  unfold fibre
  cases A : ban a with
  | some b =>
    simp only [Option.some_ne_none,if_false]
    rw [sum_ofFn_eq _ (fun _=>0) (fun e=>by rw [if_neg (excluded ban F a b A e)]),
      sum_ofFn_const,Nat.mul_zero]
  | none =>
    simp only [if_true]
    by_cases B : ∃ b,ban b=some a
    · rw [if_pos B]
      obtain ⟨b,H⟩ := B
      have D : b≠a := by intro E; rw [E,A] at H; cases H
      have R (e : Fin n) : mergeSide ban e=a ↔ a=e ∨ b=e := by
        constructor
        · intro E
          cases C : ban e with
          | none => exact .inl (E.symm.trans (easy_allowed ban e C))
          | some c =>
            have K : c=a := (desired_hit ban e c C).symm.trans E
            rw [K] at C
            exact .inr (F.unique_source b e a H C)
        · intro E
          rcases E with E|E
          · subst e; exact easy_allowed ban a A
          · subst e; exact desired_hit ban b a H
      have E (e : Fin n) : (if mergeSide ban e=a then 1 else 0) =
          (if a=e then 1 else 0)+(if b=e then 1 else 0) := by
        by_cases U : a=e <;> by_cases V : b=e
        · exact False.elim (D (V.trans U.symm))
        · simp [(R e).mpr (.inl U),U,V]
        · simp [(R e).mpr (.inr V),U,V]
        · have K : mergeSide ban e≠a := fun E=>((R e).mp E).elim U V
          simp [K,U,V]
      rw [sum_ofFn_eq _ _ E,sum_ofFn_add,sum_delta a (fun _=>1),sum_delta b (fun _=>1)]
    · rw [if_neg B]
      have E (e : Fin n) : (if mergeSide ban e=a then 1 else 0)=(if a=e then 1 else 0) := by
        have R : mergeSide ban e=a ↔ a=e := by
          constructor
          · intro H
            cases C : ban e with
            | none => exact H.symm.trans (easy_allowed ban e C)
            | some c =>
              have K : c=a := (desired_hit ban e c C).symm.trans H
              exact False.elim (B ⟨e,K ▸ C⟩)
          · intro E
            subst e
            exact easy_allowed ban a A
        by_cases U : a=e
        · rw [if_pos (R.mpr U),if_pos U]
        · rw [if_neg (fun K=>U (R.mp K)),if_neg U]
      rw [sum_ofFn_eq _ _ E,sum_delta a (fun _=>1)]

theorem gate_fibre_two (ban : Fin n→Option (Fin n)) (F : DisjointPairs ban) (a : Fin n) :
    fibre (fun _ : Unit=>mergeSide ban) () a≤2 := by
  rw [gate_fibre ban F a]
  split
  · split <;> decide
  · decide

/-- No independence between owner advances: at a shared edge each
owner contributes its own bit. -/
theorem two_label_support (mark : Fin n→Bool) (a b : Fin n)
    (support : ∀ e,mark e=true→e=a ∨ e=b) :
    (List.ofFn (fun e=>(mark e).toNat)).sum≤2 := by
  have V (e : Fin n) : (mark e).toNat ≤ (if a=e then 1 else 0)+(if b=e then 1 else 0) := by
    cases E : mark e
    · exact Nat.zero_le _
    · rcases support e E with H|H
      · subst a; simp
      · subst b; simp
  have U := sum_ofFn_le _ _ V
  rw [sum_ofFn_add,sum_delta a (fun _=>1),sum_delta b (fun _=>1)] at U
  exact U

theorem five_two_label_support (mark : Fin 5→Fin n→Bool)
    (support : ∀ j,∃ a b,∀ e, mark j e=true→e=a ∨ e=b) :
    (List.ofFn (fun e=>(List.ofFn (fun j=>(mark j e).toNat)).sum)).sum≤10 := by
  rw [←sum_swap (fun j e=>(mark j e).toNat)]
  have R : ∀ j, (List.ofFn (fun e=>(mark j e).toNat)).sum≤2 := by
    intro j
    obtain ⟨a,b,H⟩ := support j
    exact two_label_support (mark j) a b H
  have T := sum_ofFn_le _ (fun _=>2) R
  rwa [sum_ofFn_const] at T

#print axioms gate_fibre
#print axioms gate_fibre_two
#print axioms five_two_label_support
end L4.ReportAdaptiveFibre

namespace L4.ReportFastKernel

/-- Each advance can reset one blocking credit. Without an advance a
paid blocking credit cannot reappear. The actual no-rearm fact is
supplied by the literal race/transport proof. -/
def eventRank (debt : Nat) (unspent : Bool) : Nat := 2*debt+unspent.toNat

theorem eventRank_idle {m n : Nat} {a b : Bool} (D : m≤n)
    (same : m=n→b.toNat≤a.toNat) : eventRank m b≤eventRank n a := by
  unfold eventRank
  by_cases E : m=n
  · exact Nat.add_le_add (Nat.mul_le_mul_left 2 D) (same E)
  · cases a <;> cases b <;> simp <;> omega

theorem eventRank_progress {m n : Nat} {a b : Bool}
    (D : m<n ∨ (m=n ∧ a=true ∧ b=false)) : eventRank m b<eventRank n a := by
  rcases D with D|⟨rfl,rfl,rfl⟩
  · unfold eventRank
    cases a <;> cases b <;> simp <;> omega
  · unfold eventRank
    simp

theorem eventRank_paper_bound {m t W : Nat} {a : Bool}
    (L : m≤518*t*W) (T : 0<t) (Wp : 0<W) :
    eventRank m a≤2048*t*W := by
  have P : 1≤t*W := Nat.mul_pos T Wp
  have M : 518*t*W=518*(t*W) := Nat.mul_assoc 518 t W
  have H : 2048*t*W=2048*(t*W) := Nat.mul_assoc 2048 t W
  rw [M] at L
  rw [H]
  unfold eventRank
  cases a <;> simp <;> omega

#print axioms eventRank_idle
#print axioms eventRank_progress
#print axioms eventRank_paper_bound
end L4.ReportFastKernel
