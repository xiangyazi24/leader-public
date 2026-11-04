import Leader.Wu.Elimination.GapOwnershipArcs
import Leader.Wu.ShortGap.PerGapOffPay

set_option autoImplicit false

namespace Leader.ReadSupportContact

open Leader.GapOwnershipArcs

/-!
# Closed read-support contact and ordinary-row locality

The ownership arcs in `GapOwnershipArcs` are half-open; `gapWC` also reads
the left endpoint's leader flag. Closed read arcs therefore overlap, and the
ownership-disjointness lemma is not a proof of their contact bound.

The sharp bound for an adjacent ring edge is two when every gap length is at
least two. Writing the edge as local positions `(k - 1, k)` in its owning gap
shows that at least one position is strictly interior. That interior position
belongs to only this read arc, and the other site has a two-gap cover already
containing this gap. No minimum number of gaps is required. Explicit examples
show sharpness two, failure at unit spacing, and four contacts for arbitrary
nonadjacent pairs.

`readAgree` retains full cell agreement on ownership and asks only for the
left leader flag. The imported `PhysicalBridge` is a fixed-layout interface;
its state/configuration projection is not identified with the full protocol.
`ordinaryLocality_of_readAgree` constructs the repository's actual
`PerGapOffPay.OrdinaryLocality`, and `wired_offPay` consumes its established
finite-uniform summation theorem. Geometry derives the frame and contact
bounds; `OrdinaryReadResidual.quiet` remains a rowwise protocol obligation,
including disabled gaps that read a neighbour's leader flag.

Checked against the current local `GapOwnershipArcs` and
`PerGapOffPay` declarations. The full protocol must still supply fixed-frame
identities, ordinary-state coverage, adjacent scheduling, spacing, and quiet.
Merges, relabelling, ownership transfer, and convergence are outside these
fixed-layout lemmas.
-/

/-- The clockwise neighbour, including the wrap from `n - 1` to zero. -/
def succSite {n : Nat} (hn : 0 < n) (x : Fin n) : Fin n :=
  ⟨(x.val + 1) % n, Nat.mod_lt _ hn⟩

/-- The positive lift of the successor is the unreduced coordinate `x + 1`. -/
theorem lift_succSite {n : Nat} (hn : 0 < n) (x : Fin n) :
    lift (succSite hn x) = x.val + 1 := by
  have hx := x.isLt
  exact lift_of_mod hn (x.val + 1) (by omega) (by omega)

/-- Every directed edge has consecutive local positions in one closed arc. -/
theorem adjacent_pair_in_gap {m n : Nat} (d : Fin m → Nat) (hn : 0 < n)
    (hsum : (List.ofFn d).sum = n) (x : Fin n) :
    ∃ (a : Fin m) (k : Nat), 1 ≤ k ∧ k ≤ d a ∧
      gapPos d hn a (k - 1) = x ∧ gapPos d hn a k = succSite hn x := by
  rcases support_total d hsum (succSite hn x) with ⟨a, ha⟩
  rcases (support_iff_pos d hn hsum a (succSite hn x)).mp ha with
    ⟨k, hk, hkd, hp⟩
  have ht : offset d a + k = x.val + 1 :=
    (gapPos_lift d hn hsum a k hk hkd).symm.trans
      ((congrArg lift hp).trans (lift_succSite hn x))
  refine ⟨a, k, hk, hkd, ?_, hp⟩
  apply Fin.ext
  change (offset d a + (k - 1)) % n = x.val
  have he : offset d a + (k - 1) = x.val := by omega
  rw [he]
  exact Nat.mod_eq_of_lt x.isLt

/-- A strictly interior site cannot also be another gap's left endpoint. -/
theorem interior_read_unique {m n : Nat} (d : Fin m → Nat) (hn : 0 < n)
    (hd : ∀ g, 2 ≤ d g) (hsum : (List.ofFn d).sum = n)
    (a g : Fin m) (k : Nat) (hk : 1 ≤ k) (hkd : k < d a)
    (hg : readSupport d hn g (gapPos d hn a k)) : g = a := by
  rcases hg with hg | hg
  · apply support_unique d g a (gapPos d hn a k) hg
    exact (support_iff_pos d hn hsum a _).mpr ⟨k, hk, by omega, rfl⟩
  · have ea := offset_end_le d hsum a
    have eg := offset_end_le d hsum g
    have dg := hd g
    have ba : offset d a + k < n := by omega
    have bg : offset d g < n := by omega
    have hv := congrArg Fin.val hg
    change (offset d a + k) % n = (offset d g + 0) % n at hv
    rw [Nat.add_zero, Nat.mod_eq_of_lt ba, Nat.mod_eq_of_lt bg] at hv
    by_cases hga : g = a
    · exact hga
    · have hvne : g.val ≠ a.val := fun he => hga (Fin.ext he)
      by_cases hlt : g.val < a.val
      · have hs := offset_separated d g a hlt
        omega
      · have hlt' : a.val < g.val := by omega
        have hs := offset_separated d a g hlt'
        omega

/-- No lower bound on the number of gaps is required. -/
theorem adjacent_pair_touches_le_two {m n : Nat} (d : Fin m → Nat)
    (hn : 0 < n) (hd : ∀ g, 2 ≤ d g) (hsum : (List.ofFn d).sum = n)
    (x : Fin n) :
    ∃ g1 g2 : Fin m, ∀ g,
      (readSupport d hn g x ∨ readSupport d hn g (succSite hn x)) →
        g = g1 ∨ g = g2 := by
  rcases adjacent_pair_in_gap d hn hsum x with ⟨a, k, hk, hkd, hx, hy⟩
  have haX : readSupport d hn a x :=
    (readSupport_iff_pos d hn hsum a x).mpr ⟨k - 1, by omega, hx⟩
  have haY : readSupport d hn a (succSite hn x) :=
    (readSupport_iff_pos d hn hsum a _).mpr ⟨k, hkd, hy⟩
  have hda := hd a
  by_cases hfirst : k = 1
  · have hki : k < d a := by omega
    rcases readSupport_cover d hn hd hsum x with ⟨b, c, hc⟩
    have hac : a = b ∨ a = c := hc a haX
    refine ⟨b, c, ?_⟩
    intro g hg
    rcases hg with hg | hg
    · exact hc g hg
    · have heq : g = a := interior_read_unique d hn hd hsum a g k hk hki
        (by rw [hy]; exact hg)
      exact hac.imp (fun h => heq.trans h) (fun h => heq.trans h)
  · have hki : 1 ≤ k - 1 := by omega
    have hlast : k - 1 < d a := by omega
    rcases readSupport_cover d hn hd hsum (succSite hn x) with ⟨b, c, hc⟩
    have hac : a = b ∨ a = c := hc a haY
    refine ⟨b, c, ?_⟩
    intro g hg
    rcases hg with hg | hg
    · have heq : g = a := interior_read_unique d hn hd hsum a g (k - 1) hki hlast
        (by rw [hx]; exact hg)
      exact hac.imp (fun h => heq.trans h) (fun h => heq.trans h)
    · exact hc g hg

/-- With two gap indices, even an arbitrary pair has a two-gap cover. -/
theorem two_leader_pair_touches_le_two {n : Nat} (d : Fin 2 → Nat)
    (hn : 0 < n) (x y : Fin n) :
    ∃ g1 g2 : Fin 2, ∀ g,
      (readSupport d hn g x ∨ readSupport d hn g y) → g = g1 ∨ g = g2 := by
  refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_⟩
  intro g _
  have hg := g.isLt
  by_cases h : g.val = 0
  · left
    apply Fin.ext
    exact h
  · right
    apply Fin.ext
    change g.val = 1
    omega

/-- Converts a two-witness cover into a count of actual distinct gap indices. -/
theorem countP_le_two_of_cover {m : Nat} (p : Fin m → Bool) (a b : Fin m)
    (hcover : ∀ g, p g = true → g = a ∨ g = b) :
    (List.ofFn (fun g : Fin m => g)).countP p ≤ 2 := by
  let xs := List.ofFn (fun g : Fin m => g)
  have hall : xs.Nodup := ofFn_nodup (fun g : Fin m => g) (fun _ _ h => h)
  have hfilter : (xs.filter p).Nodup :=
    List.Nodup.sublist List.filter_sublist hall
  have hsub : xs.filter p ⊆ [a, b] := by
    intro g hg
    rcases hcover g (List.mem_filter.mp hg).2 with h | h
    · exact List.mem_cons.mpr (Or.inl h)
    · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl h)))
  rw [List.countP_eq_length_filter]
  exact List.Nodup.length_le_of_subset hfilter hsub

/-- Counts distinct read arcs touched by one adjacent edge; the sharp upper bound is two. -/
theorem adjacent_pair_contact_count {m n : Nat} (d : Fin m → Nat)
    (hn : 0 < n) (hd : ∀ g, 2 ≤ d g) (hsum : (List.ofFn d).sum = n)
    (x : Fin n) :
    (List.ofFn (fun g : Fin m => g)).countP (fun g => decide
      (readSupport d hn g x ∨ readSupport d hn g (succSite hn x))) ≤ 2 := by
  rcases adjacent_pair_touches_le_two d hn hd hsum x with ⟨a, b, hc⟩
  apply countP_le_two_of_cover _ a b
  intro g hg
  apply hc g
  simpa only [decide_eq_true_eq] using hg

/-- Three length-two gaps provide a nonempty geometry attaining two contacts. -/
theorem adjacent_two_is_sharp :
    (List.ofFn (fun g : Fin 3 => g)).countP (fun g => decide
      (readSupport demoLengths (by omega : 0 < 6) g ⟨0, by omega⟩ ∨
       readSupport demoLengths (by omega : 0 < 6) g
         (succSite (by omega : 0 < 6) ⟨0, by omega⟩))) = 2 := by decide

/-- A one-gap full ring gives one contact even on its wraparound edge. -/
theorem one_gap_wrap_contact :
    let d : Fin 1 → Nat := fun _ => 4
    (∀ g, 2 ≤ d g) ∧ (List.ofFn d).sum = 4 ∧
    (List.ofFn (fun g : Fin 1 => g)).countP (fun g => decide
      (readSupport d (by decide : 0 < 4) g 3 ∨
       readSupport d (by decide : 0 < 4) g
         (succSite (by decide : 0 < 4) 3))) = 1 := by decide

/-- Two length-two gaps attain two contacts without any three-gap assumption. -/
theorem two_gap_adjacent_contacts :
    let d : Fin 2 → Nat := fun _ => 2
    (∀ g, 2 ≤ d g) ∧ (List.ofFn d).sum = 4 ∧
    (List.ofFn (fun g : Fin 2 => g)).countP (fun g => decide
      (readSupport d (by decide : 0 < 4) g 0 ∨
       readSupport d (by decide : 0 < 4) g
         (succSite (by decide : 0 < 4) 0))) = 2 := by decide

/-- Three unit gaps isolate the spacing hypothesis in the contact bound. -/
def unitLengths (_ : Fin 3) : Nat := 1

/-- An adjacent edge can touch three closed arcs when unit gaps are allowed. -/
theorem length_one_three_contacts :
    (List.ofFn unitLengths).sum = 3 ∧
    (List.ofFn (fun g : Fin 3 => g)).countP (fun g => decide
      (readSupport unitLengths (by omega : 0 < 3) g ⟨0, by omega⟩ ∨
       readSupport unitLengths (by omega : 0 < 3) g
         (succSite (by omega : 0 < 3) ⟨0, by omega⟩))) = 3 := by decide

/-- Four length-two gaps provide a separated nonadjacent-pair example. -/
def fourLengths (_ : Fin 4) : Nat := 2

/-- A nonadjacent pair can attain four contacts even with spacing at least two. -/
theorem arbitrary_pair_four_is_sharp :
    (List.ofFn fourLengths).sum = 8 ∧
    (List.ofFn (fun g : Fin 4 => g)).countP (fun g => decide
      (readSupport fourLengths (by omega : 0 < 8) g ⟨0, by omega⟩ ∨
       readSupport fourLengths (by omega : 0 < 8) g ⟨4, by omega⟩)) = 4 := by decide

/-- The exact sufficient read agreement: owned cells and the left leader flag. -/
def readAgree {m n : Nat} (d : Fin m → Nat) (hn : 0 < n) (g : Fin m)
    (C D : Fin n → Cell) : Prop :=
  (∀ x, support d g x → C x = D x) ∧
    (C (gapPos d hn g 0)).leader = (D (gapPos d hn g 0)).leader

instance {m n : Nat} (d : Fin m → Nat) (hn : 0 < n) (g : Fin m)
    (C D : Fin n → Cell) : Decidable (readAgree d hn g C D) := by
  unfold readAgree
  infer_instance

/-- The imported component potential evaluated in one fixed geometric gap. -/
def phiOf {m n : Nat} (d : Fin m → Nat) (hn : 0 < n) (g : Fin m)
    (C : Fin n → Cell) : Nat := gapWC (d g) (gapPos d hn g) C

/-- The component potential depends only on `readAgree`; use the imported locality proof. -/
theorem phi_support {m n : Nat} (d : Fin m → Nat) (hn : 0 < n)
    (hsum : (List.ofFn d).sum = n) (g : Fin m) (hdd : 1 ≤ d g)
    (C D : Fin n → Cell) (h : readAgree d hn g C D) :
    phiOf d hn g C = phiOf d hn g D :=
  gapWC_owned_plus_left d hn hsum g hdd C D h.1 h.2

theorem closed_agreement_implies_readAgree {m n : Nat} (d : Fin m → Nat)
    (hn : 0 < n) (g : Fin m) (C D : Fin n → Cell)
    (h : ∀ x, readSupport d hn g x → C x = D x) : readAgree d hn g C D :=
  ⟨fun x hx => h x (Or.inl hx), congrArg Cell.leader (h _ (Or.inr rfl))⟩

/-- Change only the excluded left bullet, leaving all leader flags unchanged. -/
def flagOnlyAfter (x : Fin 6) : Cell :=
  ⟨(demoBefore x).leader, if x.val = 0 then 1 else 0, 0⟩

/-- The excluded left cell changes its bullet, but its leader flag agrees. -/
theorem leader_flag_refinement_strict :
    readAgree demoLengths (by omega : 0 < 6) ⟨0, by omega⟩ demoBefore flagOnlyAfter ∧
    ¬ (∀ x : Fin 6,
      readSupport demoLengths (by omega : 0 < 6) ⟨0, by omega⟩ x →
        demoBefore x = flagOnlyAfter x) := by decide

/-- This form allows the physical pair to touch the left leader. -/
theorem readAgree_of_pairOutside_and_flag {m n : Nat} (d : Fin m → Nat)
    (hn : 0 < n) (g : Fin m) (C D : Fin n → Cell) (l r : Fin n)
    (outside : ∀ x, x ≠ l → x ≠ r → C x = D x)
    (hown : ¬ (support d g l ∨ support d g r))
    (hflag : (C (gapPos d hn g 0)).leader = (D (gapPos d hn g 0)).leader) :
    readAgree d hn g C D := by
  refine ⟨?_, hflag⟩
  intro x hx
  apply outside x
  · intro he
    exact hown (Or.inl (he ▸ hx))
  · intro he
    exact hown (Or.inr (he ▸ hx))

theorem readAgree_of_pairOutside {m n : Nat} (d : Fin m → Nat)
    (hn : 0 < n) (g : Fin m) (C D : Fin n → Cell) (l r : Fin n)
    (outside : ∀ x, x ≠ l → x ≠ r → C x = D x)
    (hnt : ¬ (readSupport d hn g l ∨ readSupport d hn g r)) :
    readAgree d hn g C D := by
  apply readAgree_of_pairOutside_and_flag d hn g C D l r outside
  · intro h
    rcases h with h | h
    · exact hnt (Or.inl (Or.inl h))
    · exact hnt (Or.inr (Or.inl h))
  · apply congrArg Cell.leader
    apply outside (gapPos d hn g 0)
    · intro he
      exact hnt (Or.inl (Or.inr he.symm))
    · intro he
      exact hnt (Or.inr (Or.inr he.symm))

/-- A scheduled pair touches a component when either site lies in its closed read arc. -/
def readTouches {m n : Nat} {d : Fin m → Nat} {hn : 0 < n}
    (B : PhysicalBridge d hn) (g : Fin m) (s : B.State) (e : B.Event) : Prop :=
  readSupport d hn g (B.scheduledLeft s e) ∨
    readSupport d hn g (B.scheduledRight s e)

/-- Fixed-frame potential identities transport the read-agreement lemma to a step. -/
theorem phi_step_eq_of_readAgree {m n : Nat} {d : Fin m → Nat} {hn : 0 < n}
    (B : PhysicalBridge d hn) (g : Fin m) (s : B.State) (e : B.Event)
    (ho : B.Ordinary s e)
    (ha : readAgree d hn g (B.cfg (B.next s e)) (B.cfg s)) :
    B.Phi g (B.next s e) = B.Phi g s := by
  have hmin := B.minimum g
  rw [B.phi_after g s e ho, B.phi_before g s e ho]
  exact phi_support d hn B.total g (by omega) (B.cfg (B.next s e)) (B.cfg s) ha

/-- A physical two-site step outside a closed read arc preserves its potential. -/
theorem frameOutside_readAgree {m n : Nat} {d : Fin m → Nat} {hn : 0 < n}
    (B : PhysicalBridge d hn) (g : Fin m) (s : B.State) (e : B.Event)
    (ho : B.Ordinary s e) (hnt : ¬ readTouches B g s e) :
    B.Phi g (B.next s e) = B.Phi g s := by
  apply phi_step_eq_of_readAgree B g s e ho
  exact readAgree_of_pairOutside d hn g (B.cfg (B.next s e)) (B.cfg s)
    (B.scheduledLeft s e) (B.scheduledRight s e) (B.step_outside_eq s e ho) hnt

/-- Untouched ownership suffices when a touched left leader flag is separately preserved. -/
theorem step_eq_of_owned_untouched_and_flag {m n : Nat}
    {d : Fin m → Nat} {hn : 0 < n} (B : PhysicalBridge d hn)
    (g : Fin m) (s : B.State) (e : B.Event) (ho : B.Ordinary s e)
    (hown : ¬ (support d g (B.scheduledLeft s e) ∨
      support d g (B.scheduledRight s e)))
    (hflag : (B.cfg (B.next s e) (gapPos d hn g 0)).leader =
      (B.cfg s (gapPos d hn g 0)).leader) :
    B.Phi g (B.next s e) = B.Phi g s := by
  apply phi_step_eq_of_readAgree B g s e ho
  exact readAgree_of_pairOutside_and_flag d hn g (B.cfg (B.next s e)) (B.cfg s)
    (B.scheduledLeft s e) (B.scheduledRight s e) (B.step_outside_eq s e ho) hown hflag

/-- Adjacent scheduling specializes the spatial contact theorem to the bridge. -/
theorem scheduled_pair_touches_le_two {m n : Nat} {d : Fin m → Nat}
    {hn : 0 < n} (B : PhysicalBridge d hn) (s : B.State) (e : B.Event)
    (hadj : B.scheduledRight s e = succSite hn (B.scheduledLeft s e)) :
    ∃ a b : Fin m, ∀ g, readTouches B g s e → g = a ∨ g = b := by
  rcases adjacent_pair_touches_le_two d hn B.minimum B.total (B.scheduledLeft s e)
    with ⟨a, b, hc⟩
  refine ⟨a, b, ?_⟩
  intro g hg
  apply hc g
  rcases hg with hl | hr
  · exact Or.inl hl
  · exact Or.inr (hadj ▸ hr)

/-- An actual strict component increase, derived from the transition and potential. -/
def transferAt {m n : Nat} {d : Fin m → Nat} {hn : 0 < n}
    (B : PhysicalBridge d hn) (g : Fin m) (s : B.State) (e : B.Event) : Prop :=
  B.Phi g s < B.Phi g (B.next s e)

instance {m n : Nat} {d : Fin m → Nat} {hn : 0 < n}
    (B : PhysicalBridge d hn) (g : Fin m) (s : B.State) (e : B.Event) :
    Decidable (transferAt B g s e) := by
  unfold transferAt
  infer_instance

/-- Sparsity needs the physical frame property, but does not need quiet. -/
theorem transferAt_implies_readTouches {m n : Nat} {d : Fin m → Nat} {hn : 0 < n}
    (B : PhysicalBridge d hn) (g : Fin m) (s : B.State) (e : B.Event)
    (ho : B.Ordinary s e) (hi : transferAt B g s e) : readTouches B g s e := by
  classical
  by_cases ht : readTouches B g s e
  · exact ht
  · have he := frameOutside_readAgree B g s e ho ht
    change B.Phi g s < B.Phi g (B.next s e) at hi
    omega

/-- The derived increase set is covered by the two touched read arcs. -/
theorem transfer_pair_le_two {m n : Nat} {d : Fin m → Nat} {hn : 0 < n}
    (B : PhysicalBridge d hn) (s : B.State) (e : B.Event) (ho : B.Ordinary s e)
    (hadj : B.scheduledRight s e = succSite hn (B.scheduledLeft s e)) :
    ∃ a b : Fin m, ∀ g, transferAt B g s e → g = a ∨ g = b := by
  rcases scheduled_pair_touches_le_two B s e hadj with ⟨a, b, hc⟩
  exact ⟨a, b, fun g hg => hc g (transferAt_implies_readTouches B g s e ho hg)⟩

/-- At most two distinct components rise on an ordinary adjacent step. -/
theorem transfer_pair_count_le_two {m n : Nat} {d : Fin m → Nat} {hn : 0 < n}
    (B : PhysicalBridge d hn) (s : B.State) (e : B.Event) (ho : B.Ordinary s e)
    (hadj : B.scheduledRight s e = succSite hn (B.scheduledLeft s e)) :
    (List.ofFn (fun g : Fin m => g)).countP (fun g => decide (transferAt B g s e)) ≤ 2 := by
  rcases transfer_pair_le_two B s e ho hadj with ⟨a, b, hc⟩
  apply countP_le_two_of_cover _ a b
  intro g hg
  apply hc g
  simpa only [decide_eq_true_eq] using hg

/-- Additional protocol obligations; quiet is deliberately not claimed from geometry. -/
structure OrdinaryReadResidual {m n : Nat} {d : Fin m → Nat} {hn : 0 < n}
    (B : PhysicalBridge d hn) where
  NoTransfer : B.State → Prop
  enabled : Fin m → B.State → Prop
  ordinary : ∀ s e, NoTransfer s → B.Ordinary s e
  adjacent : ∀ s e, NoTransfer s →
    B.scheduledRight s e = succSite hn (B.scheduledLeft s e)
  quiet : ∀ g s e, NoTransfer s → ¬ enabled g s → readTouches B g s e →
    B.Phi g (B.next s e) ≤ B.Phi g s

/-- The frame is derived from read locality; quiet is the remaining row law.
The resulting object is the existing finite-scheduler interface. -/
theorem ordinaryLocality_of_readAgree {m n q : Nat} {d : Fin m → Nat} {hn : 0 < n}
    (B : PhysicalBridge d hn) (R : OrdinaryReadResidual B)
    (eventAt : Fin q → B.Event) :
    PerGapOffPay.OrdinaryLocality
      (fun s e => B.next s (eventAt e)) B.Phi R.NoTransfer R.enabled
      (fun g s e => readTouches B g s (eventAt e)) :=
  ⟨fun g s e hs ht => frameOutside_readAgree B g s (eventAt e)
      (R.ordinary s (eventAt e) hs) ht,
    fun g s e hs hg ht => R.quiet g s (eventAt e) hs hg ht⟩

/-- Ordinary adjacent steps can raise at most two component potentials. -/
theorem ordinary_transfer_count_le_two {m n : Nat} {d : Fin m → Nat} {hn : 0 < n}
    (B : PhysicalBridge d hn) (R : OrdinaryReadResidual B) (s : B.State) (e : B.Event)
    (hs : R.NoTransfer s) :
    (List.ofFn (fun g : Fin m => g)).countP (fun g => decide (transferAt B g s e)) ≤ 2 :=
  transfer_pair_count_le_two B s e (R.ordinary s e hs) (R.adjacent s e hs)

/-- Conditional wiring to the repository's finite-uniform off-pay consumer.
The contact bound is separate: summation uses the derived frame and quiet. -/
theorem wired_offPay {m n : Nat} {d : Fin m → Nat} {hn : 0 < n}
    (B : PhysicalBridge d hn) (R : OrdinaryReadResidual B) (eventAt : Fin n → B.Event)
    (g : Fin m) (s : B.State) (hs : R.NoTransfer s) (hg : ¬ R.enabled g s) :
    (List.ofFn (fun i : Fin n => B.Phi g (B.next s (eventAt i)))).sum ≤ n * B.Phi g s := by
  exact PerGapOffPay.perGap_offPay_of_ordinaryLocality
    (fun s' e => B.next s' (eventAt e)) B.Phi R.NoTransfer R.enabled
    (fun g' s' e => readTouches B g' s' (eventAt e))
    (ordinaryLocality_of_readAgree B R eventAt) g s hs hg

/-! A nonconstant finite witness for the conditional bridge. This deliberately
small deletion table is not asserted to refine a K2 execution. It demonstrates
that the geometric frame and quiet obligations are jointly satisfiable while
an ordinary adjacent step changes both the configuration and the potential. -/

/-- The two six-site configurations already used in the ownership counterexample. -/
def witnessCfg (s : Bool) : Fin 6 → Cell := if s then demoAfter else demoBefore

/-- Only the wraparound edge deletes site zero's leader; all other edges stutter. -/
def witnessNext (s : Bool) (e : Fin 6) : Bool := if e = 5 then true else s

/-- A finite bridge with genuine nonconstant potential and all six ring edges. -/
def witnessBridge : PhysicalBridge demoLengths (by decide : 0 < 6) where
  State := Bool
  Event := Fin 6
  cfg := witnessCfg
  next := witnessNext
  scheduledLeft := fun _ e => e
  scheduledRight := fun _ e => succSite (by decide : 0 < 6) e
  Phi := fun g s => phiOf demoLengths (by decide : 0 < 6) g (witnessCfg s)
  Ordinary := fun _ _ => True
  minimum := demo_geometry.1
  total := demo_geometry.2
  phi_before := fun _ _ _ _ => rfl
  phi_after := fun _ _ _ _ => rfl
  step_outside_eq := by decide

/-- Every gap is disabled in the witness, and its touched rows are still quiet. -/
def witnessResidual : OrdinaryReadResidual witnessBridge where
  NoTransfer := fun _ => True
  enabled := fun _ _ => False
  ordinary := fun _ _ _ => True.intro
  adjacent := fun _ _ _ => rfl
  quiet := by
    have h : ∀ (g : Fin 3) (s : Bool) (e : Fin 6),
        phiOf demoLengths (by decide : 0 < 6) g (witnessCfg (witnessNext s e)) ≤
          phiOf demoLengths (by decide : 0 < 6) g (witnessCfg s) := by decide
    intro g s e _ _ _
    exact h g s e

/-- The bridge is nonvacuous: an ordinary edge changes a positive potential. -/
theorem witness_strict_drop :
    witnessResidual.NoTransfer false ∧
    ¬ witnessResidual.enabled 0 false ∧
    readTouches witnessBridge 0 false (5 : Fin 6) ∧
    witnessBridge.Phi 0 false = 2 ∧
    witnessBridge.Phi 0 (witnessBridge.next false (5 : Fin 6)) = 0 := by
  dsimp [witnessResidual, witnessBridge, readTouches]
  decide

/-- The existing off-pay consumer accepts every state and gap of the witness. -/
theorem witness_offPay (g : Fin 3) (s : Bool) :
    (List.ofFn (fun e : Fin 6 =>
      witnessBridge.Phi g (witnessBridge.next s e))).sum ≤
        6 * witnessBridge.Phi g s := by
  exact wired_offPay witnessBridge witnessResidual (fun e => e) g s
    True.intro (fun h => h)

end Leader.ReadSupportContact

#print axioms Leader.ReadSupportContact.lift_succSite
#print axioms Leader.ReadSupportContact.adjacent_pair_in_gap
#print axioms Leader.ReadSupportContact.interior_read_unique
#print axioms Leader.ReadSupportContact.adjacent_pair_touches_le_two
#print axioms Leader.ReadSupportContact.two_leader_pair_touches_le_two
#print axioms Leader.ReadSupportContact.countP_le_two_of_cover
#print axioms Leader.ReadSupportContact.adjacent_pair_contact_count
#print axioms Leader.ReadSupportContact.adjacent_two_is_sharp
#print axioms Leader.ReadSupportContact.one_gap_wrap_contact
#print axioms Leader.ReadSupportContact.two_gap_adjacent_contacts
#print axioms Leader.ReadSupportContact.length_one_three_contacts
#print axioms Leader.ReadSupportContact.arbitrary_pair_four_is_sharp
#print axioms Leader.ReadSupportContact.phi_support
#print axioms Leader.ReadSupportContact.closed_agreement_implies_readAgree
#print axioms Leader.ReadSupportContact.leader_flag_refinement_strict
#print axioms Leader.ReadSupportContact.readAgree_of_pairOutside_and_flag
#print axioms Leader.ReadSupportContact.readAgree_of_pairOutside
#print axioms Leader.ReadSupportContact.phi_step_eq_of_readAgree
#print axioms Leader.ReadSupportContact.frameOutside_readAgree
#print axioms Leader.ReadSupportContact.step_eq_of_owned_untouched_and_flag
#print axioms Leader.ReadSupportContact.scheduled_pair_touches_le_two
#print axioms Leader.ReadSupportContact.transferAt_implies_readTouches
#print axioms Leader.ReadSupportContact.transfer_pair_le_two
#print axioms Leader.ReadSupportContact.transfer_pair_count_le_two
#print axioms Leader.ReadSupportContact.ordinaryLocality_of_readAgree
#print axioms Leader.ReadSupportContact.ordinary_transfer_count_le_two
#print axioms Leader.ReadSupportContact.wired_offPay
#print axioms Leader.ReadSupportContact.witnessBridge
#print axioms Leader.ReadSupportContact.witnessResidual
#print axioms Leader.ReadSupportContact.witness_strict_drop
#print axioms Leader.ReadSupportContact.witness_offPay
