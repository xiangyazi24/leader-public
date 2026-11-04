import Leader.L3.Width.DigitQuietStepGlue

/-!
# The quiet class after one letter: the root, layout, value and base clauses

* `quiet_rootFixed_step`, `quiet_layout_step`, `quiet_values_step`: the root, the visible betas and
  (with the digits kept) the digit values are unchanged by a letter at a fixed visible word;
* `liveTop_wBase_x`, `liveTop_wBase_y`: the BASE output rows of `liveTopPair`;
* `quiet_base_step`: the base labels of the class are closed under a letter.

Consumer: `QuietStepLaw` (WidthDigitQuiet), the root, layout, values and base fields.
-/

namespace L3.DigitQuiet

open L3
open L3.AcceptedReceipts

set_option autoImplicit false

variable {c : Compiled} {n : Nat}

/-- The BASE output of the left agent of a letter is always `NONE`.  Consumer: `pairD_wBase_left`. -/
theorem liveTop_wBase_x (ox oy : Agent c) (bX bY : Bool) :
    (liveTopPair c ox oy bX bY).x.wBase = .NONE := by
  rcases ox with ⟨l,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,wb,_,_,_,_,_,_,_⟩
  rcases oy with ⟨l2,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,wb2,_,_,_,_,_,_,_⟩
  cases l <;> cases l2 <;> cases wb <;> cases wb2 <;> cases bY <;> rfl

/-- The BASE output of the right agent of a letter.  Consumer: `pairD_wBase_right`. -/
theorem liveTop_wBase_y (ox oy : Agent c) (bX bY : Bool) :
    (liveTopPair c ox oy bX bY).y.wBase =
      if oy.l = true then oy.wBase
      else if ox.l = true then (if oy.wBase = .NONE then .SEEK else oy.wBase)
      else if ox.wBase = .ZERO then (if bY = false ∧ oy.wBase = .NONE then .ZERO else oy.wBase)
      else if ox.wBase = .SEEK then
        (if oy.wBase = .NONE then (if bY = true then .ZERO else .SEEK) else oy.wBase)
      else oy.wBase := by
  rcases ox with ⟨l,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,wb,_,_,_,_,_,_,_⟩
  rcases oy with ⟨l2,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,wb2,_,_,_,_,_,_,_⟩
  cases l <;> cases l2 <;> cases wb <;> cases wb2 <;> cases bY <;> rfl


/-- The left record of a projected letter has base `NONE`.  Consumer: `quiet_base_step`. -/
theorem phiD_left_wBase (ring : DirectedRing n) (S : Fin n → ProjD c) (e : Fin n) :
    ((phiD ring S e) e).top.wBase = .NONE := by
  rw [phiD_at_left]
  exact liveTop_wBase_x _ _ _ _

/-- The base of the right record of a projected letter, on the old records and the resolved beta of
the right site.  Consumer: `quiet_base_step`. -/
theorem phiD_right_wBase (ring : DirectedRing n) (S : Fin n → ProjD c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hbY : (pairW (S e).word (S (ring.rightNeighbor e)).word).2.beta =
      (S (ring.rightNeighbor e)).word.beta) :
    ((phiD ring S e) (ring.rightNeighbor e)).top.wBase =
      if (S (ring.rightNeighbor e)).word.native.l = true then (S (ring.rightNeighbor e)).top.wBase
      else if (S e).word.native.l = true then
        (if (S (ring.rightNeighbor e)).top.wBase = .NONE then .SEEK
          else (S (ring.rightNeighbor e)).top.wBase)
      else if (S e).top.wBase = .ZERO then
        (if (S (ring.rightNeighbor e)).word.beta = false ∧
            (S (ring.rightNeighbor e)).top.wBase = .NONE then .ZERO
          else (S (ring.rightNeighbor e)).top.wBase)
      else if (S e).top.wBase = .SEEK then
        (if (S (ring.rightNeighbor e)).top.wBase = .NONE then
          (if (S (ring.rightNeighbor e)).word.beta = true then .ZERO else .SEEK)
          else (S (ring.rightNeighbor e)).top.wBase)
      else (S (ring.rightNeighbor e)).top.wBase := by
  rw [phiD_at_right ring S e hne]
  show (liveTopPair c (S e).lift (S (ring.rightNeighbor e)).lift
    (pairW (S e).word (S (ring.rightNeighbor e)).word).1.beta
    (pairW (S e).word (S (ring.rightNeighbor e)).word).2.beta).y.wBase = _
  rw [liveTop_wBase_y, hbY]
  rfl

/-- The span of a block is at least two for the compiled width.  Consumer: `quiet_base_step`. -/
theorem digitSpan_ge_two (hn : 5 ≤ n) : 2 ≤ digitSpan (compileAdvice (ceilLogTwo n)) := by
  have ht := compileAdvice_t_ge_two (ceilLogTwo n) (ringQ_facts n hn).1
  unfold digitSpan
  have h4 : 2 ^ 2 ≤ 2 ^ (compileAdvice (ceilLogTwo n)).t := Nat.pow_le_pow_right (by omega) ht
  omega

/-- The sites `1..n-1` are not the root.  Consumer: `quiet_base_step`. -/
theorem digitSite_ne_root (ring : DirectedRing n) (root : Fin n) (k : Nat) (h0 : 0 < k)
    (hk : k < n) : digitSite ring root k ≠ root := by
  intro h
  have h' : digitSite ring root k = digitSite ring root 0 := h
  have := RenewalReferenceClock.bankRepairDigitSiteInj ring root hk (by omega) h'
  omega

/-- Every site is `digitSite k` for some `k < n`.  Consumer: `quiet_base_step`. -/
theorem digitSite_surj (ring : DirectedRing n) (root : Fin n) (e : Fin n) :
    ∃ k, k < n ∧ digitSite ring root k = e := by
  have he := e.isLt
  have hr := root.isLt
  refine ⟨(e.val + n - root.val) % n, Nat.mod_lt _ (by omega), ?_⟩
  apply Fin.ext
  rw [RenewalReferenceClock.bankRepairDigitSiteVal, Nat.add_mod_mod,
    show root.val + (e.val + n - root.val) = e.val + n by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt he]

/-- **The root stays the unique leader.**  Consumer: `QuietStepLaw`, field `rootFixed`. -/
theorem quiet_rootFixed_step (hn : 5 ≤ n) (ring : DirectedRing n) (root : Fin n) (_first : Nat)
    (S : Fin n → ProjD (compileAdvice (ceilLogTwo n)))
    (hF : WFixedRoot ring root (wordProjection S)) (e : Fin n) :
    ∀ i : Fin n, ((phiD ring S e) i).word.native.l = true ↔ i = root := by
  have h := RenewalReferenceClock.bankRepairDigitWFixedRootPhiW (by omega) ring root
    (wordProjection S) e hF
  rw [← wordProjection_phiD] at h
  intro i
  exact ⟨fun hi => h.2.1 i hi, fun hi => by rw [hi]; exact h.1⟩

/-- **The layout is unchanged**: the visible betas are fixed by `QWord`.  Consumer: `QuietStepLaw`,
field `layout`. -/
theorem quiet_layout_step (ring : DirectedRing n) (root : Fin n) (first : Nat)
    (S : Fin n → ProjD (compileAdvice (ceilLogTwo n)))
    (hQ : WidthDigitQuiet ring root first S) (hW : QWord ring (wordProjection S)) (e : Fin n) :
    2 ≤ first ∧ first < n ∧ ∀ k, 0 < k → k < n →
      (((phiD ring S e) (digitSite ring root k)).word.beta = true ↔
        first ≤ k ∧ (k - first) % digitSpan (compileAdvice (ceilLogTwo n)) = 0) := by
  refine ⟨hQ.layout.1, hQ.layout.2.1, fun k h0 hk => ?_⟩
  have hvis := qword_visible_fixed ring (wordProjection S) hW e (digitSite ring root k)
  rw [← wordProjection_phiD] at hvis
  have hb : ((phiD ring S e) (digitSite ring root k)).word.beta =
      (S (digitSite ring root k)).word.beta :=
    congrArg (fun z : Bool × Bool => z.2) hvis
  rw [hb]
  exact hQ.layout.2.2 k h0 hk

/-- **The digit values are unchanged** when every digit is kept.  Consumer: `QuietStepLaw`, field
`values`. -/
theorem quiet_values_step (ring : DirectedRing n) (root : Fin n) (first : Nat)
    (S : Fin n → ProjD (compileAdvice (ceilLogTwo n)))
    (hQ : WidthDigitQuiet ring root first S) (hW : QWord ring (wordProjection S)) (e : Fin n)
    (hdig : ∀ i : Fin n, ((phiD ring S e) i).top.d = (S i).top.d) :
    DigitValuesCorrect ring root (digitValueView (phiD ring S e)) := by
  have hv : digitValueView (phiD ring S e) = digitValueView S := by
    funext i
    have hvis := qword_visible_fixed ring (wordProjection S) hW e i
    rw [← wordProjection_phiD] at hvis
    have hb : ((phiD ring S e) i).word.beta = (S i).word.beta :=
      congrArg (fun z : Bool × Bool => z.2) hvis
    simp only [digitValueView, hb, hdig i]
  rw [hv]
  exact hQ.values

/-- **The base labels are closed under a letter**: `SEEK` moves right below `first`, turns into `ZERO`
at `first`, `ZERO` moves right below `first + R`; the root relaunches `SEEK` at site `1`.  Consumer:
`QuietStepLaw`, field `base`. -/
theorem quiet_base_step (hn : 5 ≤ n) (ring : DirectedRing n) (root : Fin n) (first : Nat)
    (S : Fin n → ProjD (compileAdvice (ceilLogTwo n)))
    (hQ : WidthDigitQuiet ring root first S) (hW : QWord ring (wordProjection S)) (e : Fin n) :
    ∀ k, 0 < k → k < n →
      (((phiD ring S e) (digitSite ring root k)).top.wBase = .SEEK → k < first) ∧
      (((phiD ring S e) (digitSite ring root k)).top.wBase = .ZERO →
        first ≤ k ∧ k < first + digitSpan (compileAdvice (ceilLogTwo n))) := by
  intro k hk0 hkn
  have hR := digitSpan_ge_two hn
  have hne := rightNeighbor_ne ring (by omega) e
  obtain ⟨p, hp, rfl⟩ := digitSite_surj ring root e
  have hf2 := hQ.layout.1
  have hbk := hQ.base k hk0 hkn
  by_cases hs1 : digitSite ring root k = digitSite ring root p
  · rw [hs1, phiD_left_wBase]
    exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
  by_cases hs2 : digitSite ring root k = ring.rightNeighbor (digitSite ring root p)
  · have hkp : k = p + 1 := by
      by_cases hpn : p + 1 < n
      · exact RenewalReferenceClock.bankRepairDigitSiteInj ring root hkn hpn hs2
      · have hpn' : p + 1 = n := by omega
        exfalso
        apply digitSite_ne_root ring root k hk0 hkn
        rw [hs2]
        show digitSite ring root (p + 1) = root
        rw [hpn']
        exact RenewalReferenceClock.bankRepairDigitSiteN ring root
    obtain ⟨-, hbY⟩ := resolved_betas ring S hW (digitSite ring root p) hne
    have hf := phiD_right_wBase ring S (digitSite ring root p) hne hbY
    rw [← hs2] at hf
    rw [hf]
    have hYl : ¬ ((S (digitSite ring root k)).word.native.l = true) := by
      intro h
      exact digitSite_ne_root ring root k hk0 hkn ((hQ.rootFixed _).mp h)
    have hbeta := hQ.layout.2.2 k hk0 hkn
    rw [if_neg hYl]
    by_cases hXl : (S (digitSite ring root p)).word.native.l = true
    · have hp0 : p = 0 := by
        have h0 : digitSite ring root p = digitSite ring root 0 := (hQ.rootFixed _).mp hXl
        exact RenewalReferenceClock.bankRepairDigitSiteInj ring root hp (by omega) h0
      rw [if_pos hXl]
      by_cases hb : (S (digitSite ring root k)).top.wBase = .NONE
      · rw [if_pos hb]
        exact ⟨fun _ => by omega, (fun h => nomatch h)⟩
      · rw [if_neg hb]
        exact hbk
    · have hp0 : p ≠ 0 := by
        intro h
        apply hXl
        subst h
        exact (hQ.rootFixed (digitSite ring root 0)).mpr rfl
      have hbp := hQ.base p (by omega) hp
      rw [if_neg hXl]
      by_cases hZ : (S (digitSite ring root p)).top.wBase = .ZERO
      · rw [if_pos hZ]
        obtain ⟨hz1, hz2⟩ := hbp.2 hZ
        by_cases hc : (S (digitSite ring root k)).word.beta = false ∧
            (S (digitSite ring root k)).top.wBase = .NONE
        · rw [if_pos hc]
          refine ⟨(fun h => nomatch h), fun _ => ?_⟩
          have hnb : ¬ (first ≤ k ∧ (k - first) % digitSpan (compileAdvice (ceilLogTwo n)) = 0) := by
            intro hh
            have := hbeta.mpr hh
            rw [hc.1] at this
            cases this
          by_cases hkR : k = first + digitSpan (compileAdvice (ceilLogTwo n))
          · exfalso
            apply hnb
            refine ⟨by omega, ?_⟩
            rw [show k - first = digitSpan (compileAdvice (ceilLogTwo n)) by omega, Nat.mod_self]
          · omega
        · rw [if_neg hc]
          exact hbk
      · rw [if_neg hZ]
        by_cases hS : (S (digitSite ring root p)).top.wBase = .SEEK
        · rw [if_pos hS]
          have hpf : p < first := hbp.1 hS
          by_cases hb : (S (digitSite ring root k)).top.wBase = .NONE
          · rw [if_pos hb]
            by_cases hbt : (S (digitSite ring root k)).word.beta = true
            · rw [if_pos hbt]
              refine ⟨(fun h => nomatch h), fun _ => ?_⟩
              obtain ⟨h1, h2⟩ := hbeta.mp hbt
              omega
            · rw [if_neg hbt]
              refine ⟨fun _ => ?_, (fun h => nomatch h)⟩
              by_cases hkf : k < first
              · exact hkf
              · exfalso
                apply hbt
                apply hbeta.mpr
                refine ⟨by omega, ?_⟩
                rw [show k - first = 0 by omega, Nat.zero_mod]
          · rw [if_neg hb]
            exact hbk
        · rw [if_neg hS]
          exact hbk
  · rw [phiD_at_other ring S _ _ hs1 hs2]
    exact hbk

end L3.DigitQuiet

#print axioms L3.DigitQuiet.quiet_rootFixed_step
#print axioms L3.DigitQuiet.quiet_layout_step
#print axioms L3.DigitQuiet.quiet_values_step
#print axioms L3.DigitQuiet.quiet_base_step
