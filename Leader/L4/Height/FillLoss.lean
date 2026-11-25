import Leader.L4.Height.LossAlt
import Leader.L4.Height.FillAlt
import Leader.L4.Height.GapAlt
import Leader.L4.Height.FillGap

namespace L4.Height

open Classical
open L4.Compiler.Native

set_option maxRecDepth 8192
set_option maxHeartbeats 30000000

/-! ## Recovering the concrete cyclic geometry of a comparison -/

/-- The clockwise path beginning at a named anchor. -/
def fillLossPath {m : Nat} (hm : 0 < m) (a : Fin m) : Nat → Fin m :=
  fun i => gapSite hm a i

theorem fillLossPath_is_path {m : Nat} (hm : 0 < m)
    (a : Fin m) (g : Nat) :
    GapPath hm (fillLossPath hm a) g := by
  intro i hi
  simp [fillLossPath, gapSite_succ]

/-- A comparison occurs as three consecutive members of the canonical
increasing anchor list. -/
def ComparisonAppears {m : Nat} (q : AnchorComparison m)
    (sites : List (Fin m)) : Prop :=
  ∃ pre post, sites = pre ++ q.a :: q.b :: q.c :: post

private theorem qualifyingComparison_spec_aux {m : Nat}
    (G : Nat) (first : Fin m) :
    ∀ n (sites : List (Fin m)), sites.length ≤ n →
      ∀ q : AnchorComparison m,
        q ∈ qualifyingComparisons G (anchorGapPairsFrom first sites) →
        ComparisonAppears q sites ∧
          q.gA = q.b.val - q.a.val ∧
          q.gB = q.c.val - q.b.val := by
  intro n
  induction n with
  | zero =>
      intro sites hlen q hq
      cases sites with
      | nil =>
          simp [anchorGapPairsFrom, qualifyingComparisons] at hq
      | cons a rest =>
          simp only [List.length_cons] at hlen
          omega
  | succ n ih =>
      intro sites hlen q hq
      cases sites with
      | nil =>
          simp [anchorGapPairsFrom, qualifyingComparisons] at hq
      | cons a tail =>
          cases tail with
          | nil =>
              simp [anchorGapPairsFrom, qualifyingComparisons] at hq
          | cons b tail =>
              cases tail with
              | nil =>
                  simp [anchorGapPairsFrom, qualifyingComparisons] at hq
              | cons c rest =>
                  cases rest with
                  | nil =>
                      change q ∈ qualifyingComparisons G
                        ({ site := a, gap := b.val - a.val } ::
                         { site := b, gap := c.val - b.val } ::
                         [{ site := c,
                            gap := (m - c.val) + first.val }]) at hq
                      by_cases hqual :
                          b.val - a.val ≤ G ∧ c.val - b.val ≤ G
                      · simp only [qualifyingComparisons, if_pos hqual,
                          List.mem_cons, List.not_mem_nil, or_false] at hq
                        subst q
                        exact ⟨⟨[], [], rfl⟩, rfl, rfl⟩
                      · simp only [qualifyingComparisons, if_neg hqual] at hq
                        cases hq
                  | cons d rest =>
                      have hrest : (d :: rest).length ≤ n := by
                        simp only [List.length_cons] at hlen ⊢
                        omega
                      change q ∈ qualifyingComparisons G
                        ({ site := a, gap := b.val - a.val } ::
                         { site := b, gap := c.val - b.val } ::
                         { site := c, gap := d.val - c.val } ::
                         anchorGapPairsFrom first (d :: rest)) at hq
                      by_cases hqual :
                          b.val - a.val ≤ G ∧ c.val - b.val ≤ G
                      · simp only [qualifyingComparisons, if_pos hqual,
                          List.mem_cons] at hq
                        rcases hq with hhead | htail
                        · subst q
                          exact ⟨⟨[], d :: rest, rfl⟩, rfl, rfl⟩
                        · have hs := ih (d :: rest) hrest q htail
                          rcases hs with
                            ⟨⟨pre, post, heq⟩, hga, hgb⟩
                          refine ⟨⟨a :: b :: c :: pre, post, ?_⟩,
                            hga, hgb⟩
                          simp only [List.cons_append]
                          rw [← heq]
                      · simp only [qualifyingComparisons, if_neg hqual] at hq
                        have hs := ih (d :: rest) hrest q hq
                        rcases hs with
                          ⟨⟨pre, post, heq⟩, hga, hgb⟩
                        refine ⟨⟨a :: b :: c :: pre, post, ?_⟩,
                          hga, hgb⟩
                        simp only [List.cons_append]
                        rw [← heq]

private theorem qualifyingComparison_spec {m : Nat}
    (G : Nat) (first : Fin m) (sites : List (Fin m))
    (q : AnchorComparison m)
    (hq : q ∈ qualifyingComparisons G
      (anchorGapPairsFrom first sites)) :
    ComparisonAppears q sites ∧
      q.gA = q.b.val - q.a.val ∧
      q.gB = q.c.val - q.b.val := by
  exact qualifyingComparison_spec_aux G first sites.length sites
    (Nat.le_refl _) q hq

private theorem pairwise_triple_lt
    {m : Nat} (a b c : Fin m) (post : List (Fin m)) :
    ∀ pre : List (Fin m),
      (pre ++ a :: b :: c :: post).Pairwise
        (fun x y => x.val < y.val) →
      a.val < b.val ∧ b.val < c.val := by
  intro pre
  induction pre with
  | nil =>
      intro h
      simp only [List.nil_append] at h
      have ha := List.pairwise_cons.mp h
      have hab := ha.1 b (by simp)
      have hb := List.pairwise_cons.mp ha.2
      have hbc := hb.1 c (by simp)
      exact ⟨hab, hbc⟩
  | cons d pre ih =>
      intro h
      rw [List.cons_append, List.pairwise_cons] at h
      exact ih h.2

private theorem comparisonAppears_lt {m : Nat}
    {q : AnchorComparison m} {sites : List (Fin m)}
    (horder : sites.Pairwise (fun x y => x.val < y.val))
    (hcmp : ComparisonAppears q sites) :
    q.a.val < q.b.val ∧ q.b.val < q.c.val := by
  rcases hcmp with ⟨pre, post, heq⟩
  rw [heq] at horder
  exact pairwise_triple_lt q.a q.b q.c post pre horder

private theorem adjacent_no_between
    {m : Nat} (a b y : Fin m) (post : List (Fin m)) :
    ∀ pre : List (Fin m),
      (pre ++ a :: b :: post).Pairwise
        (fun x z => x.val < z.val) →
      y ∈ pre ++ a :: b :: post →
      a.val < y.val → y.val < b.val → False := by
  intro pre
  induction pre with
  | nil =>
      intro hp hy hay hyb
      simp only [List.nil_append, List.mem_cons] at hy
      rcases hy with rfl | hy
      · omega
      · rcases hy with rfl | hpost
        · omega
        · have hbpack :=
            List.pairwise_cons.mp (List.pairwise_cons.mp hp).2
          have hby := hbpack.1 y hpost
          omega
  | cons d pre ih =>
      intro hp hy hay hyb
      rw [List.cons_append, List.pairwise_cons] at hp
      rw [List.cons_append] at hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | htail
      · have hda := hp.1 a (by simp)
        omega
      · exact ih hp.2 htail hay hyb

private theorem gapSite_sub_eq {m : Nat} (hm : 0 < m)
    (a b : Fin m) (h : a.val < b.val) :
    gapSite hm a (b.val - a.val) = b := by
  apply Fin.ext
  change (a.val + (b.val - a.val)) % m = b.val
  have he : a.val + (b.val - a.val) = b.val := by omega
  rw [he, Nat.mod_eq_of_lt b.isLt]

private theorem gapSite_wrap_eq {m : Nat} (hm : 0 < m)
    (a b : Fin m) (_h : a.val < b.val) :
    gapSite hm b ((m - b.val) + a.val) = a := by
  apply Fin.ext
  change (b.val + ((m - b.val) + a.val)) % m = a.val
  have he : b.val + ((m - b.val) + a.val) = m + a.val := by
    have hbLt := b.isLt
    omega
  rw [he]
  simp only [Nat.add_mod, Nat.mod_self, Nat.zero_add,
    Nat.mod_eq_of_lt a.isLt]

private theorem gapSite_val_of_add_lt {m : Nat} (hm : 0 < m)
    (a : Fin m) (i : Nat) (h : a.val + i < m) :
    (gapSite hm a i).val = a.val + i := by
  change (a.val + i) % m = a.val + i
  exact Nat.mod_eq_of_lt h

private theorem list_eq_pair_of_length_two {α : Type}
    (l : List α) (h : l.length = 2) :
    ∃ a b, l = [a, b] := by
  cases l with
  | nil => simp at h
  | cons a rest =>
      cases rest with
      | nil => simp at h
      | cons b rest =>
          cases rest with
          | nil => exact ⟨a, b, rfl⟩
          | cons c rest => simp at h

/-- All geometric facts needed to invoke the two fixed-gap theorems. -/
structure ComparisonGeometry {m : Nat} (hm : 0 < m)
    (s : Fin m → Snapshot) (q : AnchorComparison m) where
  gapAPos : 1 ≤ q.gA
  gapBPos : 1 ≤ q.gB
  gapSum : q.gA + q.gB ≤ m
  endA : q.b = gapSite hm q.a q.gA
  endB : q.c = gapSite hm q.b q.gB
  ab_ne : q.a ≠ q.b
  interiorA : ∀ i, 0 < i → i < q.gA →
    ¬ IsAnchor hm s (gapSite hm q.a i)
  interiorB : ∀ i, 0 < i → i < q.gB →
    ¬ IsAnchor hm s (gapSite hm q.b i)

private theorem heightComparison_geometry {m : Nat}
    (hm : 0 < m) (s : Fin m → Snapshot)
    (q : AnchorComparison m)
    (htwo : 2 ≤ anchorCount hm s)
    (hq : q ∈ heightComparisons hm s) :
    ComparisonGeometry hm s q := by
  by_cases hk : anchorCount hm s = 2
  · have hlen : (anchorSites hm s).length = 2 := by
      rw [anchorSites_length, hk]
    obtain ⟨a, b, hsites⟩ :=
      list_eq_pair_of_length_two (anchorSites hm s) hlen
    have horder := anchorSites_pairwise_val_lt hm s
    rw [hsites] at horder
    have hab : a.val < b.val := by
      have hp := List.pairwise_cons.mp horder
      exact hp.1 b (by simp)
    unfold heightComparisons at hq
    rw [if_pos hk] at hq
    unfold cyclicAnchorGaps at hq
    rw [hsites] at hq
    simp only [anchorGapPairsFrom, twoAnchorComparisons,
      List.mem_singleton] at hq
    subst q
    have hendA := gapSite_sub_eq hm a b hab
    have hendB := gapSite_wrap_eq hm a b hab
    refine {
      gapAPos := by
        change 1 ≤ b.val - a.val
        omega
      gapBPos := by
        change 1 ≤ (m - b.val) + a.val
        have hbLt := b.isLt
        omega
      gapSum := by
        change (b.val - a.val) + ((m - b.val) + a.val) ≤ m
        have haLt := a.isLt
        have hbLt := b.isLt
        omega
      endA := by
        change b = gapSite hm a (b.val - a.val)
        exact hendA.symm
      endB := by
        change a = gapSite hm b ((m - b.val) + a.val)
        exact hendB.symm
      ab_ne := by
        change a ≠ b
        intro h
        have hv := congrArg Fin.val h
        omega
      interiorA := ?_
      interiorB := ?_ }
    · intro i hi0 hig hiAnchor
      change i < b.val - a.val at hig
      have hmem := (mem_anchorSites hm s _).2 hiAnchor
      rw [hsites] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      have hsum : a.val + i < m := by
        have hbLt := b.isLt
        omega
      have hval := gapSite_val_of_add_lt hm a i hsum
      rcases hmem with hya | hyb
      · have hv := congrArg Fin.val hya
        rw [hval] at hv
        omega
      · have hv := congrArg Fin.val hyb
        rw [hval] at hv
        omega
    · intro i hi0 hig hiAnchor
      change i < (m - b.val) + a.val at hig
      have hmem := (mem_anchorSites hm s _).2 hiAnchor
      rw [hsites] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      have hgapLe : (m - b.val) + a.val ≤ m := by
        have hbLt := b.isLt
        omega
      have him : i < m := Nat.lt_of_lt_of_le hig hgapLe
      have hneB : gapSite hm b i ≠ b :=
        gapSite_ne_start hm b hi0 him
      have hneEnd := gapSite_internal_ne_end hm b hgapLe hi0 hig
      have hneA : gapSite hm b i ≠ a := by
        intro hia
        apply hneEnd
        calc
          gapSite hm b i = a := hia
          _ = gapSite hm b ((m - b.val) + a.val) := hendB.symm
      rcases hmem with hya | hyb
      · exact hneA hya
      · exact hneB hyb
  · have hkthree : 3 ≤ anchorCount hm s := by omega
    have hq' := hq
    unfold heightComparisons at hq'
    rw [if_neg hk] at hq'
    cases hs : anchorSites hm s with
    | nil =>
        have hlen := anchorSites_length hm s
        rw [hs] at hlen
        simp only [List.length_nil] at hlen
        omega
    | cons first rest =>
        unfold cyclicAnchorGaps at hq'
        rw [hs] at hq'
        have hspec := qualifyingComparison_spec
          (gapCeil m (anchorCount hm s)) first (first :: rest) q hq'
        rcases hspec with ⟨hcmp, hga, hgb⟩
        have horder := anchorSites_pairwise_val_lt hm s
        rw [hs] at horder
        have hlt := comparisonAppears_lt horder hcmp
        rcases hcmp with ⟨pre, post, heq⟩
        have hqaLt := q.a.isLt
        have hqbLt := q.b.isLt
        have hqcLt := q.c.isLt
        have hpair :
            (pre ++ q.a :: q.b :: q.c :: post).Pairwise
              (fun x y : Fin m => x.val < y.val) := by
          rw [← heq]
          exact horder
        have hendA : q.b = gapSite hm q.a q.gA := by
          rw [hga]
          exact (gapSite_sub_eq hm q.a q.b hlt.1).symm
        have hendB : q.c = gapSite hm q.b q.gB := by
          rw [hgb]
          exact (gapSite_sub_eq hm q.b q.c hlt.2).symm
        refine {
          gapAPos := by rw [hga]; omega
          gapBPos := by rw [hgb]; omega
          gapSum := by rw [hga, hgb]; omega
          endA := hendA
          endB := hendB
          ab_ne := by
            intro h
            have hv := congrArg Fin.val h
            omega
          interiorA := ?_
          interiorB := ?_ }
        · intro i hi0 hig hiAnchor
          have hmem0 := (mem_anchorSites hm s _).2 hiAnchor
          have hmem : gapSite hm q.a i ∈
              pre ++ q.a :: q.b :: q.c :: post := by
            rw [← heq, ← hs]
            exact hmem0
          have higa : i < q.b.val - q.a.val := by
            rw [← hga]
            exact hig
          have hsum : q.a.val + i < m := by omega
          have hval := gapSite_val_of_add_lt hm q.a i hsum
          have hay : q.a.val < (gapSite hm q.a i).val := by
            rw [hval]
            omega
          have hyb : (gapSite hm q.a i).val < q.b.val := by
            rw [hval]
            omega
          exact adjacent_no_between q.a q.b (gapSite hm q.a i)
            (q.c :: post) pre hpair hmem hay hyb
        · intro i hi0 hig hiAnchor
          have hmem0 := (mem_anchorSites hm s _).2 hiAnchor
          let preB := pre ++ [q.a]
          have hpairB :
              (preB ++ q.b :: q.c :: post).Pairwise
                (fun x y : Fin m => x.val < y.val) := by
            dsimp [preB]
            simpa [List.append_assoc] using hpair
          have hmemB : gapSite hm q.b i ∈
              preB ++ q.b :: q.c :: post := by
            dsimp [preB]
            simpa [List.append_assoc, heq, hs] using hmem0
          have higb : i < q.c.val - q.b.val := by
            rw [← hgb]
            exact hig
          have hsum : q.b.val + i < m := by omega
          have hval := gapSite_val_of_add_lt hm q.b i hsum
          have hby : q.b.val < (gapSite hm q.b i).val := by
            rw [hval]
            omega
          have hyc : (gapSite hm q.b i).val < q.c.val := by
            rw [hval]
            omega
          exact adjacent_no_between q.b q.c (gapSite hm q.b i)
            post preB hpairB hmemB hby hyc

/-! ## Scheduled draw arithmetic -/

/-- The last member of a positive-period arithmetic progression before `T`. -/
def fillLastDraw (first period T : Nat) : Nat :=
  first + period * ((T - 1 - first) / period)

structure ScheduledLastFacts
    (first period T last : Nat) where
  lastLt : last < T
  windowLeNext : T ≤ last + period
  firstLe : first ≤ last
  lastMod : (last - first) % period = 0
  maximal : ∀ r, first ≤ r → r < T →
    (r - first) % period = 0 → r ≤ last
  predecessor : first < last →
    first ≤ last - period ∧
      (last - period - first) % period = 0 ∧
      ∀ r, last - period < r → r < last →
        (r - first) % period ≠ 0

private theorem scheduled_last_facts
    (first period T : Nat)
    (hperiod : 0 < period) (hfirst : 0 < first)
    (hfirstT : first < T) :
    ScheduledLastFacts first period T
      (fillLastDraw first period T) := by
  have hq1 := Nat.mul_div_le (T - 1 - first) period
  have hq2 := Nat.lt_mul_div_succ (T - 1 - first) hperiod
  generalize hq : (T - 1 - first) / period = q
  rw [hq] at hq1 hq2
  rw [Nat.mul_add, Nat.mul_one] at hq2
  have hlast : fillLastDraw first period T = first + period * q := by
    simp [fillLastDraw, hq]
  have hdel : ∀ r, first ≤ r → (r - first) % period = 0 →
      r = first + period * ((r - first) / period) := by
    intro r hfr hmod
    have hd := Nat.div_add_mod (r - first) period
    omega
  refine {
    lastLt := ?_
    windowLeNext := ?_
    firstLe := ?_
    lastMod := ?_
    maximal := ?_
    predecessor := ?_ }
  · rw [hlast]
    omega
  · rw [hlast]
    omega
  · rw [hlast]
    omega
  · rw [hlast]
    rw [show first + period * q - first = period * q by omega]
    exact Nat.mul_mod_right period q
  · intro r hfr hrT hmod
    have er := hdel r hfr hmod
    generalize ha : (r - first) / period = a at er
    have haLt : a < q + 1 :=
      Nat.lt_of_mul_lt_mul_left (a := period) (by
        rw [Nat.mul_add, Nat.mul_one]
        omega)
    have hmul := Nat.mul_le_mul_left period (show a ≤ q by omega)
    rw [hlast]
    omega
  · intro hfirstLast
    rcases Nat.eq_zero_or_pos q with hzero | hqpos
    · rw [hzero, Nat.mul_zero] at hlast
      omega
    · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 :=
        ⟨q - 1, by omega⟩
      rw [Nat.mul_add, Nat.mul_one] at hlast hq1
      refine ⟨by omega, ?_, ?_⟩
      · rw [show fillLastDraw first period T - period - first =
          period * q' by omega]
        exact Nat.mul_mod_right period q'
      · intro r hpen hrLast hmod
        have er := hdel r (by omega) hmod
        generalize ha : (r - first) / period = a at er
        have ha1 : q' < a :=
          Nat.lt_of_mul_lt_mul_left (a := period) (by omega)
        have ha2 : a < q' + 1 :=
          Nat.lt_of_mul_lt_mul_left (a := period) (by
            rw [Nat.mul_add, Nat.mul_one]
            omega)
        omega

private theorem le_sub_of_add_le_right (a b c : Nat)
    (h : a + b ≤ c) : a ≤ c - b := by
  have hb : b ≤ c := by omega
  have hc := Nat.sub_add_cancel hb
  omega

structure FillDrawFacts
    (first period T last pen gap : Nat) where
  periodPos : 0 < period
  firstLower : gap + 1 ≤ first
  firstLePen : first ≤ pen
  penMod : (pen - first) % period = 0
  penLtLast : pen < last
  lastMod : (last - first) % period = 0
  lastLtWindow : last < T
  penPeriod : pen + period = last
  penGapLeLast : pen + gap ≤ last
  penGapLeStart : pen + gap ≤ T - gap
  noBetween : ∀ r, pen < r → r < last →
    (r - first) % period ≠ 0
  noAfter : ∀ r, last < r → r < T →
    (r - first) % period ≠ 0

private theorem fill_draw_facts {m : Nat}
    (B : Nat) (hm : 0 < m) (s : Fin m → Snapshot)
    (a : Fin m) (g G T : Nat)
    (hg : 1 ≤ g) (hgG : g ≤ G)
    (hwindow : T = 64 * (G + 1)) :
    let first := gapFirstDrawRound B hm s a g
    let period := 8 * g + 9
    let last := fillLastDraw first period T
    let pen := last - period
    FillDrawFacts first period T last pen g := by
  let first := gapFirstDrawRound B hm s a g
  let period := 8 * g + 9
  let last := fillLastDraw first period T
  let pen := last - period
  change FillDrawFacts first period T last pen g
  have hperiod : 0 < period := by
    dsimp [period]
    omega
  have hfirstLower : g + 1 ≤ first := by
    dsimp [first, gapFirstDrawRound]
    omega
  have hfirstUpper : first ≤ g + 1 + (8 * g + 8) := by
    dsimp [first, gapFirstDrawRound]
    exact Nat.add_le_add_left (Nat.min_le_left _ _) (g + 1)
  have hfirstPos : 0 < first := by omega
  have hsecondT : first + period < T := by
    change first + (8 * g + 9) < T
    rw [hwindow]
    omega
  have hsched : ScheduledLastFacts first period T last := by
    simpa only [last] using
      scheduled_last_facts first period T hperiod hfirstPos
        (by omega)
  have hcandMod : (first + period - first) % period = 0 := by
    rw [show first + period - first = period by omega, Nat.mod_self]
  have hcandLe : first + period ≤ last :=
    hsched.maximal (first + period) (by omega) hsecondT hcandMod
  have hfirstLast : first < last := by omega
  have hpred := hsched.predecessor hfirstLast
  have hperiodLeLast : period ≤ last := by omega
  have hpenPeriod : pen + period = last := by
    dsimp [pen]
    exact Nat.sub_add_cancel hperiodLeLast
  have hpenLast : pen < last := by omega
  have hpenGapLast : pen + g ≤ last := by
    change pen + g ≤ last
    dsimp [period] at hpenPeriod
    omega
  have hpenTwoGap : (pen + g) + g ≤ T := by
    dsimp [period] at hpenPeriod
    have hlastLe : last ≤ T := Nat.le_of_lt hsched.lastLt
    omega
  have hpenGapStart : pen + g ≤ T - g :=
    le_sub_of_add_le_right (pen + g) g T hpenTwoGap
  refine {
    periodPos := hperiod
    firstLower := hfirstLower
    firstLePen := by simpa only [pen] using hpred.1
    penMod := by simpa only [pen] using hpred.2.1
    penLtLast := hpenLast
    lastMod := hsched.lastMod
    lastLtWindow := hsched.lastLt
    penPeriod := hpenPeriod
    penGapLeLast := hpenGapLast
    penGapLeStart := hpenGapStart
    noBetween := ?_
    noAfter := ?_ }
  · intro r hrPen hrLast
    exact hpred.2.2 r (by simpa only [pen] using hrPen) hrLast
  · intro r hrLast hrT hmod
    have hfr : first ≤ r :=
      Nat.le_trans hsched.firstLe (Nat.le_of_lt hrLast)
    have hle := hsched.maximal r hfr hrT hmod
    omega

/-- Four source-bit requirements determined by the initial snapshot, the two
fixed gaps, and the window length. -/
def fillLossPositions {m : Nat}
    (B : Nat) (hm : 0 < m) (s : Fin m → Snapshot)
    (q : AnchorComparison m) (T : Nat) :
    List (Counting.BitRequirement m) :=
  let firstA := gapFirstDrawRound B hm s q.a q.gA
  let firstB := gapFirstDrawRound B hm s q.b q.gB
  let periodA := 8 * q.gA + 9
  let periodB := 8 * q.gB + 9
  let lastA := fillLastDraw firstA periodA T
  let lastB := fillLastDraw firstB periodB T
  let penA := lastA - periodA
  let penB := lastB - periodB
  [ { round := penA, site := q.a, value := false }
  , { round := lastA, site := q.a, value := false }
  , { round := penB, site := q.b, value := true }
  , { round := lastB, site := q.b, value := true } ]

/-! ## Words, prefixes, and prescribed bits -/

private theorem boundedRunWord_val
    {m : Nat} (B : Nat) (hm : 0 < m) (hB : m < B)
    (x : HeightBoundedState m B) :
    ∀ u : List (Fin (2 ^ m)),
      (runWord
        (boundedHeightNext B hm (heightPres B hm hB)) x u).1 =
      runWord (heightChain B hm) x.1 u := by
  intro u
  induction u generalizing x with
  | nil => rfl
  | cons e u ih =>
      change
        (runWord
          (boundedHeightNext B hm (heightPres B hm hB))
          (boundedHeightNext B hm (heightPres B hm hB) x e) u).1 =
        runWord (heightChain B hm) (heightChain B hm x.1 e) u
      simpa [boundedHeightNext] using
        ih (boundedHeightNext B hm (heightPres B hm hB) x e)

private theorem runWord_heightChain_eq_runRounds
    {m : Nat} (B : Nat) (hm : 0 < m)
    (s : Fin m → Snapshot) :
    ∀ u : List (Fin (2 ^ m)),
      runWord (heightChain B hm) s u =
        runRounds B hm (u.map bitsOf) s := by
  intro u
  induction u generalizing s with
  | nil => rfl
  | cons e u ih =>
      change
        runWord (heightChain B hm) (heightChain B hm s e) u =
          runRounds B hm (u.map bitsOf)
            (logicalRound B hm (bitsOf e) s)
      simpa [heightChain] using ih (heightChain B hm s e)

private theorem boundedPrefixState_eq_gapState
    {m : Nat} (B : Nat) (hm : 0 < m) (hB : m < B)
    (x : HeightBoundedState m B)
    (u : List (Fin (2 ^ m))) (t : Nat) :
    (boundedPrefixState B hm hB x u t).1 =
      gapState B hm (u.map bitsOf) x.1 t := by
  unfold boundedPrefixState gapState
  rw [boundedRunWord_val B hm hB x]
  rw [runWord_heightChain_eq_runRounds B hm x.1]
  rw [List.map_take]

/-- The actual bit vector of a word round, totalized outside the word. -/
def wordRoundBits {m : Nat}
    (u : List (Fin (2 ^ m))) (r : Nat) : Fin m → Bool :=
  if h : r < u.length then bitsOf u[r] else fun _ => false

private theorem wordRoundBits_at {m : Nat}
    (u : List (Fin (2 ^ m))) (r : Nat) (hr : r < u.length)
    (i : Fin m) :
    wordRoundBits u r i = bitsOf u[r] i := by
  simp [wordRoundBits, hr]

private theorem gapRoundBits_map_eq {m : Nat}
    (u : List (Fin (2 ^ m))) (r : Nat)
    (hr : r < (u.map bitsOf).length) :
    gapRoundBits (u.map bitsOf) r hr = wordRoundBits u r := by
  have hu : r < u.length := by
    simpa only [List.length_map] using hr
  funext i
  simp [gapRoundBits, wordRoundBits, hu]

private theorem prescribed_of_mem {m : Nat}
    (p : Counting.BitRequirement m) :
    ∀ (ps : List (Counting.BitRequirement m))
      (u : List (Fin (2 ^ m))),
      p ∈ ps → Counting.prescribed ps u = true →
      Counting.prescribed [p] u = true := by
  intro ps u hp hall
  induction ps with
  | nil => cases hp
  | cons q qs ih =>
      simp only [List.mem_cons] at hp
      simp only [Counting.prescribed, List.all_cons,
        Bool.and_eq_true] at hall
      rcases hp with hhead | htail
      · subst q
        simpa [Counting.prescribed] using hall.1
      · apply ih htail
        exact hall.2

private theorem prescribed_single_value {m : Nat}
    (site : Fin m) (value : Bool) :
    ∀ (r : Nat) (u : List (Fin (2 ^ m)))
      (hr : r < u.length),
      Counting.prescribed
        [{ round := r, site := site, value := value }] u = true →
      bitsOf u[r] site = value := by
  intro r
  induction r with
  | zero =>
      intro u hr hp
      cases u with
      | nil => simp at hr
      | cons e u =>
          change bitsOf e site = value
          change (decide (bitsOf e site = value) && true) = true at hp
          have hd : decide (bitsOf e site = value) = true := by
            cases h : decide (bitsOf e site = value) <;>
              simp [h] at hp ⊢
          exact of_decide_eq_true hd
  | succ r ih =>
      intro u hr hp
      cases u with
      | nil => simp at hr
      | cons e u =>
          have hr' : r < u.length := by
            simp only [List.length_cons] at hr
            omega
          have hp' : Counting.prescribed
              [{ round := r, site := site, value := value }] u = true := by
            change Counting.prescribed
              [{ round := r, site := site, value := value }] u = true at hp
            exact hp
          exact ih u hr' hp'

/-! `gapFixed_of_live_no_internal` is supplied by `FillGap` with the
identical theorem name and statement, so it must not be redeclared here. -/

/-! ## Two equal-valued draws give one uninterrupted role window -/

private theorem same_value_role_window {m : Nat}
    (B : Nat) (hm : 0 < m)
    (bs : List (Fin m → Bool)) (s : Fin m → Snapshot)
    (a b : Fin m) (g T : Nat)
    (hgm : g ≤ m) (hb : b = gapSite hm a g)
    (hbits : T ≤ bs.length)
    (hf : gapFixed B hm bs s a b g T)
    (pen last start final : Nat) (v : Bool)
    (hpenT : pen < T) (hlastT : last < T)
    (hfinalT : final ≤ T)
    (hpenLast : pen < last)
    (hpenGapLast : pen + g ≤ last)
    (hpenGapStart : pen + g ≤ start)
    (hdrawPen : gapDraw B hm bs s a pen)
    (hdrawLast : gapDraw B hm bs s a last)
    (hbitPen :
      (gapRoundBits bs pen (Nat.lt_of_lt_of_le hpenT hbits)) a = v)
    (hbitLast :
      (gapRoundBits bs last (Nat.lt_of_lt_of_le hlastT hbits)) a = v)
    (hnoPen : ∀ q, pen < q → q < last →
      ¬ gapDraw B hm bs s a q)
    (hnoLast : ∀ q, last < q → q < final →
      ¬ gapDraw B hm bs s a q) :
    ∀ t (hst : start ≤ t) (htf : t < final)
      (j : Nat) (hj : j < g),
      (afterPhaseTwo B hm
        (gapRoundBits bs t
          (Nat.lt_of_lt_of_le
            (Nat.lt_of_lt_of_le htf hfinalT) hbits))
        (gapState B hm bs s t) (gapSite hm a j)).role = v := by
  intro t hst htf j hj
  have hreach : pen + j ≤ t := by omega
  by_cases hlastFinal : last < final
  · have hfinalPredT : final - 1 < T := by omega
    have hlastPred : last ≤ final - 1 := by omega
    have hroles := gap_role_two_draws B hm bs s a b g T
      hgm hb hbits hf pen last (final - 1)
      hpenT hlastT hfinalPredT hpenLast hlastPred v
      hbitPen hbitLast hdrawPen hdrawLast hnoPen (by
        intro q hqLast hqPred
        apply hnoLast q hqLast
        omega)
    exact hroles j hj t hreach (by omega)
  · have htLast : t < last := by omega
    have hlastPredT : last - 1 < T := by omega
    have hpenPred : pen ≤ last - 1 := by omega
    have hroles := gap_role B hm bs s a b g T hgm hb hbits hf
      pen (last - 1) hpenT hlastPredT hpenPred v hbitPen hdrawPen (by
        intro q hqPen hqPred
        apply hnoPen q hqPen
        omega)
    exact hroles j hj t hreach (by omega)

/-! ## Converting accepted FillGap positions to Count requirements -/

/-- Convert the accepted tuple representation to `Counting.BitRequirement`. -/
def fillLossRequirement {m : Nat}
    (p : Nat × Fin m × Bool) : Counting.BitRequirement m :=
  { round := p.1, site := p.2.1, value := p.2.2 }

/-- The four requirements used by the exact LossAlt interface. -/
def fillLossRequirements {m : Nat}
    (B : Nat) (hm : 0 < m) (s : Fin m → Snapshot)
    (a b c : Fin m) (gA gB G T : Nat) :
    List (Counting.BitRequirement m) :=
  (fourDrawPositions B hm s a b c gA gB G T).map
    fillLossRequirement

private theorem fillLossRequirements_length
    {m : Nat} (B : Nat) (hm : 0 < m)
    (s : Fin m → Snapshot) (a b c : Fin m)
    (gA gB G T : Nat) :
    (fillLossRequirements B hm s a b c gA gB G T).length = 4 := by
  simp [fillLossRequirements, fourDrawPositions]

private theorem fillLossRequirements_range
    {m : Nat} (B G T : Nat) (hm : 0 < m)
    (s : Fin m → Snapshot) (a b c : Fin m) (gA gB : Nat)
    (hrange : ∀ r i v, (r, i, v) ∈
      fourDrawPositions B hm s a b c gA gB G T → r < T) :
    Counting.RequirementsInRange T
      (fillLossRequirements B hm s a b c gA gB G T) := by
  unfold Counting.RequirementsInRange
  intro p hp
  unfold fillLossRequirements at hp
  rw [List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  simpa [fillLossRequirement] using hrange q.1 q.2.1 q.2.2 hq

private theorem fillLoss_nodup_map_of_injective
    {α β : Type} (l : List α) (hl : l.Nodup)
    (f : α → β) (hf : Function.Injective f) :
    (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have hp := List.nodup_cons.mp hl
      apply List.nodup_cons.mpr
      constructor
      · intro hmem
        obtain ⟨b, hb, hba⟩ := List.mem_map.mp hmem
        have heq : b = a := hf hba
        subst b
        exact hp.1 hb
      · exact ih hp.2

private def fillLossCoordinate {m : Nat}
    (p : Nat × Fin m) : Nat × Nat :=
  (p.1, p.2.val)

private theorem fillLossCoordinate_injective {m : Nat} :
    Function.Injective (fillLossCoordinate (m := m)) := by
  intro p q h
  change (p.1, p.2.val) = (q.1, q.2.val) at h
  apply Prod.ext
  · exact congrArg (fun z : Nat × Nat => z.1) h
  · apply Fin.ext
    exact congrArg (fun z : Nat × Nat => z.2) h

private theorem fillLossRequirements_distinct
    {m : Nat} (B : Nat) (hm : 0 < m)
    (s : Fin m → Snapshot) (a b c : Fin m)
    (gA gB G T : Nat)
    (hdist : ((fourDrawPositions B hm s a b c gA gB G T).map
      drawCoordinate).Nodup) :
    Counting.RequirementsDistinct
      (fillLossRequirements B hm s a b c gA gB G T) := by
  unfold Counting.RequirementsDistinct
  change (((fillLossRequirements B hm s a b c gA gB G T).map
    (fun p => (p.round, p.site.val))).Nodup)
  have hnodup := fillLoss_nodup_map_of_injective
    ((fourDrawPositions B hm s a b c gA gB G T).map drawCoordinate)
    hdist (fillLossCoordinate (m := m))
    (fillLossCoordinate_injective (m := m))
  unfold fillLossRequirements
  rw [List.map_map]
  simpa [List.map_map, fillLossRequirement, drawCoordinate,
    fillLossCoordinate, Function.comp_def] using hnodup

private theorem prescribed_carries_positions
    {m : Nat} (B G T : Nat) (hm : 0 < m)
    (s : Fin m → Snapshot) (a b c : Fin m) (gA gB : Nat)
    (u : List (Fin (2 ^ m))) (hlen : u.length = T)
    (hrange : ∀ r i v, (r, i, v) ∈
      fourDrawPositions B hm s a b c gA gB G T → r < T)
    (hpres : Counting.prescribed
      (fillLossRequirements B hm s a b c gA gB G T) u = true) :
    CarriesPositions (u.map bitsOf)
      (fourDrawPositions B hm s a b c gA gB G T) := by
  unfold CarriesPositions
  intro r i v hmem
  let p : Counting.BitRequirement m :=
    { round := r, site := i, value := v }
  have hp : p ∈ fillLossRequirements B hm s a b c gA gB G T := by
    unfold fillLossRequirements
    apply List.mem_map.mpr
    exact ⟨(r, i, v), hmem, rfl⟩
  have hrT : r < T := hrange r i v hmem
  have hru : r < u.length := by
    rw [hlen]
    exact hrT
  have hsingle := prescribed_of_mem p
    (fillLossRequirements B hm s a b c gA gB G T) u hp hpres
  have hbit : bitsOf u[r] i = v := by
    apply prescribed_single_value i v r u hru
    simpa only [p] using hsingle
  have hrmap : r < (u.map bitsOf).length := by
    simpa only [List.length_map] using hru
  refine ⟨hrmap, ?_⟩
  have heq := gapRoundBits_map_eq u r hrmap
  rw [heq]
  rw [wordRoundBits_at u r hru i]
  exact hbit

/-! ## The exact LossAlt interface -/

/-- The four-bit FillGap bridge at the exact interface expected by LossAlt.
`FillLossInterface` is Type-valued, so this declaration is necessarily a
`def`, not a `theorem`; its requested full type is unchanged. -/
noncomputable def fill_loss_interface {m : Nat} (B : Nat) (hm : 0 < m)
    (hB : m < B) :
    ∀ x : HeightBoundedState m B,
      2 ≤ boundedAnchorCount (B := B) hm x →
      FillLossInterface B hm hB x := by
  intro x htwo q hq hgAG hgBG
  let k := boundedAnchorCount (B := B) hm x
  let G := gapCeil m k
  let T := gapWindowLen m k
  have htwoRaw : 2 ≤ anchorCount hm x.1 := by
    simpa only [boundedAnchorCount] using htwo
  have geom := heightComparison_geometry hm x.1 q htwoRaw hq
  have hgAG' : q.gA ≤ G := by
    simpa only [G, k] using hgAG
  have hgBG' : q.gB ≤ G := by
    simpa only [G, k] using hgBG
  have hanchorA : IsAnchor hm x.1 q.a :=
    heightComparison_start_anchor hm x.1 q hq q.a (by
      simp [comparisonSites])
  have hanchorB : IsAnchor hm x.1 q.b :=
    heightComparison_start_anchor hm x.1 q hq q.b (by
      simp [comparisonSites])
  have hanchorC : IsAnchor hm x.1 q.c :=
    heightComparison_start_anchor hm x.1 q hq q.c (by
      simp [comparisonSites])
  have hwindow : T = 64 * (G + 1) := by rfl
  have hpositions := fourDrawPositions_distinct_lt
    B G T hm x.1 q.a q.b q.c q.gA q.gB
    hwindow geom.gapAPos geom.gapBPos hgAG' hgBG'
    geom.gapSum geom.endA
  let positions := fillLossRequirements
    B hm x.1 q.a q.b q.c q.gA q.gB G T
  refine {
    positions := positions
    positionsFour := ?_
    positionsRange := ?_
    positionsDistinct := ?_
    prescribedLoss := ?_ }
  · dsimp [positions]
    exact fillLossRequirements_length B hm x.1
      q.a q.b q.c q.gA q.gB G T
  · dsimp [positions]
    simpa only [T, k] using
      fillLossRequirements_range B G T hm x.1
        q.a q.b q.c q.gA q.gB hpositions.2
  · dsimp [positions]
    exact fillLossRequirements_distinct B hm x.1
      q.a q.b q.c q.gA q.gB G T hpositions.1
  · intro u hlen hpres
    have hlenT : u.length = T := by
      simpa only [T, k] using hlen
    have hcarry := prescribed_carries_positions
      B G T hm x.1 q.a q.b q.c q.gA q.gB
      u hlenT hpositions.2 (by simpa only [positions] using hpres)
    have hbitsLen : T ≤ (u.map bitsOf).length := by
      have heq : (u.map bitsOf).length = T := by
        simpa only [List.length_map] using hlenT
      rw [heq]
      exact Nat.le_refl T
    have hloss := four_bit_loss_of_gaps
      B G T hm (u.map bitsOf) x.1
      q.a q.b q.c q.gA q.gB
      hwindow geom.gapAPos geom.gapBPos hgAG' hgBG'
      geom.gapSum hB geom.endA geom.endB
      hanchorA hanchorB hanchorC
      geom.interiorA geom.interiorB
      hbitsLen x.2 hcarry
    obtain ⟨t, ht, hlost⟩ := hloss
    refine ⟨t, ?_, ?_⟩
    · simpa only [T, k] using ht
    · rw [boundedPrefixState_eq_gapState B hm hB x u t]
      exact hlost

end L4.Height
