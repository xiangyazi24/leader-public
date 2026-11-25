import Leader.L4.Height.HeightMain
import Leader.L4.Height.Count
import Leader.L4.Height.Arith

namespace L4.Height

open Classical
open L4.Compiler.Native

set_option maxRecDepth 8192
set_option maxHeartbeats 20000000

theorem counting_wordSum_eq {n : Nat}
    (f : List (Fin n) → Nat) :
    ∀ r, Counting.wordSum f r = wordSum f r := by
  intro r
  induction r generalizing f with
  | zero => rfl
  | succ r ih =>
      simp only [Counting.wordSum, wordSum]
      apply sum_ofFn_eq
      intro e
      exact ih (fun v => f (e :: v))

def anchorSites {m : Nat} (hm : 0 < m)
    (s : Fin m → Snapshot) : List (Fin m) :=
  (List.finRange m).filter (fun i => decide (IsAnchor hm s i))

def lostAnchorSites {m : Nat} (hm : 0 < m)
    (start finish : Fin m → Snapshot) : List (Fin m) :=
  (anchorSites hm start).filter
    (fun i => !(decide (IsAnchor hm finish i)))

theorem mem_anchorSites {m : Nat} (hm : 0 < m)
    (s : Fin m → Snapshot) (i : Fin m) :
    i ∈ anchorSites hm s ↔ IsAnchor hm s i := by
  unfold anchorSites
  rw [List.mem_filter]
  constructor
  · intro h
    exact of_decide_eq_true h.2
  · intro h
    exact ⟨List.mem_finRange i, decide_eq_true h⟩

theorem anchorSites_nodup {m : Nat} (hm : 0 < m)
    (s : Fin m → Snapshot) :
    (anchorSites hm s).Nodup := by
  unfold anchorSites
  exact List.Pairwise.filter
    (fun i : Fin m => decide (IsAnchor hm s i))
    (List.nodup_finRange m)

theorem anchorSites_length {m : Nat} (hm : 0 < m)
    (s : Fin m → Snapshot) :
    (anchorSites hm s).length = anchorCount hm s := by
  unfold anchorSites anchorCount
  exact List.countP_eq_length_filter.symm

private theorem pairwise_map_of_pairwise
    {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    (f : α → β) (hf : ∀ a b, R a b → S (f a) (f b)) :
    ∀ {l : List α}, l.Pairwise R → (l.map f).Pairwise S := by
  intro l hl
  induction l with
  | nil => simp
  | cons a l ih =>
      rcases List.pairwise_cons.mp hl with ⟨ha, ht⟩
      apply List.pairwise_cons.mpr
      constructor
      · intro b hb
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
        exact hf a c (ha c hc)
      · exact ih ht

private theorem finRange_pairwise_val_lt :
    ∀ n, (List.finRange n).Pairwise
      (fun a b : Fin n => a.val < b.val)
  | 0 => by simp [List.finRange]
  | n + 1 => by
      unfold List.finRange
      rw [List.ofFn_succ]
      apply List.pairwise_cons.mpr
      constructor
      · intro b hb
        rw [List.mem_ofFn] at hb
        obtain ⟨i, rfl⟩ := hb
        exact Nat.succ_pos i.val
      · have hi := finRange_pairwise_val_lt n
        unfold List.finRange at hi
        have hm := pairwise_map_of_pairwise
          (R := fun a b : Fin n => a.val < b.val)
          (S := fun a b : Fin (n + 1) => a.val < b.val)
          (f := fun i : Fin n => i.succ)
          (fun a b h => by exact Nat.succ_lt_succ h) hi
        simpa only [List.map_ofFn, Function.comp_def] using hm

theorem anchorSites_pairwise_val_lt {m : Nat} (hm : 0 < m)
    (s : Fin m → Snapshot) :
    (anchorSites hm s).Pairwise
      (fun a b : Fin m => a.val < b.val) := by
  unfold anchorSites
  exact List.Pairwise.filter
    (fun i : Fin m => decide (IsAnchor hm s i))
    (finRange_pairwise_val_lt m)

structure AnchorGap (m : Nat) where
  site : Fin m
  gap : Nat
deriving DecidableEq

def anchorGapPairsFrom {m : Nat} (first : Fin m) :
    List (Fin m) → List (AnchorGap m)
  | [] => []
  | [a] => [{ site := a, gap := (m - a.val) + first.val }]
  | a :: b :: rest =>
      { site := a, gap := b.val - a.val } ::
        anchorGapPairsFrom first (b :: rest)

def cyclicAnchorGaps {m : Nat} (hm : 0 < m)
    (s : Fin m → Snapshot) : List (AnchorGap m) :=
  match anchorSites hm s with
  | [] => []
  | a :: rest => anchorGapPairsFrom a (a :: rest)

def gapValues {m : Nat} (ps : List (AnchorGap m)) : List Nat :=
  ps.map AnchorGap.gap

private theorem anchorGapPairsFrom_length {m : Nat}
    (first : Fin m) :
    ∀ l : List (Fin m),
      (anchorGapPairsFrom first l).length = l.length
  | [] => rfl
  | [a] => rfl
  | a :: b :: rest => by
      simpa only [anchorGapPairsFrom, List.length_cons] using
        congrArg Nat.succ
          (anchorGapPairsFrom_length first (b :: rest))

private theorem anchorGapPairsFrom_sites {m : Nat}
    (first : Fin m) :
    ∀ l : List (Fin m),
      (anchorGapPairsFrom first l).map AnchorGap.site = l
  | [] => rfl
  | [a] => rfl
  | a :: b :: rest => by
      simp only [anchorGapPairsFrom, List.map_cons]
      rw [anchorGapPairsFrom_sites first (b :: rest)]

private theorem anchorGapPairsFrom_sum
    {m : Nat} (first a : Fin m) :
    ∀ rest : List (Fin m),
      (a :: rest).Pairwise
        (fun x y : Fin m => x.val < y.val) →
      (gapValues (anchorGapPairsFrom first (a :: rest))).sum =
        (m - a.val) + first.val
  | [], _ => by
      simp [anchorGapPairsFrom, gapValues]
  | b :: rest, hp => by
      rcases List.pairwise_cons.mp hp with ⟨ha, ht⟩
      have hab : a.val < b.val := ha b (by simp)
      have ih := anchorGapPairsFrom_sum first b rest ht
      simp only [anchorGapPairsFrom, gapValues,
        List.map_cons, List.sum_cons]
      change b.val - a.val +
          (gapValues (anchorGapPairsFrom first (b :: rest))).sum =
        (m - a.val) + first.val
      rw [ih]
      have haLt := a.isLt
      have hbLt := b.isLt
      omega

private theorem anchorGapPairsFrom_positive
    {m : Nat} (first a : Fin m) :
    ∀ rest : List (Fin m),
      (a :: rest).Pairwise
        (fun x y : Fin m => x.val < y.val) →
      ∀ p, p ∈ anchorGapPairsFrom first (a :: rest) → 1 ≤ p.gap
  | [], _, p, hp => by
      simp only [anchorGapPairsFrom, List.mem_singleton] at hp
      subst p
      dsimp
      omega
  | b :: rest, hp, p, hmem => by
      rcases List.pairwise_cons.mp hp with ⟨ha, ht⟩
      have hab : a.val < b.val := ha b (by simp)
      simp only [anchorGapPairsFrom, List.mem_cons] at hmem
      rcases hmem with rfl | htail
      · dsimp
        omega
      · exact anchorGapPairsFrom_positive first b rest ht p htail

theorem cyclicAnchorGaps_sites {m : Nat} (hm : 0 < m)
    (s : Fin m → Snapshot) :
    (cyclicAnchorGaps hm s).map AnchorGap.site = anchorSites hm s := by
  unfold cyclicAnchorGaps
  cases h : anchorSites hm s with
  | nil => rfl
  | cons a rest =>
      exact anchorGapPairsFrom_sites a (a :: rest)

theorem cyclicAnchorGaps_length {m : Nat} (hm : 0 < m)
    (s : Fin m → Snapshot) :
    (cyclicAnchorGaps hm s).length = anchorCount hm s := by
  have h := congrArg List.length (cyclicAnchorGaps_sites hm s)
  simpa only [List.length_map, anchorSites_length] using h

theorem cyclicAnchorGaps_sum {m : Nat} (hm : 0 < m)
    (s : Fin m → Snapshot) :
    (gapValues (cyclicAnchorGaps hm s)).sum = m := by
  cases h : anchorSites hm s with
  | nil =>
      obtain ⟨i, hi⟩ := anchor_exists hm s
      have himem := (mem_anchorSites hm s i).2 hi
      rw [h] at himem
      cases himem
  | cons a rest =>
      have hp := anchorSites_pairwise_val_lt hm s
      rw [h] at hp
      have hs := anchorGapPairsFrom_sum a a rest hp
      unfold cyclicAnchorGaps
      rw [h]
      calc
        (gapValues (anchorGapPairsFrom a (a :: rest))).sum =
            (m - a.val) + a.val := hs
        _ = m := by omega

theorem cyclicAnchorGaps_positive {m : Nat} (hm : 0 < m)
    (s : Fin m → Snapshot) :
    ∀ p, p ∈ cyclicAnchorGaps hm s → 1 ≤ p.gap := by
  cases h : anchorSites hm s with
  | nil =>
      obtain ⟨i, hi⟩ := anchor_exists hm s
      have himem := (mem_anchorSites hm s i).2 hi
      rw [h] at himem
      cases himem
  | cons a rest =>
      have hp := anchorSites_pairwise_val_lt hm s
      rw [h] at hp
      intro p hmem
      unfold cyclicAnchorGaps at hmem
      rw [h] at hmem
      exact anchorGapPairsFrom_positive a a rest hp p hmem

theorem cyclicAnchorGap_site_anchor {m : Nat} (hm : 0 < m)
    (s : Fin m → Snapshot) (p : AnchorGap m)
    (hp : p ∈ cyclicAnchorGaps hm s) :
    IsAnchor hm s p.site := by
  have hmapped : p.site ∈ (cyclicAnchorGaps hm s).map AnchorGap.site :=
    List.mem_map.mpr ⟨p, hp, rfl⟩
  rw [cyclicAnchorGaps_sites] at hmapped
  exact (mem_anchorSites hm s p.site).1 hmapped

private theorem le_sum_of_mem :
    ∀ {a : Nat} {l : List Nat}, a ∈ l → a ≤ l.sum
  | _, [], h => by cases h
  | a, b :: l, h => by
      simp only [List.mem_cons] at h
      rcases h with rfl | htail
      · simp only [List.sum_cons]
        omega
      · have ih := le_sum_of_mem htail
        simp only [List.sum_cons]
        omega

theorem cyclicAnchorGap_le {m : Nat} (hm : 0 < m)
    (s : Fin m → Snapshot) (p : AnchorGap m)
    (hp : p ∈ cyclicAnchorGaps hm s) : p.gap ≤ m := by
  have hmem : p.gap ∈ gapValues (cyclicAnchorGaps hm s) :=
    List.mem_map.mpr ⟨p, hp, rfl⟩
  have hle := le_sum_of_mem hmem
  rw [cyclicAnchorGaps_sum hm s] at hle
  exact hle

structure AnchorComparison (m : Nat) where
  a : Fin m
  b : Fin m
  c : Fin m
  gA : Nat
  gB : Nat
deriving DecidableEq

def comparisonSites {m : Nat} (q : AnchorComparison m) : List (Fin m) :=
  [q.a, q.b, q.c]

def comparisonSitesFlat {m : Nat}
    (qs : List (AnchorComparison m)) : List (Fin m) :=
  qs.flatMap comparisonSites

def qualifyingComparisons {m : Nat} (G : Nat) :
    List (AnchorGap m) → List (AnchorComparison m)
  | p :: q :: r :: rest =>
      if p.gap ≤ G ∧ q.gap ≤ G then
        { a := p.site, b := q.site, c := r.site,
          gA := p.gap, gB := q.gap } ::
          qualifyingComparisons G rest
      else qualifyingComparisons G rest
  | _ => []

def twoAnchorComparisons {m : Nat} :
    List (AnchorGap m) → List (AnchorComparison m)
  | p :: q :: _ =>
      [{ a := p.site, b := q.site, c := p.site,
         gA := p.gap, gB := q.gap }]
  | _ => []

def heightComparisons {m : Nat} (hm : 0 < m)
    (s : Fin m → Snapshot) : List (AnchorComparison m) :=
  let ps := cyclicAnchorGaps hm s
  let k := anchorCount hm s
  if k = 2 then twoAnchorComparisons ps
  else qualifyingComparisons (gapCeil m k) ps

private theorem qualifyingComparisons_length {m : Nat} (G : Nat) :
    ∀ ps : List (AnchorGap m),
      (qualifyingComparisons G ps).length =
        qualifyingTriples G (gapValues ps)
  | [] => rfl
  | [p] => rfl
  | [p, q] => rfl
  | p :: q :: r :: rest => by
      have ih :
          (qualifyingComparisons G rest).length =
            qualifyingTriples G (List.map AnchorGap.gap rest) := by
        simpa only [gapValues] using
          (qualifyingComparisons_length G rest)
      by_cases h : p.gap ≤ G ∧ q.gap ≤ G
      · simp only [qualifyingComparisons, if_pos h, List.length_cons,
          gapValues, List.map_cons, qualifyingTriples]
        rw [ih]
        omega
      · simp only [qualifyingComparisons, if_neg h, gapValues,
          List.map_cons, qualifyingTriples, Nat.zero_add]
        exact ih

private theorem qualifyingTriples_le_div_three (G : Nat) :
    ∀ gs : List Nat, qualifyingTriples G gs ≤ gs.length / 3
  | [] => by simp [qualifyingTriples]
  | [a] => by simp [qualifyingTriples]
  | [a, b] => by simp [qualifyingTriples]
  | a :: b :: c :: rest => by
      have ih := qualifyingTriples_le_div_three G rest
      have hdiv :
          (a :: b :: c :: rest).length / 3 = rest.length / 3 + 1 := by
        simp only [List.length_cons]
        have he : rest.length + 1 + 1 + 1 = rest.length + 3 := by omega
        rw [he]
        exact Nat.add_div_right rest.length (by decide : 0 < 3)
      by_cases h : a ≤ G ∧ b ≤ G
      · simp only [qualifyingTriples, if_pos h]
        rw [hdiv]
        omega
      · simp only [qualifyingTriples, if_neg h]
        rw [hdiv]
        omega

private theorem qualifyingComparisons_sites_subset {m : Nat} (G : Nat) :
    ∀ ps : List (AnchorGap m),
      comparisonSitesFlat (qualifyingComparisons G ps) ⊆
        ps.map AnchorGap.site
  | [] => by simp [qualifyingComparisons, comparisonSitesFlat]
  | [p] => by simp [qualifyingComparisons, comparisonSitesFlat]
  | [p, q] => by simp [qualifyingComparisons, comparisonSitesFlat]
  | p :: q :: r :: rest => by
      intro y hy
      by_cases h : p.gap ≤ G ∧ q.gap ≤ G
      · simp only [qualifyingComparisons, if_pos h,
          comparisonSitesFlat, List.flatMap_cons, comparisonSites] at hy
        rw [List.mem_append] at hy
        rcases hy with hhead | htail
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hhead
          simp only [List.map_cons, List.mem_cons]
          rcases hhead with hpa | hqb | hrc
          · exact Or.inl hpa
          · exact Or.inr (Or.inl hqb)
          · exact Or.inr (Or.inr (Or.inl hrc))
        · have ht : y ∈ rest.map AnchorGap.site :=
            qualifyingComparisons_sites_subset G rest htail
          simp only [List.map_cons, List.mem_cons]
          exact Or.inr (Or.inr (Or.inr ht))
      · simp only [qualifyingComparisons, if_neg h] at hy
        have ht : y ∈ rest.map AnchorGap.site :=
          qualifyingComparisons_sites_subset G rest hy
        simp only [List.map_cons, List.mem_cons]
        exact Or.inr (Or.inr (Or.inr ht))

private theorem qualifyingComparisons_sites_nodup {m : Nat} (G : Nat) :
    ∀ ps : List (AnchorGap m),
      (ps.map AnchorGap.site).Nodup →
      (comparisonSitesFlat (qualifyingComparisons G ps)).Nodup
  | [], _ => by simp [qualifyingComparisons, comparisonSitesFlat]
  | [p], _ => by simp [qualifyingComparisons, comparisonSitesFlat]
  | [p, q], _ => by simp [qualifyingComparisons, comparisonSitesFlat]
  | p :: q :: r :: rest, hn => by
      have hsource :
          ([p.site, q.site, r.site] ++ rest.map AnchorGap.site).Nodup := by
        change (p.site :: q.site :: r.site ::
          rest.map AnchorGap.site).Nodup
        simpa only [List.map_cons] using hn
      rcases List.nodup_append.mp hsource with
        ⟨hblock, hrest, hdisj⟩
      have hrec := qualifyingComparisons_sites_nodup G rest hrest
      by_cases h : p.gap ≤ G ∧ q.gap ≤ G
      · simp only [qualifyingComparisons, if_pos h,
          comparisonSitesFlat, List.flatMap_cons, comparisonSites]
        apply List.nodup_append.mpr
        refine ⟨hblock, hrec, ?_⟩
        intro x hx y hy hxy
        have hy' : y ∈ rest.map AnchorGap.site :=
          qualifyingComparisons_sites_subset G rest hy
        exact hdisj x hx y hy' hxy
      · simpa only [qualifyingComparisons, if_neg h] using hrec

private theorem qualifyingComparison_gap_bounds {m : Nat} (G : Nat) :
    ∀ {ps : List (AnchorGap m)} {q : AnchorComparison m},
      q ∈ qualifyingComparisons G ps → q.gA ≤ G ∧ q.gB ≤ G
  | [], q, h => by cases h
  | [p], q, h => by cases h
  | [p, r], q, h => by cases h
  | p :: r :: t :: rest, q, hq => by
      by_cases h : p.gap ≤ G ∧ r.gap ≤ G
      · simp only [qualifyingComparisons, if_pos h, List.mem_cons] at hq
        rcases hq with hhead | htail
        · subst q
          exact h
        · exact qualifyingComparison_gap_bounds G htail
      · simp only [qualifyingComparisons, if_neg h] at hq
        exact qualifyingComparison_gap_bounds G hq

private theorem twoAnchorComparisons_sites_subset {m : Nat} :
    ∀ ps : List (AnchorGap m),
      comparisonSitesFlat (twoAnchorComparisons ps) ⊆
        ps.map AnchorGap.site
  | [] => by simp [twoAnchorComparisons, comparisonSitesFlat]
  | [p] => by simp [twoAnchorComparisons, comparisonSitesFlat]
  | p :: q :: rest => by
      intro y hy
      simp only [twoAnchorComparisons, comparisonSitesFlat,
        List.flatMap_cons, List.flatMap_nil, comparisonSites,
        List.append_nil] at hy
      simp only [List.map_cons, List.mem_cons]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with hpa | hqb | hpc
      · exact Or.inl hpa
      · exact Or.inr (Or.inl hqb)
      · exact Or.inl hpc

private theorem twoAnchorComparisons_length_of_two {m : Nat}
    (ps : List (AnchorGap m)) (h : ps.length = 2) :
    (twoAnchorComparisons ps).length = 1 := by
  cases ps with
  | nil => simp at h
  | cons p rest =>
      cases rest with
      | nil => simp at h
      | cons q tail =>
          cases tail with
          | nil => rfl
          | cons r tail => simp at h

private theorem twoAnchorComparison_gap_le
    {m : Nat} (ps : List (AnchorGap m))
    (hsum : (gapValues ps).sum = m)
    {q : AnchorComparison m} (hq : q ∈ twoAnchorComparisons ps) :
    q.gA ≤ m ∧ q.gB ≤ m := by
  cases ps with
  | nil => cases hq
  | cons p rest =>
      cases rest with
      | nil => cases hq
      | cons r tail =>
          simp only [twoAnchorComparisons, List.mem_singleton] at hq
          subst q
          have hp : p.gap ∈ gapValues (p :: r :: tail) := by
            simp [gapValues]
          have hr : r.gap ∈ gapValues (p :: r :: tail) := by
            simp [gapValues]
          have hple := le_sum_of_mem hp
          have hrle := le_sum_of_mem hr
          rw [hsum] at hple hrle
          exact ⟨hple, hrle⟩

theorem heightComparisons_sites_subset {m : Nat} (hm : 0 < m)
    (s : Fin m → Snapshot) :
    comparisonSitesFlat (heightComparisons hm s) ⊆
      (cyclicAnchorGaps hm s).map AnchorGap.site := by
  unfold heightComparisons
  by_cases h : anchorCount hm s = 2
  · rw [if_pos h]
    exact twoAnchorComparisons_sites_subset _
  · rw [if_neg h]
    exact qualifyingComparisons_sites_subset _ _

theorem heightComparison_start_anchor {m : Nat} (hm : 0 < m)
    (s : Fin m → Snapshot) (q : AnchorComparison m)
    (hq : q ∈ heightComparisons hm s) (y : Fin m)
    (hy : y ∈ comparisonSites q) : IsAnchor hm s y := by
  have hflat : y ∈ comparisonSitesFlat (heightComparisons hm s) :=
    List.mem_flatMap.mpr ⟨q, hq, hy⟩
  have hp := heightComparisons_sites_subset hm s hflat
  obtain ⟨p, hpairs, rfl⟩ := List.mem_map.mp hp
  exact cyclicAnchorGap_site_anchor hm s p hpairs

theorem heightComparisons_many {m : Nat} (hm : 0 < m)
    (s : Fin m → Snapshot)
    (htwo : 2 ≤ anchorCount hm s) :
    anchorCount hm s ≤ 10 * (heightComparisons hm s).length := by
  unfold heightComparisons
  by_cases hk : anchorCount hm s = 2
  · rw [if_pos hk]
    have hpairs : (cyclicAnchorGaps hm s).length = 2 := by
      rw [cyclicAnchorGaps_length, hk]
    have hone := twoAnchorComparisons_length_of_two
      (cyclicAnchorGaps hm s) hpairs
    rw [hone, hk]
    omega
  · rw [if_neg hk]
    have hkthree : 3 ≤ anchorCount hm s := by omega
    have hlen :
        (gapValues (cyclicAnchorGaps hm s)).length = anchorCount hm s := by
      simp only [gapValues, List.length_map, cyclicAnchorGaps_length]
    have hpos : ∀ g,
        g ∈ gapValues (cyclicAnchorGaps hm s) → 1 ≤ g := by
      intro g hg
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
      exact cyclicAnchorGaps_positive hm s p hp
    have hsum := cyclicAnchorGaps_sum hm s
    have ht := triples_qualify
      (gapValues (cyclicAnchorGaps hm s))
      (anchorCount hm s) m hkthree hlen hpos hsum
    rw [← qualifyingComparisons_length] at ht
    exact ht

theorem heightComparisons_length_of_two {m : Nat} (hm : 0 < m)
    (s : Fin m → Snapshot) (hk : anchorCount hm s = 2) :
    (heightComparisons hm s).length = 1 := by
  unfold heightComparisons
  rw [if_pos hk]
  apply twoAnchorComparisons_length_of_two
  rw [cyclicAnchorGaps_length, hk]

theorem heightComparisons_length_le_pred {m : Nat} (hm : 0 < m)
    (s : Fin m → Snapshot) (htwo : 2 ≤ anchorCount hm s) :
    (heightComparisons hm s).length ≤ anchorCount hm s - 1 := by
  by_cases hk : anchorCount hm s = 2
  · calc
      (heightComparisons hm s).length = 1 :=
        heightComparisons_length_of_two hm s hk
      _ ≤ anchorCount hm s - 1 := by
        simpa only [hk] using (by decide : 1 ≤ 2 - 1)
  · have hkthree : 3 ≤ anchorCount hm s := by omega
    unfold heightComparisons
    rw [if_neg hk]
    rw [qualifyingComparisons_length]
    have hb := qualifyingTriples_le_div_three
      (gapCeil m (anchorCount hm s))
      (gapValues (cyclicAnchorGaps hm s))
    have hlen :
        (gapValues (cyclicAnchorGaps hm s)).length = anchorCount hm s := by
      simp only [gapValues, List.length_map, cyclicAnchorGaps_length]
    rw [hlen] at hb
    omega

theorem heightComparison_gap_bounds {m : Nat} (hm : 0 < m)
    (s : Fin m → Snapshot) (q : AnchorComparison m)
    (hq : q ∈ heightComparisons hm s) :
    q.gA ≤ gapCeil m (anchorCount hm s) ∧
      q.gB ≤ gapCeil m (anchorCount hm s) := by
  by_cases hk : anchorCount hm s = 2
  · unfold heightComparisons at hq
    rw [if_pos hk] at hq
    have hle := twoAnchorComparison_gap_le
      (cyclicAnchorGaps hm s) (cyclicAnchorGaps_sum hm s) hq
    have hG : m ≤ gapCeil m (anchorCount hm s) := by
      rw [hk]
      unfold gapCeil
      apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2
      omega
    exact ⟨Nat.le_trans hle.1 hG, Nat.le_trans hle.2 hG⟩
  · unfold heightComparisons at hq
    rw [if_neg hk] at hq
    exact qualifyingComparison_gap_bounds _ hq

theorem heightComparisons_sites_nodup {m : Nat} (hm : 0 < m)
    (s : Fin m → Snapshot) (hk : 3 ≤ anchorCount hm s) :
    (comparisonSitesFlat (heightComparisons hm s)).Nodup := by
  unfold heightComparisons
  rw [if_neg (by omega : anchorCount hm s ≠ 2)]
  apply qualifyingComparisons_sites_nodup
  rw [cyclicAnchorGaps_sites]
  exact anchorSites_nodup hm s

private theorem filter_not_length_add_filter_length
    {α : Type} (p : α → Bool) :
    ∀ l : List α,
      (l.filter (fun a => !(p a))).length +
        (l.filter p).length = l.length := by
  intro l
  induction l with
  | nil => rfl
  | cons a l ih =>
      cases hp : p a <;> simp [hp, ih] <;> omega

private theorem filter_filter_of_imp
    {α : Type} (p q : α → Bool)
    (h : ∀ a, q a = true → p a = true) :
    ∀ l : List α, (l.filter p).filter q = l.filter q := by
  intro l
  induction l with
  | nil => rfl
  | cons a l ih =>
      cases hp : p a with
      | false =>
          cases hq : q a with
          | false => simp [hp, hq, ih]
          | true =>
              have hpt : p a = true := h a hq
              rw [hp] at hpt
              cases hpt
      | true =>
          cases hq : q a <;> simp [hp, hq, ih]

theorem lostAnchorSites_length
    {m : Nat} (hm : 0 < m)
    (start finish : Fin m → Snapshot)
    (hsubset : ∀ i, IsAnchor hm finish i → IsAnchor hm start i) :
    (lostAnchorSites hm start finish).length =
      anchorCount hm start - anchorCount hm finish := by
  have hsurvivors :
      (anchorSites hm start).filter
          (fun i => decide (IsAnchor hm finish i)) =
        anchorSites hm finish := by
    unfold anchorSites
    apply filter_filter_of_imp
    intro i hi
    exact decide_eq_true (hsubset i (of_decide_eq_true hi))
  have hpart := filter_not_length_add_filter_length
    (fun i : Fin m => decide (IsAnchor hm finish i))
    (anchorSites hm start)
  rw [hsurvivors] at hpart
  rw [anchorSites_length hm start, anchorSites_length hm finish] at hpart
  unfold lostAnchorSites
  omega

def activeEventIndices {F : Nat} {α : Type}
    (events : Fin F → α → Bool) (x : α) : List (Fin F) :=
  (List.finRange F).filter (fun j => events j x)

private theorem sum_indicator_eq_countP
    {α : Type} (p : α → Bool) :
    ∀ l : List α,
      (l.map (fun a => Counting.indicator (p a))).sum =
        l.countP p := by
  intro l
  rw [List.countP_eq_length_filter]
  induction l with
  | nil => rfl
  | cons a l ih =>
      have ih' :
          (l.map (fun a => if p a = true then 1 else 0)).sum =
            (l.filter p).length := by
        simpa only [Counting.indicator] using ih
      cases hp : p a <;>
        simp [Counting.indicator, hp] <;> omega

theorem activeEventIndices_length
    {F : Nat} {α : Type}
    (events : Fin F → α → Bool) (x : α) :
    (activeEventIndices events x).length =
      Counting.eventCount events x := by
  change
    ((List.finRange F).filter (fun j => events j x)).length =
      (List.ofFn (fun j : Fin F =>
        Counting.indicator (events j x))).sum
  rw [← List.countP_eq_length_filter]
  rw [← sum_indicator_eq_countP]
  unfold List.finRange
  rw [List.map_ofFn]
  rfl

private theorem filter_length_le {α : Type} (p : α → Bool) :
    ∀ l : List α, (l.filter p).length ≤ l.length
  | [] => by simp
  | a :: l => by
      have ih := filter_length_le p l
      cases h : p a <;> simp [h] <;> omega

theorem eventCount_le_card {F : Nat} {α : Type}
    (events : Fin F → α → Bool) (x : α) :
    Counting.eventCount events x ≤ F := by
  have h :
      (activeEventIndices events x).length ≤
        (List.finRange F).length := by
    unfold activeEventIndices
    exact filter_length_le (fun j : Fin F => events j x)
      (List.finRange F)
  rw [activeEventIndices_length, List.length_finRange] at h
  exact h

private theorem nodup_map_of_injective
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

def activeWitnesses {F : Nat} {α β : Type}
    (events : Fin F → α → Bool) (witness : Fin F → β)
    (x : α) : List β :=
  (activeEventIndices events x).map witness

private theorem activeWitnesses_nodup
    {F : Nat} {α β : Type}
    (events : Fin F → α → Bool) (witness : Fin F → β)
    (x : α) (hinj : Function.Injective witness) :
    (activeWitnesses events witness x).Nodup := by
  unfold activeWitnesses
  apply nodup_map_of_injective
  · unfold activeEventIndices
    exact List.Pairwise.filter
      (fun j => events j x) (List.nodup_finRange F)
  · exact hinj

private theorem activeWitnesses_length
    {F : Nat} {α β : Type}
    (events : Fin F → α → Bool) (witness : Fin F → β)
    (x : α) :
    (activeWitnesses events witness x).length =
      Counting.eventCount events x := by
  unfold activeWitnesses
  rw [List.length_map, activeEventIndices_length]

theorem eventCount_le_anchor_loss
    {m F : Nat} {α : Type}
    (hm : 0 < m)
    (start finish : Fin m → Snapshot)
    (events : Fin F → α → Bool) (z : α)
    (witness : Fin F → Fin m)
    (hinj : Function.Injective witness)
    (hanchors : ∀ i, IsAnchor hm finish i → IsAnchor hm start i)
    (hstart : ∀ j, IsAnchor hm start (witness j))
    (hlost : ∀ j, events j z = true →
      ¬ IsAnchor hm finish (witness j)) :
    Counting.eventCount events z ≤
      anchorCount hm start - anchorCount hm finish := by
  have hsub :
      activeWitnesses events witness z ⊆
        lostAnchorSites hm start finish := by
    intro y hy
    unfold activeWitnesses at hy
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hy
    have hjparts := List.mem_filter.mp hj
    have hevent : events j z = true := hjparts.2
    unfold lostAnchorSites
    apply List.mem_filter.mpr
    constructor
    · unfold anchorSites
      apply List.mem_filter.mpr
      exact ⟨List.mem_finRange _, decide_eq_true (hstart j)⟩
    · by_cases hfinish : IsAnchor hm finish (witness j)
      · exact False.elim ((hlost j hevent) hfinish)
      · simp [hfinish]
  have hlen := List.Nodup.length_le_of_subset
    (activeWitnesses_nodup events witness z hinj) hsub
  rw [activeWitnesses_length,
    lostAnchorSites_length hm start finish hanchors] at hlen
  exact hlen

private theorem injective_of_ofFn_nodup
    {α : Type} {n : Nat} (f : Fin n → α)
    (hn : (List.ofFn f).Nodup) : Function.Injective f := by
  induction n with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ n ih =>
      rw [List.ofFn_succ, List.nodup_cons] at hn
      intro i j hij
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
      · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
        · rfl
        · exfalso
          apply hn.1
          rw [List.mem_ofFn]
          exact ⟨j, hij.symm⟩
      · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
        · exfalso
          apply hn.1
          rw [List.mem_ofFn]
          exact ⟨i, hij⟩
        · have heq := ih (fun t : Fin n => f t.succ) hn.2 hij
          exact congrArg Fin.succ heq

private theorem indexed_selection_nodup
    {m : Nat} :
    ∀ (qs : List (AnchorComparison m))
      (pick : Fin qs.length → Fin m),
      (∀ j, pick j ∈ comparisonSites qs[j.val]) →
      (comparisonSitesFlat qs).Nodup →
      (List.ofFn pick).Nodup := by
  intro qs
  induction qs with
  | nil =>
      intro pick hmem hflat
      simp
  | cons q qs ih =>
      intro pick hmem hflat
      rw [List.ofFn_succ, List.nodup_cons]
      have happ :
          (comparisonSites q ++ comparisonSitesFlat qs).Nodup := by
        simpa [comparisonSitesFlat] using hflat
      rcases List.nodup_append.mp happ with
        ⟨hblock, hrest, hdisj⟩
      constructor
      · intro htail
        rw [List.mem_ofFn] at htail
        obtain ⟨j, hj⟩ := htail
        have hhead : pick 0 ∈ comparisonSites q := by
          simpa using hmem (0 : Fin (q :: qs).length)
        have htailmem :
            pick j.succ ∈ comparisonSites qs[j.val] := by
          simpa using hmem j.succ
        have hflatmem : pick j.succ ∈ comparisonSitesFlat qs :=
          List.mem_flatMap.mpr
            ⟨qs[j.val], List.getElem_mem _, htailmem⟩
        exact hdisj (pick 0) hhead (pick j.succ) hflatmem hj.symm
      · apply ih (fun j => pick j.succ)
        · intro j
          simpa using hmem j.succ
        · exact hrest

theorem runWord_anchor_subset
    {m : Nat} (B : Nat) (hm : 0 < m) (hB : m < B)
    (x : HeightBoundedState m B) :
    ∀ (u : List (Fin (2 ^ m))) (i : Fin m),
      IsAnchor hm
          (runWord
            (boundedHeightNext B hm (heightPres B hm hB)) x u).1 i →
        IsAnchor hm x.1 i := by
  intro u
  induction u generalizing x with
  | nil =>
      intro i hi
      exact hi
  | cons e u ih =>
      intro i hi
      have hnext := ih
        (boundedHeightNext B hm (heightPres B hm hB) x e) i
        (by simpa [runWord] using hi)
      change IsAnchor hm
        (logicalRound B hm (bitsOf e) x.1) i at hnext
      exact anchor_mono B hm hB (bitsOf e) x.1 x.2 i hnext

theorem stoppedRun_anchor_subset
    {m : Nat} (B : Nat) (hm : 0 < m) (hB : m < B)
    (x : HeightBoundedState m B) :
    ∀ (u : List (Fin (2 ^ m))) (i : Fin m),
      IsAnchor hm
          (stoppedRun
            (boundedHeightNext B hm (heightPres B hm hB))
            (boundedHeightStop (B := B) hm) x u).1 i →
        IsAnchor hm x.1 i := by
  intro u
  induction u generalizing x with
  | nil =>
      intro i hi
      exact hi
  | cons e u ih =>
      intro i hi
      by_cases hx : boundedHeightStop (B := B) hm x
      · simpa only [stoppedRun, hx, if_pos] using hi
      · have htail :
          IsAnchor hm
            (stoppedRun
              (boundedHeightNext B hm (heightPres B hm hB))
              (boundedHeightStop (B := B) hm)
              (boundedHeightNext B hm (heightPres B hm hB) x e) u).1 i := by
            simpa only [stoppedRun, hx, if_false] using hi
        have hnext := ih
          (boundedHeightNext B hm (heightPres B hm hB) x e) i htail
        change IsAnchor hm
          (logicalRound B hm (bitsOf e) x.1) i at hnext
        exact anchor_mono B hm hB (bitsOf e) x.1 x.2 i hnext

private theorem runWord_append
    {α : Type} {n : Nat}
    (next : α → Fin n → α) (x : α)
    (u v : List (Fin n)) :
    runWord next x (u ++ v) = runWord next (runWord next x u) v := by
  unfold runWord
  rw [List.foldl_append]

private theorem stoppedRun_eq_runWord_of_endpoint_not_stop
    {α : Type} {n : Nat}
    (next : α → Fin n → α) (stop : α → Prop) :
    ∀ (x : α) (u : List (Fin n)),
      ¬ stop (stoppedRun next stop x u) →
      stoppedRun next stop x u = runWord next x u := by
  intro x u
  induction u generalizing x with
  | nil => intro h; rfl
  | cons e u ih =>
      intro hfinal
      by_cases hx : stop x
      · have hf : ¬ stop x := by
          simpa only [stoppedRun, hx, if_pos] using hfinal
        exact False.elim (hf hx)
      · have htail :
          ¬ stop (stoppedRun next stop (next x e) u) := by
            simpa only [stoppedRun, hx, if_false] using hfinal
        simp only [stoppedRun, hx, if_false]
        change stoppedRun next stop (next x e) u =
          runWord next (next x e) u
        exact ih (next x e) htail

theorem prefix_loss_persists
    {m : Nat} (B : Nat) (hm : 0 < m) (hB : m < B)
    (x : HeightBoundedState m B)
    (u : List (Fin (2 ^ m))) (t : Nat) (y : Fin m)
    (hlost : ¬ IsAnchor hm
      (runWord
        (boundedHeightNext B hm (heightPres B hm hB))
        x (u.take t)).1 y) :
    ¬ IsAnchor hm
      (runWord
        (boundedHeightNext B hm (heightPres B hm hB)) x u).1 y := by
  intro hfull
  let next := boundedHeightNext B hm (heightPres B hm hB)
  have happ := runWord_append next x (u.take t) (u.drop t)
  have hdecomp : u.take t ++ u.drop t = u :=
    List.take_append_drop t u
  rw [hdecomp] at happ
  have htail :
      IsAnchor hm
        (runWord next (runWord next x (u.take t)) (u.drop t)).1 y := by
    rw [← happ]
    exact hfull
  have hpref := runWord_anchor_subset B hm hB
    (runWord next x (u.take t)) (u.drop t) y htail
  exact hlost hpref

def boundedPrefixState
    {m : Nat} (B : Nat) (hm : 0 < m) (hB : m < B)
    (x : HeightBoundedState m B)
    (u : List (Fin (2 ^ m))) (t : Nat) : HeightBoundedState m B :=
  runWord
    (boundedHeightNext B hm (heightPres B hm hB)) x (u.take t)

structure FourDrawLoss
    {m : Nat} (B : Nat) (hm : 0 < m) (hB : m < B)
    (x : HeightBoundedState m B) (q : AnchorComparison m) where
  positions : List (Counting.BitRequirement m)
  positionsFour : positions.length = 4
  positionsRange : Counting.RequirementsInRange
    (gapWindowLen m (boundedAnchorCount (B := B) hm x)) positions
  positionsDistinct : Counting.RequirementsDistinct positions
  prescribedLoss : ∀ u,
    u.length = gapWindowLen m (boundedAnchorCount (B := B) hm x) →
    Counting.prescribed positions u = true →
    ∃ t, t ≤ gapWindowLen m (boundedAnchorCount (B := B) hm x) ∧
      (¬ IsAnchor hm (boundedPrefixState B hm hB x u t).1 q.a ∨
       ¬ IsAnchor hm (boundedPrefixState B hm hB x u t).1 q.b ∨
       ¬ IsAnchor hm (boundedPrefixState B hm hB x u t).1 q.c)

abbrev FillLossInterface
    {m : Nat} (B : Nat) (hm : 0 < m) (hB : m < B)
    (x : HeightBoundedState m B) :=
  ∀ q : AnchorComparison m,
    q ∈ heightComparisons hm x.1 →
    q.gA ≤ gapCeil m (boundedAnchorCount (B := B) hm x) →
    q.gB ≤ gapCeil m (boundedAnchorCount (B := B) hm x) →
    FourDrawLoss B hm hB x q

noncomputable def fillResultAt
    {m : Nat} (B : Nat) (hm : 0 < m) (hB : m < B)
    (x : HeightBoundedState m B)
    (hfill : FillLossInterface B hm hB x)
    (j : Fin (heightComparisons hm x.1).length) :
    FourDrawLoss B hm hB x
      ((heightComparisons hm x.1)[j.val]) := by
  apply hfill
  · exact List.getElem_mem _
  · exact (heightComparison_gap_bounds hm x.1 _ (List.getElem_mem _)).1
  · exact (heightComparison_gap_bounds hm x.1 _ (List.getElem_mem _)).2

noncomputable def fillPositions
    {m : Nat} (B : Nat) (hm : 0 < m) (hB : m < B)
    (x : HeightBoundedState m B)
    (hfill : FillLossInterface B hm hB x)
    (j : Fin (heightComparisons hm x.1).length) :
    List (Counting.BitRequirement m) :=
  (fillResultAt B hm hB x hfill j).positions

noncomputable def fillEvents
    {m : Nat} (B : Nat) (hm : 0 < m) (hB : m < B)
    (x : HeightBoundedState m B)
    (hfill : FillLossInterface B hm hB x)
    (j : Fin (heightComparisons hm x.1).length)
    (u : List (Fin (2 ^ m))) : Bool :=
  Counting.prescribed (fillPositions B hm hB x hfill j) u

theorem fill_event_loses_at_endpoint
    {m : Nat} (B : Nat) (hm : 0 < m) (hB : m < B)
    (x : HeightBoundedState m B)
    (hfill : FillLossInterface B hm hB x)
    (j : Fin (heightComparisons hm x.1).length)
    (u : List (Fin (2 ^ m)))
    (hlen : u.length = gapWindowLen m
      (boundedAnchorCount (B := B) hm x))
    (hevent : fillEvents B hm hB x hfill j u = true)
    (hnot : boundedAnchorCount (B := B) hm
      (stoppedRun
        (boundedHeightNext B hm (heightPres B hm hB))
        (boundedHeightStop (B := B) hm) x u) ≠ 1) :
    ∃ y,
      y ∈ comparisonSites ((heightComparisons hm x.1)[j.val]) ∧
      ¬ IsAnchor hm
        (stoppedRun
          (boundedHeightNext B hm (heightPres B hm hB))
          (boundedHeightStop (B := B) hm) x u).1 y := by
  let q := (heightComparisons hm x.1)[j.val]
  let next := boundedHeightNext B hm (heightPres B hm hB)
  let stop := boundedHeightStop (B := B) hm
  have hpres :
      Counting.prescribed
        (fillResultAt B hm hB x hfill j).positions u = true := by
    simpa only [fillEvents, fillPositions] using hevent
  have hloss :=
    (fillResultAt B hm hB x hfill j).prescribedLoss u hlen hpres
  obtain ⟨t, ht, hnamed⟩ := hloss
  have hnostop : ¬ stop (stoppedRun next stop x u) := by
    intro hs
    apply hnot
    simpa only [stop, boundedHeightStop, boundedAnchorCount] using hs
  have heq := stoppedRun_eq_runWord_of_endpoint_not_stop
    next stop x u hnostop
  rcases hnamed with ha | hb | hc
  · refine ⟨q.a, by simp [q, comparisonSites], ?_⟩
    have hp := prefix_loss_persists B hm hB x u t q.a ha
    intro hend
    apply hp
    rw [← heq]
    exact hend
  · refine ⟨q.b, by simp [q, comparisonSites], ?_⟩
    have hp := prefix_loss_persists B hm hB x u t q.b hb
    intro hend
    apply hp
    rw [← heq]
    exact hend
  · refine ⟨q.c, by simp [q, comparisonSites], ?_⟩
    have hp := prefix_loss_persists B hm hB x u t q.c hc
    intro hend
    apply hp
    rw [← heq]
    exact hend

theorem fill_eventCount_le_anchor_loss
    {m : Nat} (B : Nat) (hm : 0 < m) (hB : m < B)
    (x : HeightBoundedState m B)
    (htwo : 2 ≤ boundedAnchorCount (B := B) hm x)
    (hfill : FillLossInterface B hm hB x)
    (u : List (Fin (2 ^ m)))
    (hlen : u.length = gapWindowLen m
      (boundedAnchorCount (B := B) hm x)) :
    Counting.eventCount (fillEvents B hm hB x hfill) u ≤
      boundedAnchorCount (B := B) hm x -
        boundedAnchorCount (B := B) hm
          (stoppedRun
            (boundedHeightNext B hm (heightPres B hm hB))
            (boundedHeightStop (B := B) hm) x u) := by
  let qs := heightComparisons hm x.1
  let events := fillEvents B hm hB x hfill
  let next := boundedHeightNext B hm (heightPres B hm hB)
  let stop := boundedHeightStop (B := B) hm
  let finish := stoppedRun next stop x u
  let k := boundedAnchorCount (B := B) hm x
  by_cases htarget : boundedAnchorCount (B := B) hm finish = 1
  · have hcard : Counting.eventCount events u ≤ qs.length :=
      eventCount_le_card events u
    have hfamily : qs.length ≤ k - 1 := by
      simpa only [qs, k, boundedAnchorCount] using
        (heightComparisons_length_le_pred hm x.1 htwo)
    have hle := Nat.le_trans hcard hfamily
    change Counting.eventCount events u ≤
      k - boundedAnchorCount (B := B) hm finish
    calc
      Counting.eventCount events u ≤ k - 1 := hle
      _ = k - boundedAnchorCount (B := B) hm finish := by
        rw [htarget]
  · have hchoice :
        ∀ j : Fin qs.length,
          ∃ y, y ∈ comparisonSites qs[j.val] ∧
            (events j u = true → ¬ IsAnchor hm finish.1 y) := by
      intro j
      by_cases he : events j u = true
      · have hloss := fill_event_loses_at_endpoint
          B hm hB x hfill j u hlen
          (by simpa only [events, qs] using he)
          (by simpa only [finish, k, boundedAnchorCount] using htarget)
        obtain ⟨y, hy, hylost⟩ := hloss
        exact ⟨y, by simpa only [qs] using hy, fun _ => by
          simpa only [finish] using hylost⟩
      · exact ⟨qs[j.val].a, by simp [comparisonSites], fun h =>
          False.elim (he h)⟩
    let witness : Fin qs.length → Fin m :=
      fun j => Classical.choose (hchoice j)
    have hwmem : ∀ j, witness j ∈ comparisonSites qs[j.val] := by
      intro j
      exact (Classical.choose_spec (hchoice j)).1
    have hwactive : ∀ j, events j u = true →
        ¬ IsAnchor hm finish.1 (witness j) := by
      intro j hj
      exact (Classical.choose_spec (hchoice j)).2 hj
    have hwinj : Function.Injective witness := by
      by_cases hk : k = 2
      · have hqone : qs.length = 1 := by
          simpa only [qs, k, boundedAnchorCount] using
            (heightComparisons_length_of_two hm x.1 hk)
        intro i j _
        apply Fin.ext
        have hi := i.isLt
        have hj := j.isLt
        omega
      · have hkthree : 3 ≤ k := by omega
        have hflat : (comparisonSitesFlat qs).Nodup := by
          simpa only [qs, k, boundedAnchorCount] using
            (heightComparisons_sites_nodup hm x.1 hkthree)
        have hselected := indexed_selection_nodup qs witness hwmem hflat
        exact injective_of_ofFn_nodup witness hselected
    have hstart : ∀ j, IsAnchor hm x.1 (witness j) := by
      intro j
      apply heightComparison_start_anchor hm x.1 qs[j.val]
      · exact List.getElem_mem _
      · exact hwmem j
    have hloss := eventCount_le_anchor_loss
      (hm := hm)
      (start := x.1)
      (finish := finish.1)
      (events := events)
      (z := u)
      (witness := witness)
      hwinj
      (fun i hi => by
        exact stoppedRun_anchor_subset B hm hB x u i
          (by simpa only [finish, next, stop] using hi))
      hstart hwactive
    simpa only [events, finish, next, stop, k,
      boundedAnchorCount] using hloss

theorem drift_step_of_events
    {m F : Nat} (B : Nat) (hm : 0 < m) (hB : m < B)
    (x : HeightBoundedState m B)
    (positions : Fin F → List (Counting.BitRequirement m))
    (events : Fin F → List (Fin (2 ^ m)) → Bool)
    (hfour : ∀ j, (positions j).length = 4)
    (hrange : ∀ j,
      Counting.RequirementsInRange
        (gapWindowLen m (boundedAnchorCount (B := B) hm x))
        (positions j))
    (hdistinct : ∀ j, Counting.RequirementsDistinct (positions j))
    (hcontained : ∀ j u,
      Counting.prescribed (positions j) u = true → events j u = true)
    (hmany : boundedAnchorCount (B := B) hm x ≤ 10 * F)
    (hpoint : ∀ u,
      u.length = gapWindowLen m (boundedAnchorCount (B := B) hm x) →
      Counting.eventCount events u ≤
        boundedAnchorCount (B := B) hm x -
          boundedAnchorCount (B := B) hm
            (stoppedRun
              (boundedHeightNext B hm (heightPres B hm hB))
              (boundedHeightStop (B := B) hm) x u)) :
    let k := boundedAnchorCount (B := B) hm x
    160 * wordSum
      (fun u => k - boundedAnchorCount (B := B) hm
        (stoppedRun
          (boundedHeightNext B hm (heightPres B hm hB))
          (boundedHeightStop (B := B) hm) x u))
      (gapWindowLen m k) ≥
        k * (2 ^ m) ^ (gapWindowLen m k) := by
  let k := boundedAnchorCount (B := B) hm x
  let T := gapWindowLen m k
  let next := boundedHeightNext B hm (heightPres B hm hB)
  let stop := boundedHeightStop (B := B) hm
  change
    160 * wordSum
      (fun u => k - boundedAnchorCount (B := B) hm
        (stoppedRun next stop x u)) T ≥
      k * (2 ^ m) ^ T
  have hmeanZero := Counting.four_bit_loss_mean
    (m := m)
    (w := gapWindowLen m (boundedAnchorCount (B := B) hm x))
    (F := F)
    positions events hfour hrange hdistinct hcontained
  rw [counting_wordSum_eq] at hmeanZero
  have hmean :
      F * (2 ^ m) ^ T ≤
        16 * wordSum (fun u => Counting.eventCount events u) T := by
    simpa only [T, k] using hmeanZero
  have hsum :
      wordSum (fun u => Counting.eventCount events u) T ≤
        wordSum
          (fun u => k - boundedAnchorCount (B := B) hm
            (stoppedRun next stop x u)) T := by
    apply wordSum_mono_length
    intro u hu
    simpa only [T, k, next, stop] using hpoint u hu
  have hmany' : k ≤ 10 * F := by
    simpa only [k] using hmany
  calc
    k * (2 ^ m) ^ T
        ≤ (10 * F) * (2 ^ m) ^ T :=
          Nat.mul_le_mul_right ((2 ^ m) ^ T) hmany'
    _ = 10 * (F * (2 ^ m) ^ T) := by ac_rfl
    _ ≤ 10 *
        (16 * wordSum (fun u => Counting.eventCount events u) T) :=
          Nat.mul_le_mul_left 10 hmean
    _ = 160 * wordSum (fun u => Counting.eventCount events u) T := by
      let E := wordSum (fun u => Counting.eventCount events u) T
      change 10 * (16 * E) = 160 * E
      calc
        10 * (16 * E) = (10 * 16) * E :=
          (Nat.mul_assoc 10 16 E).symm
        _ = 160 * E :=
          congrArg (fun z : Nat => z * E)
            (by decide : 10 * 16 = 160)
    _ ≤ 160 * wordSum
        (fun u => k - boundedAnchorCount (B := B) hm
          (stoppedRun next stop x u)) T :=
          Nat.mul_le_mul_left 160 hsum

theorem drift_step_of_interfaces
    {m : Nat} (B : Nat) (hm : 0 < m) (hB : m < B)
    (x : HeightBoundedState m B)
    (htwo : 2 ≤ boundedAnchorCount (B := B) hm x)
    (hfill : FillLossInterface B hm hB x) :
    let k := boundedAnchorCount (B := B) hm x
    160 * wordSum
      (fun u => k - boundedAnchorCount (B := B) hm
        (stoppedRun
          (boundedHeightNext B hm (heightPres B hm hB))
          (boundedHeightStop (B := B) hm) x u))
      (gapWindowLen m k) ≥
        k * (2 ^ m) ^ (gapWindowLen m k) := by
  let F := (heightComparisons hm x.1).length
  let positions : Fin F → List (Counting.BitRequirement m) :=
    fillPositions B hm hB x hfill
  let events : Fin F → List (Fin (2 ^ m)) → Bool :=
    fillEvents B hm hB x hfill
  apply drift_step_of_events B hm hB x positions events
  · intro j
    exact (fillResultAt B hm hB x hfill j).positionsFour
  · intro j
    exact (fillResultAt B hm hB x hfill j).positionsRange
  · intro j
    exact (fillResultAt B hm hB x hfill j).positionsDistinct
  · intro j u h
    simpa only [events, positions, fillEvents, fillPositions] using h
  · simpa only [F, boundedAnchorCount] using
      (heightComparisons_many hm x.1 htwo)
  · intro u hu
    simpa only [events, F] using
      (fill_eventCount_le_anchor_loss B hm hB x htwo hfill u hu)

theorem drift_step_of_fill
    {m : Nat} (B : Nat) (hm : 0 < m) (hB : m < B)
    (hfill : ∀ x : HeightBoundedState m B,
      2 ≤ boundedAnchorCount (B := B) hm x →
      FillLossInterface B hm hB x) :
    ∀ x : HeightBoundedState m B,
      2 ≤ boundedAnchorCount (B := B) hm x →
      let k := boundedAnchorCount (B := B) hm x
      160 * wordSum
        (fun u => k - boundedAnchorCount (B := B) hm
          (stoppedRun
            (boundedHeightNext B hm (heightPres B hm hB))
            (boundedHeightStop (B := B) hm) x u))
        (gapWindowLen m k) ≥
          k * (2 ^ m) ^ (gapWindowLen m k) := by
  intro x htwo
  exact drift_step_of_interfaces B hm hB x htwo (hfill x htwo)

end L4.Height
