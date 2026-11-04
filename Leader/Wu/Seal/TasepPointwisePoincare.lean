import Leader.Wu.Seal.TasepFiniteTime

/-!
# First pointwise Poincare bricks for the seal-sweep TASEP kernel

The imported finite-time module stops at an exact stationary aggregate and an
exact lower bound on the `P P*` common-successor weight of every nontrivial
adjacent swap.  This file starts the separate pointwise layer.

The first issue is geometric rather than analytic: summing over edge labels is
useful only after ruling out duplicate swap targets.  On a ring of size at
least three, two different active adjacent edges cannot produce the same
Boolean configuration.  The proof below unfolds the actual directed-ring
successor and handles its modular wrap directly.  It then packages the active
edges and their swap targets as duplicate-free lists and proves that every
target remains in the same fixed-mass slice.

No Poincare inequality, mixing estimate, or marked-endpoint lower bound is
claimed here.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialSealSweepTasepPointwisePoincareSol

open PPLL PPLLResearchFormulation
open PPLLNoCheckBirthConditionTwoGeometry
open PPartialSealSweepHomeFrontQuotientSol
open PPartialSealSweepABGateBreakthroughSol
open PPartialSealSweepTasepMixingFirstBrickSol
open PPartialSealSweepTasepFiniteTimeSol
open PPartialSealSweepTasepRotationBridgeSol

set_option autoImplicit false

variable {n : Nat}

/-! ## Directed-ring two-step geometry -/

private def tasepFrontConfigDecEq :
    (m : Nat) -> DecidableEq (Fin m -> Bool)
  | 0 => fun F G =>
      isTrue (funext (fun i => Fin.elim0 i))
  | m + 1 => fun F G =>
      if hzero : F 0 = G 0 then
        match tasepFrontConfigDecEq m
            (fun i : Fin m => F i.succ)
            (fun i : Fin m => G i.succ) with
        | isTrue htail =>
            isTrue (funext (fun i =>
              Fin.cases hzero (fun j => congrFun htail j) i))
        | isFalse htail =>
            isFalse (fun hFG =>
              htail (funext (fun i => congrFun hFG i.succ)))
      else
        isFalse (fun hFG => hzero (congrFun hFG 0))

local instance tasepFrontConfigDecidableEq (m : Nat) :
    DecidableEq (Fin m -> Bool) :=
  tasepFrontConfigDecEq m

/-- A directed ring of size at least three has no successor two-cycle. -/
theorem rightNeighbor_rightNeighbor_ne_self_of_three_le
    (ring : DirectedRing n) (hn : 3 <= n) (edge : Fin n) :
    ring.rightNeighbor (ring.rightNeighbor edge) ≠ edge := by
  intro hcycle
  have hv := congrArg Fin.val hcycle
  unfold DirectedRing.rightNeighbor at hv
  dsimp only at hv
  by_cases hfirst : edge.val + 1 < n
  · rw [Nat.mod_eq_of_lt hfirst] at hv
    by_cases hsecond : edge.val + 1 + 1 < n
    · rw [Nat.mod_eq_of_lt hsecond] at hv
      omega
    · have hwrap : edge.val + 1 + 1 = n := by omega
      rw [hwrap, Nat.mod_self] at hv
      omega
  · have hwrap : edge.val + 1 = n := by omega
    rw [hwrap, Nat.mod_self] at hv
    have hone : 1 < n := by omega
    rw [Nat.mod_eq_of_lt hone] at hv
    omega

/-! ## Support of equality between two swap targets -/

/-- If two adjacent-swap targets agree and the first edge is nontrivial, the
first edge lies in the two-coordinate support of the second swap. -/
theorem edge_eq_or_eq_rightNeighbor_of_swapFrontConfigAt_eq
    (ring : DirectedRing n) (F : Fin n -> Bool) (edge other : Fin n)
    (hne : F edge ≠ F (ring.rightNeighbor edge))
    (hswap : swapFrontConfigAt ring F edge =
      swapFrontConfigAt ring F other) :
    edge = other \/ edge = ring.rightNeighbor other := by
  by_cases heo : edge = other
  · exact Or.inl heo
  by_cases her : edge = ring.rightNeighbor other
  · exact Or.inr her
  exfalso
  have hvalue := congrFun hswap edge
  rw [swapFrontConfigAt_edge] at hvalue
  simp [swapFrontConfigAt, heo, her] at hvalue
  exact hne hvalue.symm

/-- The right endpoint of a nontrivial first swap also lies in the
two-coordinate support of any equal second swap target. -/
theorem rightNeighbor_eq_or_eq_rightNeighbor_of_swapFrontConfigAt_eq
    (ring : DirectedRing n) (hn : 1 < n)
    (F : Fin n -> Bool) (edge other : Fin n)
    (hne : F edge ≠ F (ring.rightNeighbor edge))
    (hswap : swapFrontConfigAt ring F edge =
      swapFrontConfigAt ring F other) :
    ring.rightNeighbor edge = other \/
      ring.rightNeighbor edge = ring.rightNeighbor other := by
  by_cases hro : ring.rightNeighbor edge = other
  · exact Or.inl hro
  by_cases hrr : ring.rightNeighbor edge = ring.rightNeighbor other
  · exact Or.inr hrr
  exfalso
  have hvalue := congrFun hswap (ring.rightNeighbor edge)
  rw [swapFrontConfigAt_rightNeighbor ring hn F edge] at hvalue
  simp [swapFrontConfigAt, hro, hrr] at hvalue
  exact hne hvalue

/-- On a ring with at least three sites, a nontrivial adjacent-swap target
determines its edge label.  The second edge need not separately be assumed
nontrivial. -/
theorem edge_eq_of_swapFrontConfigAt_eq_of_endpoint_ne
    (ring : DirectedRing n) (hn : 3 <= n)
    (F : Fin n -> Bool) (edge other : Fin n)
    (hne : F edge ≠ F (ring.rightNeighbor edge))
    (hswap : swapFrontConfigAt ring F edge =
      swapFrontConfigAt ring F other) :
    edge = other := by
  rcases edge_eq_or_eq_rightNeighbor_of_swapFrontConfigAt_eq
      ring F edge other hne hswap with heo | her
  · exact heo
  rcases rightNeighbor_eq_or_eq_rightNeighbor_of_swapFrontConfigAt_eq
      ring (by omega) F edge other hne hswap with hro | hrr
  · exfalso
    have hcycle :
        ring.rightNeighbor (ring.rightNeighbor other) = other := by
      rw [← her]
      exact hro
    exact rightNeighbor_rightNeighbor_ne_self_of_three_le
      ring hn other hcycle
  · exact rightNeighbor_injective ring hrr

/-- The map from a nontrivial edge, packaged with its endpoint inequality, to
its symmetric adjacent-swap target is injective. -/
theorem swapFrontConfigAt_nontrivialEdge_injective
    (ring : DirectedRing n) (hn : 3 <= n) (F : Fin n -> Bool) :
    Function.Injective
      (fun edge : {e : Fin n //
          F e ≠ F (ring.rightNeighbor e)} =>
        swapFrontConfigAt ring F edge.1) := by
  intro edge other hswap
  apply Subtype.ext
  exact edge_eq_of_swapFrontConfigAt_eq_of_endpoint_ne
    ring hn F edge.1 other.1 edge.2 hswap

/-! ## Duplicate-free active-swap target lists -/

private theorem pointwise_nodup_ofFn_of_injective
    {m : Nat} {alpha : Type} (f : Fin m -> alpha)
    (hf : Function.Injective f) :
    (List.ofFn f).Nodup := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.ofFn_succ, List.nodup_cons]
      constructor
      · intro hmem
        rw [List.mem_ofFn] at hmem
        obtain ⟨edge, hedge⟩ := hmem
        have h := hf hedge
        cases h
      · apply ih
        intro edge other hsame
        exact Fin.succ_inj.mp (hf hsame)

private theorem pointwise_nodup_ofFn_id (m : Nat) :
    (List.ofFn (fun edge : Fin m => edge)).Nodup := by
  exact pointwise_nodup_ofFn_of_injective
    (fun edge : Fin m => edge) (fun _ _ h => h)

private theorem pointwise_nodup_filter_of_nodup
    {alpha : Type} (p : alpha -> Bool) (xs : List alpha)
    (hxs : xs.Nodup) :
    (xs.filter p).Nodup := by
  rw [List.nodup_iff_pairwise_ne] at hxs ⊢
  exact hxs.filter p

private theorem pointwise_nodup_map_of_injective_on
    {alpha beta : Type} (xs : List alpha) (f : alpha -> beta)
    (hxs : xs.Nodup)
    (hinj : forall a, a ∈ xs -> forall b, b ∈ xs ->
      f a = f b -> a = b) :
    (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      rw [List.nodup_cons] at hxs
      simp only [List.map_cons]
      rw [List.nodup_cons]
      constructor
      · intro hmem
        rw [List.mem_map] at hmem
        obtain ⟨b, hb, hab⟩ := hmem
        have heq := hinj a (by simp) b (by simp [hb]) hab.symm
        subst b
        exact hxs.1 hb
      · apply ih hxs.2
        intro b hb c hc hbc
        exact hinj b (by simp [hb]) c (by simp [hc]) hbc

private theorem pointwise_sum_map_eq_filter_of_false_zero
    {alpha : Type} (xs : List alpha) (p : alpha -> Bool)
    (weight : alpha -> Nat)
    (hzero : forall x, x ∈ xs -> p x = false -> weight x = 0) :
    (xs.map weight).sum = ((xs.filter p).map weight).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      have htail : forall x, x ∈ xs -> p x = false -> weight x = 0 := by
        intro x hx hp
        exact hzero x (by simp [hx]) hp
      have hrec := ih htail
      cases hp : p a with
      | false =>
          have ha0 := hzero a (by simp) hp
          simp [hp, ha0, hrec]
      | true =>
          simp [hp, hrec]

/-- Edge labels whose adjacent Boolean endpoints differ. -/
def tasepNontrivialSwapEdges (ring : DirectedRing n)
    (F : Fin n -> Bool) : List (Fin n) :=
  (List.ofFn (fun edge : Fin n => edge)).filter
    (fun edge => decide (F edge ≠ F (ring.rightNeighbor edge)))

theorem mem_tasepNontrivialSwapEdges_iff
    (ring : DirectedRing n) (F : Fin n -> Bool) (edge : Fin n) :
    edge ∈ tasepNontrivialSwapEdges ring F ↔
      F edge ≠ F (ring.rightNeighbor edge) := by
  simp [tasepNontrivialSwapEdges]

theorem tasepNontrivialSwapEdges_nodup
    (ring : DirectedRing n) (F : Fin n -> Bool) :
    (tasepNontrivialSwapEdges ring F).Nodup := by
  unfold tasepNontrivialSwapEdges
  exact pointwise_nodup_filter_of_nodup _ _
    (pointwise_nodup_ofFn_id n)

/-- The list of configurations obtained by applying every nontrivial
adjacent swap once. -/
def tasepNontrivialSwapTargets (ring : DirectedRing n)
    (F : Fin n -> Bool) : List (Fin n -> Bool) :=
  (tasepNontrivialSwapEdges ring F).map
    (swapFrontConfigAt ring F)

/-- No target multiplicity is lost when the adjacent-swap edge sum is
reindexed by target configuration. -/
theorem tasepNontrivialSwapTargets_nodup
    (ring : DirectedRing n) (hn : 3 <= n) (F : Fin n -> Bool) :
    (tasepNontrivialSwapTargets ring F).Nodup := by
  unfold tasepNontrivialSwapTargets
  apply pointwise_nodup_map_of_injective_on
    (tasepNontrivialSwapEdges ring F)
    (swapFrontConfigAt ring F)
    (tasepNontrivialSwapEdges_nodup ring F)
  intro edge hedge other hother hswap
  exact edge_eq_of_swapFrontConfigAt_eq_of_endpoint_ne
    ring hn F edge other
      ((mem_tasepNontrivialSwapEdges_iff ring F edge).mp hedge)
      hswap

theorem tasepNontrivialSwapTargets_length
    (ring : DirectedRing n) (F : Fin n -> Bool) :
    (tasepNontrivialSwapTargets ring F).length =
      (tasepNontrivialSwapEdges ring F).length := by
  simp [tasepNontrivialSwapTargets]

theorem sum_all_swapEdge_cost_eq_sum_nontrivialSwapTargets_cost
    (ring : DirectedRing n) (F : Fin n -> Bool)
    (cost : (Fin n -> Bool) -> Nat) (hself : cost F = 0) :
    (List.ofFn (fun edge : Fin n =>
      cost (swapFrontConfigAt ring F edge))).sum =
      ((tasepNontrivialSwapTargets ring F).map cost).sum := by
  unfold tasepNontrivialSwapTargets tasepNontrivialSwapEdges
  rw [List.map_map]
  have hmap :
      (List.ofFn (fun edge : Fin n => edge)).map (fun edge =>
          cost (swapFrontConfigAt ring F edge)) =
        List.ofFn (fun edge : Fin n =>
          cost (swapFrontConfigAt ring F edge)) := by
    simpa [Function.comp_def] using
      (List.map_ofFn (fun edge : Fin n => edge)
        (fun edge => cost (swapFrontConfigAt ring F edge)))
  rw [← hmap]
  apply pointwise_sum_map_eq_filter_of_false_zero
  intro edge hedge hinactive
  have heq : F edge = F (ring.rightNeighbor edge) := by
    by_cases hsame : F edge = F (ring.rightNeighbor edge)
    · exact hsame
    · have hne : F edge ≠ F (ring.rightNeighbor edge) := hsame
      have hdec :
          decide (F edge ≠ F (ring.rightNeighbor edge)) = true := by
        simp [hne]
      rw [hdec] at hinactive
      cases hinactive
  have hswap : swapFrontConfigAt ring F edge = F := by
    funext i
    by_cases hie : i = edge
    · subst i
      simp [swapFrontConfigAt, heq]
    · by_cases hir : i = ring.rightNeighbor edge
      · subst i
        simp [swapFrontConfigAt, hie, heq]
      · simp [swapFrontConfigAt, hie, hir]
  calc
    cost (swapFrontConfigAt ring F edge) = cost F := congrArg cost hswap
    _ = 0 := hself

theorem mem_tasepFrontConfigSlice_of_mem_nontrivialSwapTargets
    (ring : DirectedRing n) (hn : 3 <= n)
    (k : Nat) (F G : Fin n -> Bool)
    (hmass : frontConfigMass F = k)
    (hG : G ∈ tasepNontrivialSwapTargets ring F) :
    G ∈ tasepFrontConfigSlice n k := by
  unfold tasepNontrivialSwapTargets at hG
  rw [List.mem_map] at hG
  obtain ⟨edge, hedge, rfl⟩ := hG
  exact (mem_tasepFrontConfigSlice_iff
    (m := n) (k := k) (swapFrontConfigAt ring F edge)).2
      ((frontConfigMass_swapFrontConfigAt_of_endpoint_ne
        ring (by omega) F edge
          ((mem_tasepNontrivialSwapEdges_iff ring F edge).mp hedge)).trans
        hmass)

/-- The exact incidence identity has a factor-two margin in every
nondegenerate slice.  This is the stationary slack needed to absorb a
nonzero finite-time mixing error; the earlier inverse-square theorem alone
has no such margin. -/
theorem two_mul_frontSliceCard_le_square_mul_markedPair_pointwise
    (m k : Nat) (hm : 3 <= m) (hk : 2 <= k) (hkm : k < m) :
    2 * frontSliceCard m k <=
      m ^ 2 * markedPairSliceCard m k := by
  have hexact := frontSliceCard_markedPair_exact m k hk (by omega)
  have hkfactor : 2 <= k * (k - 1) := by
    calc
      2 = 2 * 1 := by omega
      _ <= k * (k - 1) := Nat.mul_le_mul hk (by omega)
  have hscale :
      2 * frontSliceCard m k <=
        (k * (k - 1)) * frontSliceCard m k := by
    exact Nat.mul_le_mul_right (frontSliceCard m k) hkfactor
  have hcoeff : m * (m - 1) <= m ^ 2 := by
    rw [Nat.pow_two]
    exact Nat.mul_le_mul_left m (by omega)
  calc
    2 * frontSliceCard m k <=
        (k * (k - 1)) * frontSliceCard m k := hscale
    _ = m * (m - 1) * markedPairSliceCard m k := hexact.symm
    _ <= m ^ 2 * markedPairSliceCard m k :=
      Nat.mul_le_mul_right _ hcoeff

theorem two_mul_frontSliceWordCount_le_square_mul_markedPairWordCount
    (m k : Nat) (hm : 3 <= m) (hk : 2 <= k) (hkm : k < m) :
    2 * frontSliceWordCount m k <=
      m ^ 2 * markedPairWordCount m k := by
  rw [frontSliceWordCount_eq_card,
    markedPairWordCount_eq_markedPairSliceCard m k (by omega) hk]
  exact two_mul_frontSliceCard_le_square_mul_markedPair_pointwise
    m k hm hk hkm

/-- Arbitrary directed-edge function-slice form of the same strict margin. -/
theorem two_mul_tasepFrontConfigSlice_length_le_square_mul_marked_length
    (ring : DirectedRing n) (hn : 3 <= n)
    (k : Nat) (hk : 2 <= k) (hkn : k < n) (edge : Fin n) :
    2 * (tasepFrontConfigSlice n k).length <=
      n ^ 2 * (tasepMarkedFrontConfigSlice ring k edge).length := by
  rw [tasepFrontConfigSlice_length_eq_wordCount,
    tasepMarkedFrontConfigSlice_length_eq_wordCount ring (by omega)]
  exact two_mul_frontSliceWordCount_le_square_mul_markedPairWordCount
    n k hn hk hkn

/-! ## Exact fixed-slice normalization of the integer `P P*` kernel -/

private theorem pointwise_sum_ofFn_eq
    (f g : Fin n -> Nat) (hfg : forall i, f i = g i) :
    (List.ofFn f).sum = (List.ofFn g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons, hfg 0]
      exact congrArg (g 0 + .)
        (ih (fun i => f i.succ) (fun i => g i.succ)
          (fun i => hfg i.succ))

private theorem pointwise_sum_ofFn_add
    (f g : Fin n -> Nat) :
    (List.ofFn (fun i => f i + g i)).sum =
      (List.ofFn f).sum + (List.ofFn g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons, ih]
      omega

private theorem pointwise_sum_ofFn_const (m c : Nat) :
    (List.ofFn (fun _ : Fin m => c)).sum = m * c := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons, ih, Nat.succ_mul]
      omega

private theorem pointwise_sum_list_ofFn_comm
    {alpha : Type} {m : Nat} (xs : List alpha)
    (f : alpha -> Fin m -> Nat) :
    (xs.map (fun x => (List.ofFn (fun i => f x i)).sum)).sum =
      (List.ofFn (fun i =>
        (xs.map (fun x => f x i)).sum)).sum := by
  induction xs with
  | nil =>
      simpa using (pointwise_sum_ofFn_const m 0).symm
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      exact (pointwise_sum_ofFn_add
        (fun i => f x i)
        (fun i => (xs.map (fun y => f y i)).sum)).symm

private theorem pointwise_sum_indicator_ofFn_eq_countP
    {alpha : Type} {m : Nat} (f : Fin m -> alpha) (p : alpha -> Bool) :
    (List.ofFn (fun i => if p (f i) then 1 else 0)).sum =
      (List.ofFn f).countP p := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.countP_cons]
      have htail := ih (fun i => f i.succ)
      rw [htail]
      cases hp : p (f 0) <;> simp [Nat.add_comm]

theorem tasepSliceIncomingPairs_length_eq_indicator_sum
    (ring : DirectedRing n) (k : Nat) (H : Fin n -> Bool) :
    (tasepSliceIncomingPairs ring k H).length =
      ((tasepFrontConfigSlice n k).map (fun G =>
        (List.ofFn (fun second : Fin n =>
          if localStep ring clockwiseTasepPair G second = H
            then 1 else 0)).sum)).sum := by
  classical
  unfold tasepSliceIncomingPairs tasepSliceSchedulerPairs
  rw [← List.countP_eq_length_filter]
  rw [List.countP_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro G _hG
  dsimp only [Function.comp_apply]
  calc
    _ = List.countP
        (fun p : (Fin n -> Bool) × Fin n =>
          decide (localStep ring clockwiseTasepPair p.1 p.2 = H))
        (List.ofFn (fun second : Fin n => (G, second))) := by
      apply congrArg (fun q =>
        List.countP q (List.ofFn (fun second : Fin n => (G, second))))
      funext p
      by_cases h : localStep ring clockwiseTasepPair p.1 p.2 = H
      · simp [h]
      · simp [h]
    _ = (List.ofFn (fun second : Fin n =>
          if localStep ring clockwiseTasepPair G second = H
            then 1 else 0)).sum := by
      rw [← pointwise_sum_indicator_ofFn_eq_countP
        (fun second : Fin n => (G, second))
        (fun p : (Fin n -> Bool) × Fin n =>
          decide (localStep ring clockwiseTasepPair p.1 p.2 = H))]
      apply pointwise_sum_ofFn_eq
      intro second
      by_cases h : localStep ring clockwiseTasepPair G second = H
      · simp [h]
      · simp [h]

theorem tasepCommonSuccessorPairCount_sum_fixedSlice
    (ring : DirectedRing n) (hn : 1 < n) (k : Nat)
    (F : Fin n -> Bool) (hF : F ∈ tasepFrontConfigSlice n k) :
    ((tasepFrontConfigSlice n k).map
      (tasepCommonSuccessorPairCount ring F)).sum = n ^ 2 := by
  classical
  unfold tasepCommonSuccessorPairCount
  rw [pointwise_sum_list_ofFn_comm]
  calc
    _ = (List.ofFn (fun _ : Fin n => n)).sum := by
      apply pointwise_sum_ofFn_eq
      intro first
      calc
        _ = ((tasepFrontConfigSlice n k).map (fun G =>
          (List.ofFn (fun second : Fin n =>
            if localStep ring clockwiseTasepPair F first =
                localStep ring clockwiseTasepPair G second
              then 1 else 0)).sum)).sum := by
          apply congrArg List.sum
          apply List.map_congr_left
          intro G _hG
          apply pointwise_sum_ofFn_eq
          intro second
          by_cases h : localStep ring clockwiseTasepPair F first =
              localStep ring clockwiseTasepPair G second
          · simp [h]
          · simp [h]
        _ = ((tasepFrontConfigSlice n k).map (fun G =>
          (List.ofFn (fun second : Fin n =>
            if localStep ring clockwiseTasepPair G second =
                localStep ring clockwiseTasepPair F first
              then 1 else 0)).sum)).sum := by
          apply congrArg List.sum
          apply List.map_congr_left
          intro G _hG
          apply pointwise_sum_ofFn_eq
          intro second
          by_cases h : localStep ring clockwiseTasepPair F first =
              localStep ring clockwiseTasepPair G second
          · rw [if_pos h, if_pos h.symm]
          · have hrev : localStep ring clockwiseTasepPair G second ≠
                localStep ring clockwiseTasepPair F first :=
              fun h' => h h'.symm
            rw [if_neg h, if_neg hrev]
        _ = n := by
          rw [← tasepSliceIncomingPairs_length_eq_indicator_sum
            ring k (localStep ring clockwiseTasepPair F first)]
          apply tasepSliceIncomingPairs_length ring hn k
          exact (mem_tasepFrontConfigSlice_iff
            (m := n) (k := k)
            (localStep ring clockwiseTasepPair F first)).2
              ((frontConfigMass_clockwiseTasep_localStep
                ring hn F first).trans
                  ((mem_tasepFrontConfigSlice_iff
                    (m := n) (k := k) F).1 hF))
    _ = n ^ 2 := by
      simpa [Nat.pow_two] using (pointwise_sum_ofFn_const n n)

/-- Symmetry turns the row normalization into the matching column
normalization without a second scheduler count. -/
theorem tasepCommonSuccessorPairCount_sum_fixedSlice_reverse
    (ring : DirectedRing n) (hn : 1 < n) (k : Nat)
    (F : Fin n -> Bool) (hF : F ∈ tasepFrontConfigSlice n k) :
    ((tasepFrontConfigSlice n k).map (fun G =>
      tasepCommonSuccessorPairCount ring G F)).sum = n ^ 2 := by
  calc
    ((tasepFrontConfigSlice n k).map (fun G =>
        tasepCommonSuccessorPairCount ring G F)).sum =
      ((tasepFrontConfigSlice n k).map (fun G =>
        tasepCommonSuccessorPairCount ring F G)).sum := by
          apply congrArg List.sum
          apply List.map_congr_left
          intro G hG
          exact tasepCommonSuccessorPairCount_symm ring G F
    _ = n ^ 2 :=
      tasepCommonSuccessorPairCount_sum_fixedSlice ring hn k F hF

/-! ## Exact local `P P*` comparison on the injective target list -/

private theorem pointwise_mul_sum_map
    {alpha : Type} (c : Nat) (xs : List alpha) (weight : alpha -> Nat) :
    c * (xs.map weight).sum =
      (xs.map (fun x => c * weight x)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, Nat.mul_add, ih]

private theorem pointwise_sum_map_le_sum_map
    {alpha : Type} (xs : List alpha) (left right : alpha -> Nat)
    (hle : forall x, x ∈ xs -> left x <= right x) :
    (xs.map left).sum <= (xs.map right).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      apply Nat.add_le_add
      · exact hle x (by simp)
      · apply ih
        intro y hy
        exact hle y (by simp [hy])

private theorem pointwise_sum_map_append
    {alpha : Type} (xs ys : List alpha) (weight : alpha -> Nat) :
    ((xs ++ ys).map weight).sum =
      (xs.map weight).sum + (ys.map weight).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.cons_append, List.map_cons, List.sum_cons, ih]
      omega

private theorem pointwise_sum_map_le_of_nodup_subset
    {alpha : Type} (xs ys : List alpha) (weight : alpha -> Nat)
    (hxs : xs.Nodup) (hsub : xs ⊆ ys) :
    (xs.map weight).sum <= (ys.map weight).sum := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
      rw [List.nodup_cons] at hxs
      have ha : a ∈ ys := hsub (by simp)
      rw [List.mem_iff_append] at ha
      obtain ⟨before, after, rfl⟩ := ha
      have htailSub : xs ⊆ before ++ after := by
        intro x hx
        have hxcons : x ∈ a :: xs := List.mem_cons_of_mem a hx
        have hxfull := hsub hxcons
        rw [List.mem_append] at hxfull ⊢
        rcases hxfull with hbefore | hrest
        · exact Or.inl hbefore
        · simp only [List.mem_cons] at hrest
          rcases hrest with hxa | hafter
          · subst x
            exact (hxs.1 hx).elim
          · exact Or.inr hafter
      have htail := ih (before ++ after) hxs.2 htailSub
      calc
        ((a :: xs).map weight).sum =
            weight a + (xs.map weight).sum := by rfl
        _ <= weight a + ((before ++ after).map weight).sum :=
          Nat.add_le_add_left htail _
        _ = ((before ++ a :: after).map weight).sum := by
          rw [pointwise_sum_map_append, pointwise_sum_map_append]
          simp only [List.map_cons, List.sum_cons]
          omega

/-- Each target in the nontrivial adjacent-swap list inherits the imported
`n/2` lower bound on its exact integer `P P*` common-successor weight.  The
arbitrary `cost` is nonnegative because it is Nat-valued. -/
theorem n_mul_cost_le_two_mul_commonSuccessor_cost_of_mem_swapTargets
    (ring : DirectedRing n) (hn : 3 <= n)
    (F G : Fin n -> Bool) (cost : (Fin n -> Bool) -> Nat)
    (hG : G ∈ tasepNontrivialSwapTargets ring F) :
    n * cost G <=
      2 * (tasepCommonSuccessorPairCount ring F G * cost G) := by
  unfold tasepNontrivialSwapTargets at hG
  rw [List.mem_map] at hG
  obtain ⟨edge, hedge, rfl⟩ := hG
  have hcommon := n_le_two_mul_tasepCommonSuccessorPairCount_swap
    ring (by omega) F edge
      ((mem_tasepNontrivialSwapEdges_iff ring F edge).mp hedge)
  simpa only [Nat.mul_assoc] using
    (Nat.mul_le_mul_right (cost (swapFrontConfigAt ring F edge)) hcommon)

/-- Summed denominator-cleared comparison on the duplicate-free adjacent-swap
target row.  Later Poincare work may instantiate `cost G` with a squared
function difference.  No division or probability object occurs here. -/
theorem n_mul_sum_swapTarget_cost_le_two_mul_sum_commonSuccessor_cost
    (ring : DirectedRing n) (hn : 3 <= n)
    (F : Fin n -> Bool) (cost : (Fin n -> Bool) -> Nat) :
    n * ((tasepNontrivialSwapTargets ring F).map cost).sum <=
      2 * ((tasepNontrivialSwapTargets ring F).map (fun G =>
        tasepCommonSuccessorPairCount ring F G * cost G)).sum := by
  rw [pointwise_mul_sum_map, pointwise_mul_sum_map]
  apply pointwise_sum_map_le_sum_map
  intro G hG
  exact n_mul_cost_le_two_mul_commonSuccessor_cost_of_mem_swapTargets
    ring hn F G cost hG

/-- The injective adjacent-swap target row is a genuine subrow of the full
fixed-mass `P P*` row. -/
theorem sum_swapTarget_commonSuccessor_cost_le_sum_fixedSlice
    (ring : DirectedRing n) (hn : 3 <= n) (k : Nat)
    (F : Fin n -> Bool) (hmass : frontConfigMass F = k)
    (cost : (Fin n -> Bool) -> Nat) :
    ((tasepNontrivialSwapTargets ring F).map (fun G =>
      tasepCommonSuccessorPairCount ring F G * cost G)).sum <=
      ((tasepFrontConfigSlice n k).map (fun G =>
        tasepCommonSuccessorPairCount ring F G * cost G)).sum := by
  classical
  apply pointwise_sum_map_le_of_nodup_subset
  · exact tasepNontrivialSwapTargets_nodup ring hn F
  · intro G hG
    exact mem_tasepFrontConfigSlice_of_mem_nontrivialSwapTargets
      ring hn k F G hmass hG

/-- Full-row denominator-cleared comparison.  For any Nat-valued cost on
targets, the exact `P P*` row energy dominates the nontrivial adjacent-swap
row energy by the imported factor `n/2`. -/
theorem n_mul_sum_swapTarget_cost_le_two_mul_sum_fixedSlice_commonSuccessor_cost
    (ring : DirectedRing n) (hn : 3 <= n) (k : Nat)
    (F : Fin n -> Bool) (hmass : frontConfigMass F = k)
    (cost : (Fin n -> Bool) -> Nat) :
    n * ((tasepNontrivialSwapTargets ring F).map cost).sum <=
      2 * ((tasepFrontConfigSlice n k).map (fun G =>
        tasepCommonSuccessorPairCount ring F G * cost G)).sum := by
  exact Nat.le_trans
    (n_mul_sum_swapTarget_cost_le_two_mul_sum_commonSuccessor_cost
      ring hn F cost)
    (Nat.mul_le_mul_left 2
      (sum_swapTarget_commonSuccessor_cost_le_sum_fixedSlice
        ring hn k F hmass cost))

theorem n_mul_sum_fixedSlice_swapTarget_cost_le_two_mul_sum_fixedSlice_commonSuccessor_cost
    (ring : DirectedRing n) (hn : 3 <= n) (k : Nat)
    (cost : (Fin n -> Bool) -> (Fin n -> Bool) -> Nat) :
    n * ((tasepFrontConfigSlice n k).map (fun F =>
      ((tasepNontrivialSwapTargets ring F).map (cost F)).sum)).sum <=
      2 * ((tasepFrontConfigSlice n k).map (fun F =>
        ((tasepFrontConfigSlice n k).map (fun G =>
          tasepCommonSuccessorPairCount ring F G * cost F G)).sum)).sum := by
  rw [pointwise_mul_sum_map, pointwise_mul_sum_map]
  apply pointwise_sum_map_le_sum_map
  intro F hF
  apply n_mul_sum_swapTarget_cost_le_two_mul_sum_fixedSlice_commonSuccessor_cost
    ring hn k F
  exact (mem_tasepFrontConfigSlice_iff
    (m := n) (k := k) F).1 hF

/-- Full cyclic-edge row form.  Equal-endpoint swaps contribute zero, so the
injective active-target comparison above controls the standard edge sum
without changing its normalization. -/
theorem n_mul_sum_allSwapEdge_cost_le_two_mul_sum_fixedSlice_commonSuccessor_cost
    (ring : DirectedRing n) (hn : 3 <= n) (k : Nat)
    (F : Fin n -> Bool) (hmass : frontConfigMass F = k)
    (cost : (Fin n -> Bool) -> Nat) (hself : cost F = 0) :
    n * (List.ofFn (fun edge : Fin n =>
      cost (swapFrontConfigAt ring F edge))).sum <=
      2 * ((tasepFrontConfigSlice n k).map (fun G =>
        tasepCommonSuccessorPairCount ring F G * cost G)).sum := by
  rw [sum_all_swapEdge_cost_eq_sum_nontrivialSwapTargets_cost
    ring F cost hself]
  exact
    n_mul_sum_swapTarget_cost_le_two_mul_sum_fixedSlice_commonSuccessor_cost
      ring hn k F hmass cost

/-- Global full-edge form of the exact denominator-cleared `P P*`
comparison.  This is ready for any squared-difference cost: only its
definitional zero value on the diagonal is required. -/
theorem n_mul_sum_fixedSlice_allSwapEdge_cost_le_two_mul_sum_fixedSlice_commonSuccessor_cost
    (ring : DirectedRing n) (hn : 3 <= n) (k : Nat)
    (cost : (Fin n -> Bool) -> (Fin n -> Bool) -> Nat)
    (hself : forall F, F ∈ tasepFrontConfigSlice n k -> cost F F = 0) :
    n * ((tasepFrontConfigSlice n k).map (fun F =>
      (List.ofFn (fun edge : Fin n =>
        cost F (swapFrontConfigAt ring F edge))).sum)).sum <=
      2 * ((tasepFrontConfigSlice n k).map (fun F =>
        ((tasepFrontConfigSlice n k).map (fun G =>
          tasepCommonSuccessorPairCount ring F G * cost F G)).sum)).sum := by
  have hedgeToTarget :
      ((tasepFrontConfigSlice n k).map (fun F =>
        (List.ofFn (fun edge : Fin n =>
          cost F (swapFrontConfigAt ring F edge))).sum)).sum =
        ((tasepFrontConfigSlice n k).map (fun F =>
          ((tasepNontrivialSwapTargets ring F).map (cost F)).sum)).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro F hF
    exact sum_all_swapEdge_cost_eq_sum_nontrivialSwapTargets_cost
      ring F (cost F) (hself F hF)
  rw [hedgeToTarget]
  exact
    n_mul_sum_fixedSlice_swapTarget_cost_le_two_mul_sum_fixedSlice_commonSuccessor_cost
      ring hn k cost

/-- Squared-observable specialization of the full-edge comparison.  This is
the exact integer Dirichlet inequality used by the subsequent Poincare layer;
there is no abstract cost or diagonal-zero premise left to discharge. -/
theorem n_mul_sum_fixedSlice_allSwapEdge_squaredGap_le_two_mul_commonSuccessor_squaredGap
    (ring : DirectedRing n) (hn : 3 <= n) (k : Nat)
    (phi : (Fin n -> Bool) -> Int) :
    n * ((tasepFrontConfigSlice n k).map (fun F =>
      (List.ofFn (fun edge : Fin n =>
        Int.natAbs
          (phi F - phi (swapFrontConfigAt ring F edge)) ^ 2)).sum)).sum <=
      2 * ((tasepFrontConfigSlice n k).map (fun F =>
        ((tasepFrontConfigSlice n k).map (fun G =>
          tasepCommonSuccessorPairCount ring F G *
            Int.natAbs (phi F - phi G) ^ 2)).sum)).sum := by
  apply
    n_mul_sum_fixedSlice_allSwapEdge_cost_le_two_mul_sum_fixedSlice_commonSuccessor_cost
      ring hn k (fun F G => Int.natAbs (phi F - phi G) ^ 2)
  intro F hF
  simp

/-! The first remaining implication is now the pure fixed-slice inequality:
bound the all-pairs squared variation by a polynomial multiple of the
full cyclic adjacent-swap squared energy.  One route splits this into a
complete-transposition slice Poincare theorem and an arbitrary-distance
moving-particle comparison.  The integer `P P*` normalization and its
adjacent-row domination are already closed above; injective target reindexing
and the zero cost of stuttering swaps prevent an extra factor `n` loss or a
filtered-edge premise.
-/

#print axioms rightNeighbor_rightNeighbor_ne_self_of_three_le
#print axioms edge_eq_of_swapFrontConfigAt_eq_of_endpoint_ne
#print axioms swapFrontConfigAt_nontrivialEdge_injective
#print axioms tasepNontrivialSwapTargets_nodup
#print axioms mem_tasepFrontConfigSlice_of_mem_nontrivialSwapTargets
#print axioms two_mul_tasepFrontConfigSlice_length_le_square_mul_marked_length
#print axioms tasepCommonSuccessorPairCount_sum_fixedSlice
#print axioms tasepCommonSuccessorPairCount_sum_fixedSlice_reverse
#print axioms n_mul_sum_swapTarget_cost_le_two_mul_sum_commonSuccessor_cost
#print axioms n_mul_sum_swapTarget_cost_le_two_mul_sum_fixedSlice_commonSuccessor_cost
#print axioms n_mul_sum_fixedSlice_swapTarget_cost_le_two_mul_sum_fixedSlice_commonSuccessor_cost
#print axioms sum_all_swapEdge_cost_eq_sum_nontrivialSwapTargets_cost
#print axioms n_mul_sum_allSwapEdge_cost_le_two_mul_sum_fixedSlice_commonSuccessor_cost
#print axioms n_mul_sum_fixedSlice_allSwapEdge_cost_le_two_mul_sum_fixedSlice_commonSuccessor_cost
#print axioms n_mul_sum_fixedSlice_allSwapEdge_squaredGap_le_two_mul_commonSuccessor_squaredGap

end PPartialSealSweepTasepPointwisePoincareSol
end PPLLCompleteMultiLeaderCleanup
