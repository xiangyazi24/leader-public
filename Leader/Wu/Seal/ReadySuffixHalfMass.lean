import Leader.Wu.Seal.HomeTrapWorkload

/-!
# Exact half mass of good suffixes from a loaded seal-sweep trap

This module proves the transient-readiness suffix lemma left open by the R109
endpoint reduction.  Starting from a quotient state with a loaded home trap,
at least half of every fixed-length uniform scheduler layer ends either below
the source home count or with some loaded trap.

The pairing is an exact finite-word involution.  Fix a ready edge `hit` and
let `out` be the edge leaving its occupied right home.  Swap the first clock
among `hit` and `out`.  A bad word cannot see `hit` first, since that clock
deletes the occupied home.  Thus its swapped word sees `hit` first and is good;
later trajectory divergence is harmless because quotient homes never return.

The one-site alias needs separate treatment: `hit = out`, and the local-step
write convention retains the left output of `AA -> AC`, so the sole ready site
stays ready forever.  For two sites the two edges are distinct and the same
involution proof applies without assuming three distinct neighboring sites.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialSealSweepReadySuffixHalfMassSol

open PPLL PPLLResearchFormulation PPLLTraceConvergence
open PPLLSchedulerBlocks PPLLNoCheckBirthConditionTwoGeometry
open PPartialSealSweepHomeFrontQuotientSol
open PPartialSealSweepHomeTrapCurrentSol
open PPartialSealSweepHomeTrapWorkloadSol

set_option autoImplicit false

variable {n : Nat}

/-! ## Home-count monotonicity for the unrestricted quotient -/

/-- A transparent copy of the quotient home count, used to expose its finite
sum without depending on the private helper in the quotient module. -/
private def readySuffixHomeCount
    (X : Fin n → SealSweepHomeFrontSite) : Nat :=
  (List.ofFn fun i : Fin n => if (X i).1 then 1 else 0).sum

private theorem readySuffixHomeCount_eq
    (X : Fin n → SealSweepHomeFrontSite) :
    readySuffixHomeCount X = homeFrontHomeCount X := by
  rfl

private theorem sum_ofFn_le
    (f g : Fin n → Nat) (hfg : ∀ i, f i ≤ g i) :
    (List.ofFn f).sum ≤ (List.ofFn g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      exact Nat.add_le_add (hfg 0)
        (ih (fun i => f i.succ) (fun i => g i.succ)
          (fun i => hfg i.succ))

private theorem sum_ofFn_lt_of_single_lt
    (f g : Fin n → Nat) (j : Fin n)
    (hle : ∀ i, f i ≤ g i) (hlt : f j < g j) :
    (List.ofFn f).sum < (List.ofFn g).sum := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      by_cases hj0 : j = 0
      · subst j
        have htail := sum_ofFn_le
          (fun i : Fin n => f i.succ) (fun i => g i.succ)
          (fun i => hle i.succ)
        omega
      · have hjpos : 0 < j.val := by
          have hjne : j.val ≠ 0 := fun h =>
            hj0 (Fin.ext (by simpa using h))
          omega
        let j' : Fin n := ⟨j.val - 1, by omega⟩
        have hjsucc : j'.succ = j := Fin.ext (by simp [j']; omega)
        have htail := ih (fun i => f i.succ) (fun i => g i.succ) j'
          (fun i => hle i.succ) (hjsucc ▸ hlt)
        have hhead := hle 0
        omega

/-- The left endpoint's home bit is invariant under the exact quotient pair
table. -/
theorem sealSweepHomeFrontPair_leftHome
    (l r : SealSweepHomeFrontSite) :
    (sealSweepHomeFrontPair l r).1.1 = l.1 := by
  rcases l with ⟨lh, lf⟩
  rcases r with ⟨rh, rf⟩
  cases lh <;> cases lf <;> cases rh <;> cases rf <;> rfl

/-- A responder home present after a quotient pair transition was already
present before it.  The table never creates homes. -/
theorem sealSweepHomeFrontPair_rightHome_backward
    (l r : SealSweepHomeFrontSite)
    (hafter : (sealSweepHomeFrontPair l r).2.1 = true) :
    r.1 = true := by
  rcases l with ⟨lh, lf⟩
  rcases r with ⟨rh, rf⟩
  cases lh <;> cases lf <;> cases rh <;> cases rf <;>
    simp [sealSweepHomeFrontPair] at hafter ⊢

private theorem sealSweepFrontHitsHomePair_leftFront
    (l r : SealSweepHomeFrontSite)
    (hhit : sealSweepFrontHitsHomePair l r = true) :
    l.2 = true := by
  rcases l with ⟨lh, lf⟩
  rcases r with ⟨rh, rf⟩
  cases lh <;> cases lf <;> cases rh <;> cases rf <;>
    simp [sealSweepFrontHitsHomePair] at hhit ⊢

private theorem sealSweepFrontHitsHomePair_rightHome
    (l r : SealSweepHomeFrontSite)
    (hhit : sealSweepFrontHitsHomePair l r = true) :
    r.1 = true := by
  rcases l with ⟨lh, lf⟩
  rcases r with ⟨rh, rf⟩
  cases lh <;> cases lf <;> cases rh <;> cases rf <;>
    simp [sealSweepFrontHitsHomePair] at hhit ⊢

private theorem sealSweepHomeFrontPair_rightHome_false_of_hit
    (l r : SealSweepHomeFrontSite)
    (hhit : sealSweepFrontHitsHomePair l r = true) :
    (sealSweepHomeFrontPair l r).2.1 = false := by
  rcases l with ⟨lh, lf⟩
  rcases r with ⟨rh, rf⟩
  cases lh <;> cases lf <;> cases rh <;> cases rf <;>
    simp [sealSweepFrontHitsHomePair, sealSweepHomeFrontPair] at hhit ⊢

/-- Pointwise backward persistence of homes through one quotient local step. -/
theorem homeFrontLocalStep_home_backward
    (ring : DirectedRing n)
    (X : Fin n → SealSweepHomeFrontSite) (edge i : Fin n)
    (hafter : (localStep ring sealSweepHomeFrontPair X edge i).1 = true) :
    (X i).1 = true := by
  let j := ring.rightNeighbor edge
  by_cases hie : i = edge
  · subst i
    have hleft : (sealSweepHomeFrontPair (X edge) (X j)).1.1 = true := by
      simpa [localStep, j] using hafter
    exact (sealSweepHomeFrontPair_leftHome (X edge) (X j)).symm.trans hleft
  · by_cases hij : i = j
    · subst i
      have hright :
          (sealSweepHomeFrontPair (X edge) (X j)).2.1 = true := by
        simpa [localStep, j, hie] using hafter
      exact sealSweepHomeFrontPair_rightHome_backward
        (X edge) (X j) hright
    · simpa [localStep, j, hie, hij] using hafter

/-- Home count is nonincreasing under every quotient local step, without a
reachability or balance hypothesis. -/
theorem homeFrontHomeCount_localStep_le
    (ring : DirectedRing n)
    (X : Fin n → SealSweepHomeFrontSite) (edge : Fin n) :
    homeFrontHomeCount
        (localStep ring sealSweepHomeFrontPair X edge) ≤
      homeFrontHomeCount X := by
  change readySuffixHomeCount
      (localStep ring sealSweepHomeFrontPair X edge) ≤
    readySuffixHomeCount X
  unfold readySuffixHomeCount
  apply sum_ofFn_le
  intro i
  cases hafter : (localStep ring sealSweepHomeFrontPair X edge i).1 with
  | false => simp [hafter]
  | true =>
      have hbefore := homeFrontLocalStep_home_backward
        ring X edge i hafter
      simp [hafter, hbefore]

/-- Home count is nonincreasing along every quotient scheduler word. -/
theorem homeFrontHomeCount_run_le
    (ring : DirectedRing n)
    (X : Fin n → SealSweepHomeFrontSite) (word : DetSchedule n) :
    homeFrontHomeCount
        (runLocalSchedule ring sealSweepHomeFrontPair X word) ≤
      homeFrontHomeCount X := by
  induction word generalizing X with
  | nil =>
      simp only [runLocalSchedule]
      exact Nat.le_refl _
  | cons edge rest ih =>
      simp only [runLocalSchedule]
      exact Nat.le_trans (ih _)
        (homeFrontHomeCount_localStep_le ring X edge)

/-- On a nontrivial ring, selecting a loaded edge strictly lowers the exact
quotient home count. -/
theorem homeFrontHomeCount_localStep_lt_of_hit
    (ring : DirectedRing n) (hn : 1 < n)
    (X : Fin n → SealSweepHomeFrontSite) (edge : Fin n)
    (hhit : sealSweepFrontHitsHomePair
      (X edge) (X (ring.rightNeighbor edge)) = true) :
    homeFrontHomeCount
        (localStep ring sealSweepHomeFrontPair X edge) <
      homeFrontHomeCount X := by
  let j := ring.rightNeighbor edge
  have hej : edge ≠ j := by
    exact (rightNeighbor_ne_self_of_one_lt ring hn edge).symm
  have hjHome : (X j).1 = true := by
    exact sealSweepFrontHitsHomePair_rightHome
      (X edge) (X j) (by simpa [j] using hhit)
  have hjAfter :
      (localStep ring sealSweepHomeFrontPair X edge j).1 = false := by
    have hpair := sealSweepHomeFrontPair_rightHome_false_of_hit
      (X edge) (X j) (by simpa [j] using hhit)
    simp [localStep, j, hej.symm, hpair]
  change readySuffixHomeCount
      (localStep ring sealSweepHomeFrontPair X edge) <
    readySuffixHomeCount X
  unfold readySuffixHomeCount
  apply sum_ofFn_lt_of_single_lt _ _ j
  · intro i
    cases hafter : (localStep ring sealSweepHomeFrontPair X edge i).1 with
    | false => simp [hafter]
    | true =>
        have hbefore := homeFrontLocalStep_home_backward
          ring X edge i hafter
        simp [hafter, hbefore]
  · simp [hjAfter, hjHome]

/-! ## Persistence of one chosen loaded edge before its two relevant clocks -/

/-- If neither the chosen hit edge nor the edge leaving its right home is
selected, then absence of home loss preserves that chosen readiness.  An
incoming edge may touch the left endpoint, but any nonstuttering change there
is itself a hit and would strictly lower home count. -/
theorem homeFrontReadyAt_localStep_of_homeCount_eq
    (ring : DirectedRing n) (hn : 1 < n)
    (X : Fin n → SealSweepHomeFrontSite)
    (hit edge : Fin n)
    (hready : sealSweepFrontHitsHomePair
      (X hit) (X (ring.rightNeighbor hit)) = true)
    (hedgeHit : edge ≠ hit)
    (hedgeOut : edge ≠ ring.rightNeighbor hit)
    (hcount : homeFrontHomeCount
        (localStep ring sealSweepHomeFrontPair X edge) =
      homeFrontHomeCount X) :
    sealSweepFrontHitsHomePair
        (localStep ring sealSweepHomeFrontPair X edge hit)
        (localStep ring sealSweepHomeFrontPair X edge
          (ring.rightNeighbor hit)) = true := by
  let out := ring.rightNeighbor hit
  have hrightNotOut : ring.rightNeighbor edge ≠ out := by
    intro h
    have h' : ring.rightNeighbor edge = ring.rightNeighbor hit := by
      simpa [out] using h
    have heq : edge = hit := rightNeighbor_injective ring h'
    exact hedgeHit heq
  have houtEq :
      localStep ring sealSweepHomeFrontPair X edge out = X out := by
    simp [localStep, out, hedgeOut.symm, hrightNotOut.symm]
  have hhitFront : (X hit).2 = true :=
    sealSweepFrontHitsHomePair_leftFront
      (X hit) (X out) (by simpa [out] using hready)
  have hhitEq :
      localStep ring sealSweepHomeFrontPair X edge hit = X hit := by
    by_cases hhitRight : hit = ring.rightNeighbor edge
    · have hrightHit : ring.rightNeighbor edge = hit := hhitRight.symm
      have hpairHit : sealSweepFrontHitsHomePair
          (X edge) (X hit) = false := by
        cases hpair : sealSweepFrontHitsHomePair (X edge) (X hit) with
        | false => rfl
        | true =>
            have hpair' : sealSweepFrontHitsHomePair
                (X edge) (X (ring.rightNeighbor edge)) = true := by
              simpa [hrightHit] using hpair
            have hlt := homeFrontHomeCount_localStep_lt_of_hit
              ring hn X edge hpair'
            omega
      have hmove : sealSweepFrontMovePair (X edge) (X hit) = false := by
        simp [sealSweepFrontMovePair, hhitFront]
      have hpairSelf := sealSweepHomeFrontPair_eq_self_of_no_move_no_hit
        (X edge) (X hit) hmove hpairHit
      simp only [localStep, if_neg hedgeHit.symm, if_pos hhitRight]
      simpa only [hrightHit] using congrArg Prod.snd hpairSelf
    · simp only [localStep, if_neg hedgeHit.symm, if_neg hhitRight]
  rw [hhitEq, houtEq]
  simpa [out] using hready

/-! ## The first-relevant-clock involution -/

/-- Swap the first occurrence of either distinguished edge.  Once that first
clock is swapped, the untouched suffix is left byte-for-byte unchanged. -/
def homeFrontReadySuffixSwap
    (hit out : Fin n) : DetSchedule n → DetSchedule n
  | [] => []
  | edge :: rest =>
      if edge = hit then out :: rest
      else if edge = out then hit :: rest
      else edge :: homeFrontReadySuffixSwap hit out rest

theorem homeFrontReadySuffixSwap_length
    (hit out : Fin n) (word : DetSchedule n) :
    (homeFrontReadySuffixSwap hit out word).length = word.length := by
  induction word with
  | nil => rfl
  | cons edge rest ih =>
      by_cases heHit : edge = hit
      · subst edge
        simp [homeFrontReadySuffixSwap, Nat.add_comm]
      · by_cases heOut : edge = out
        · subst edge
          simp [homeFrontReadySuffixSwap, heHit, Nat.add_comm]
        · simp [homeFrontReadySuffixSwap, heHit, heOut, ih, Nat.add_comm]

theorem homeFrontReadySuffixSwap_involutive
    (hit out : Fin n) (hne : hit ≠ out) (word : DetSchedule n) :
    homeFrontReadySuffixSwap hit out
        (homeFrontReadySuffixSwap hit out word) = word := by
  induction word with
  | nil => rfl
  | cons edge rest ih =>
      by_cases heHit : edge = hit
      · subst edge
        simp [homeFrontReadySuffixSwap, hne, hne.symm]
      · by_cases heOut : edge = out
        · subst edge
          simp [homeFrontReadySuffixSwap, hne, hne.symm]
        · simp [homeFrontReadySuffixSwap, heHit, heOut, ih]

private theorem homeFrontReadySuffixSwap_injective
    (hit out : Fin n) (hne : hit ≠ out) :
    Function.Injective (homeFrontReadySuffixSwap hit out) := by
  intro x y hxy
  rw [← homeFrontReadySuffixSwap_involutive hit out hne x,
    ← homeFrontReadySuffixSwap_involutive hit out hne y, hxy]

/-! ## Exact schedule-list counting helpers -/

private theorem nodup_ofFn_of_injective
    {q : Nat} {α : Type} (f : Fin q → α)
    (hf : Function.Injective f) :
    (List.ofFn f).Nodup := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [List.ofFn_succ, List.nodup_cons]
      constructor
      · intro hmem
        rw [List.mem_ofFn] at hmem
        obtain ⟨i, hi⟩ := hmem
        have h := hf hi
        cases h
      · apply ih
        intro i j hij
        exact Fin.succ_inj.mp (hf hij)

private theorem nodup_flatMap_of_nodup
    {α β : Type} (xs : List α) (f : α → List β)
    (hxs : xs.Nodup)
    (hfn : ∀ x, x ∈ xs → (f x).Nodup)
    (hdisjoint : ∀ x, x ∈ xs → ∀ y, y ∈ xs → x ≠ y →
      ∀ a, a ∈ f x → ∀ b, b ∈ f y → a ≠ b) :
    (xs.flatMap f).Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.nodup_cons] at hxs
      simp only [List.flatMap_cons]
      rw [List.nodup_append]
      refine ⟨hfn x (by simp), ?_, ?_⟩
      · apply ih hxs.2
        · intro y hy
          exact hfn y (by simp [hy])
        · intro y hy z hz hyz
          exact hdisjoint y (by simp [hy]) z (by simp [hz]) hyz
      · intro a ha b hb
        rw [List.mem_flatMap] at hb
        obtain ⟨y, hy, hby⟩ := hb
        apply hdisjoint x (by simp) y (by simp [hy])
        · intro hxy
          exact hxs.1 (hxy ▸ hy)
        · exact ha
        · exact hby

/-- The exact scheduler enumeration contains no duplicate words. -/
theorem allSchedules_nodup (n t : Nat) :
    (allSchedules n t).Nodup := by
  induction t with
  | zero => simp [allSchedules]
  | succ t ih =>
      rw [allSchedules]
      apply nodup_flatMap_of_nodup _ _ ih
      · intro pre hpre
        apply nodup_ofFn_of_injective
        intro e f hef
        exact List.singleton_inj.mp (List.append_cancel_left hef)
      · intro pre hpre other hother hne a ha b hb hab
        rw [List.mem_ofFn] at ha hb
        obtain ⟨e, rfl⟩ := ha
        obtain ⟨f, rfl⟩ := hb
        apply hne
        apply List.append_inj_left hab
        rw [allSchedules_schedule_length n t pre hpre,
          allSchedules_schedule_length n t other hother]

private theorem nodup_filter_of_nodup
    {α : Type} (p : α → Bool) (xs : List α) (hxs : xs.Nodup) :
    (xs.filter p).Nodup := by
  rw [List.nodup_iff_pairwise_ne] at hxs ⊢
  exact hxs.filter p

private theorem nodup_map_of_injective
    {α β : Type} (f : α → β) (xs : List α)
    (hf : Function.Injective f) (hxs : xs.Nodup) :
    (xs.map f).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  apply (List.nodup_iff_pairwise_ne.mp hxs).imp
  intro a b hab hEq
  exact hab (hf hEq)

/-- An involution of a duplicate-free finite list that sends every bad item
to a good item injects the bad sublist into the good sublist. -/
private theorem countP_not_le_countP_of_involution
    {α : Type} (xs : List α) (good : α → Bool) (swap : α → α)
    (hnodup : xs.Nodup)
    (hinvol : ∀ x, swap (swap x) = x)
    (hmem : ∀ x, x ∈ xs → swap x ∈ xs)
    (hbadGood : ∀ x, x ∈ xs → good x = false → good (swap x) = true) :
    xs.countP (fun x => !good x) ≤ xs.countP good := by
  classical
  have hinj : Function.Injective swap := by
    intro x y hxy
    rw [← hinvol x, ← hinvol y, hxy]
  let bad := xs.filter (fun x => !good x)
  have hbadNodup : bad.Nodup :=
    nodup_filter_of_nodup (fun x => !good x) xs hnodup
  have himageNodup : (bad.map swap).Nodup :=
    nodup_map_of_injective swap bad hinj hbadNodup
  have hsubset : bad.map swap ⊆ xs.filter good := by
    intro y hy
    rw [List.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [List.mem_filter] at hx ⊢
    refine ⟨hmem x hx.1, hbadGood x hx.1 ?_⟩
    simpa using hx.2
  have hle := himageNodup.length_le_of_subset hsubset
  rw [List.length_map] at hle
  rw [List.countP_eq_length_filter, List.countP_eq_length_filter]
  exact hle

private theorem countP_not_add_countP
    {α : Type} (p : α → Bool) (xs : List α) :
    xs.countP (fun x => !p x) + xs.countP p = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [List.countP_cons, List.countP_cons, List.length_cons]
      cases hp : p x <;>
        simp [hp, Nat.add_assoc, Nat.add_comm] at * <;> omega

/-! ## Bad suffixes pair injectively with good suffixes -/

private theorem readySuffixSwap_good_of_bad
    (ring : DirectedRing n) (hn : 1 < n)
    (source current : Fin n → SealSweepHomeFrontSite)
    (hit : Fin n)
    (hcount : homeFrontHomeCount current = homeFrontHomeCount source)
    (hready : sealSweepFrontHitsHomePair
      (current hit) (current (ring.rightNeighbor hit)) = true)
    (word : DetSchedule n)
    (hbad : homeFrontDropOrReadyEndpointTest ring source
      (runLocalSchedule ring sealSweepHomeFrontPair current word) = false) :
    homeFrontDropOrReadyEndpointTest ring source
      (runLocalSchedule ring sealSweepHomeFrontPair current
        (homeFrontReadySuffixSwap hit (ring.rightNeighbor hit) word)) = true := by
  induction word generalizing current with
  | nil =>
      have hgood := (homeFrontDropOrReadyEndpointTest_spec
        ring source current).2 (Or.inr ⟨hit, hready⟩)
      simpa only [runLocalSchedule, homeFrontReadySuffixSwap] using hgood
  | cons edge rest ih =>
      let out := ring.rightNeighbor hit
      have hhitOut : hit ≠ out :=
        (rightNeighbor_ne_self_of_one_lt ring hn hit).symm
      by_cases hedgeHit : edge = hit
      · subst edge
        let Y := localStep ring sealSweepHomeFrontPair current hit
        have hstepLt : homeFrontHomeCount Y <
            homeFrontHomeCount current :=
          homeFrontHomeCount_localStep_lt_of_hit ring hn current hit hready
        have htailLe := homeFrontHomeCount_run_le ring Y rest
        have hfinalLt : homeFrontHomeCount
              (runLocalSchedule ring sealSweepHomeFrontPair Y rest) <
            homeFrontHomeCount source := by
          omega
        have hgood := (homeFrontDropOrReadyEndpointTest_spec ring source
          (runLocalSchedule ring sealSweepHomeFrontPair Y rest)).2
          (Or.inl hfinalLt)
        simp only [runLocalSchedule] at hbad
        rw [hbad] at hgood
        contradiction
      · by_cases hedgeOut : edge = out
        · subst edge
          let Y := localStep ring sealSweepHomeFrontPair current hit
          have hstepLt : homeFrontHomeCount Y <
              homeFrontHomeCount current :=
            homeFrontHomeCount_localStep_lt_of_hit ring hn current hit hready
          have htailLe := homeFrontHomeCount_run_le ring Y rest
          have hfinalLt : homeFrontHomeCount
                (runLocalSchedule ring sealSweepHomeFrontPair Y rest) <
              homeFrontHomeCount source := by
            omega
          have hgood := (homeFrontDropOrReadyEndpointTest_spec ring source
            (runLocalSchedule ring sealSweepHomeFrontPair Y rest)).2
            (Or.inl hfinalLt)
          have hswap : homeFrontReadySuffixSwap hit out (out :: rest) =
              hit :: rest := by
            simp [homeFrontReadySuffixSwap, hhitOut, hhitOut.symm]
          rw [hswap]
          exact hgood
        · let Y := localStep ring sealSweepHomeFrontPair current edge
          have hbadY : homeFrontDropOrReadyEndpointTest ring source
              (runLocalSchedule ring sealSweepHomeFrontPair Y rest) = false := by
            simpa [Y, runLocalSchedule] using hbad
          have hstepLe' : homeFrontHomeCount Y ≤
              homeFrontHomeCount current := by
            simpa [Y] using
              homeFrontHomeCount_localStep_le ring current edge
          have htailLe := homeFrontHomeCount_run_le ring Y rest
          have hnotFinalLt : ¬ homeFrontHomeCount
                (runLocalSchedule ring sealSweepHomeFrontPair Y rest) <
              homeFrontHomeCount source := by
            intro hlt
            have hgood := (homeFrontDropOrReadyEndpointTest_spec ring source
              (runLocalSchedule ring sealSweepHomeFrontPair Y rest)).2
              (Or.inl hlt)
            rw [hbadY] at hgood
            contradiction
          have hYeq : homeFrontHomeCount Y =
              homeFrontHomeCount current := by
            omega
          have hreadyY : sealSweepFrontHitsHomePair
              (Y hit) (Y (ring.rightNeighbor hit)) = true := by
            exact homeFrontReadyAt_localStep_of_homeCount_eq
              ring hn current hit edge hready hedgeHit
              (by simpa [out] using hedgeOut) hYeq
          have hrecursive := ih Y (hYeq.trans hcount) hreadyY hbadY
          have hswap :
              homeFrontReadySuffixSwap hit out (edge :: rest) =
                edge :: homeFrontReadySuffixSwap hit out rest := by
            simp [homeFrontReadySuffixSwap, hedgeHit, hedgeOut]
          rw [hswap]
          simpa [Y, runLocalSchedule] using hrecursive

/-! ## Exact half-mass theorem -/

private theorem oneSite_ready_run_eq
    (ring : DirectedRing 1)
    (X : Fin 1 → SealSweepHomeFrontSite)
    (hready : HomeFrontHitReady ring X)
    (word : DetSchedule 1) :
    runLocalSchedule ring sealSweepHomeFrontPair X word = X := by
  obtain ⟨hit, hhit⟩ := hready
  have hneighbor : ring.rightNeighbor hit = hit := Subsingleton.elim _ _
  have hXA : X hit = (true, true) := by
    rcases hsite : X hit with ⟨home, front⟩
    cases home <;> cases front <;>
      simp [sealSweepFrontHitsHomePair, hneighbor, hsite] at hhit ⊢
  have hall : ∀ i : Fin 1, X i = (true, true) := by
    intro i
    have hi : i = hit := Subsingleton.elim _ _
    rw [hi]
    exact hXA
  have hstep : ∀ edge : Fin 1,
      localStep ring sealSweepHomeFrontPair X edge = X := by
    intro edge
    funext i
    have hie : i = edge := Subsingleton.elim _ _
    have hj : ring.rightNeighbor edge = edge := Subsingleton.elim _ _
    subst i
    simp [localStep, hj, hall, sealSweepHomeFrontPair]
  induction word with
  | nil => rfl
  | cons edge rest ih =>
      simp only [runLocalSchedule]
      rw [hstep edge]
      exact ih

/-- From every loaded quotient state, at least half of every exact scheduler
suffix layer ends below the source home count or loaded again.  No positivity,
balance, or reachability premise is needed. -/
theorem homeFrontHitReady_suffix_half_mass
    (ring : DirectedRing n)
    (X : Fin n → SealSweepHomeFrontSite)
    (hready : HomeFrontHitReady ring X) (r : Nat) :
    n ^ r ≤ 2 * homeFrontDropOrReadyEndpointCount ring X r := by
  by_cases hn : 1 < n
  · obtain ⟨hit, hhit⟩ := hready
    let out := ring.rightNeighbor hit
    have hne : hit ≠ out :=
      (rightNeighbor_ne_self_of_one_lt ring hn hit).symm
    let good : DetSchedule n → Bool := fun word =>
      homeFrontDropOrReadyEndpointTest ring X
        (runLocalSchedule ring sealSweepHomeFrontPair X word)
    have hbadGood : ∀ word, word ∈ allSchedules n r →
        good word = false →
        good (homeFrontReadySuffixSwap hit out word) = true := by
      intro word _hword hbad
      exact readySuffixSwap_good_of_bad ring hn X X hit rfl hhit word hbad
    have hmem : ∀ word, word ∈ allSchedules n r →
        homeFrontReadySuffixSwap hit out word ∈ allSchedules n r := by
      intro word hword
      apply mem_allSchedules_of_length n r
        (homeFrontReadySuffixSwap hit out word)
      rw [homeFrontReadySuffixSwap_length]
      exact allSchedules_schedule_length n r word hword
    have hbadLe := countP_not_le_countP_of_involution
      (allSchedules n r) good (homeFrontReadySuffixSwap hit out)
      (allSchedules_nodup n r)
      (homeFrontReadySuffixSwap_involutive hit out hne)
      hmem hbadGood
    have hpartition := countP_not_add_countP good (allSchedules n r)
    change n ^ r ≤ 2 * (allSchedules n r).countP good
    rw [← allSchedules_length n r]
    omega
  · have hnPos : 0 < n := by
      obtain ⟨hit, _⟩ := hready
      exact Fin.pos hit
    have hnOne : n = 1 := by omega
    subst n
    have hrun : ∀ word : DetSchedule 1,
        runLocalSchedule ring sealSweepHomeFrontPair X word = X :=
      oneSite_ready_run_eq ring X hready
    have hcount : homeFrontDropOrReadyEndpointCount ring X r =
        (allSchedules 1 r).length := by
      unfold homeFrontDropOrReadyEndpointCount
      apply List.countP_eq_length.mpr
      intro word _hword
      rw [hrun word]
      exact (homeFrontDropOrReadyEndpointTest_spec ring X X).2
        (Or.inr hready)
    rw [hcount, allSchedules_length]
    simp

#print axioms homeFrontHomeCount_run_le
#print axioms homeFrontReadyAt_localStep_of_homeCount_eq
#print axioms homeFrontReadySuffixSwap_involutive
#print axioms allSchedules_nodup
#print axioms homeFrontHitReady_suffix_half_mass

end PPartialSealSweepReadySuffixHalfMassSol
end PPLLCompleteMultiLeaderCleanup
