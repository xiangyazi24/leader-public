import Leader.Wu.Seal.ABGate
import Leader.Wu.Seal.SweepProtocol
import Leader.Wu.Seal.UniformScheduler
import Leader.Wu.Seal.MixedRankDriftObstruction

/-!
# Finite-time bricks for the seal-sweep TASEP reduction

The fixed-slice normalization and cyclic rotation modules are static.  This
module begins the genuinely dynamical part without treating stationarity as a
finite-time estimate.

First, the two boundary masses that do not require TASEP mixing are discharged
against the exact positive-descendant carrier.  A single front means a single
surviving output leader and is already Definition-1 safe.  Full front mass
forces every positive quotient site to be `A = (true, true)`, so the corrected
`Ready or AB` prefix gate is already true at horizon zero.

The second part records mass preservation, exact fixed-target column
multiplicity, and the local laziness estimate needed by a finite-chain
comparison route.  It then assembles duplicate-free backward target columns
for every horizon, proves their exact `n^t` size, and identifies them with the
fixed-slice row table.  Summing marked target columns gives an exact finite-time
stationary aggregate.  This remains an average over starting configurations;
no pointwise mixing or marked-endpoint lower bound is claimed here.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialSealSweepTasepFiniteTimeSol

open PPLL PPLLResearchFormulation PPLLTraceConvergence
open PPLLNoCheckBirthConditionTwoGeometry
open PPartialSealSweepIidDriftObstructionSol
open PPartialSealSweepHomeFrontQuotientSol
open PPartialSealSweepHomeTrapCurrentSol
open PPartialSealSweepABGateBreakthroughSol
open PPartialSealSweepTasepMixingFirstBrickSol
open PPartialSealSweepTasepRotationBridgeSol

set_option autoImplicit false

variable {n psi kappa tau : Nat}

/-! ## Finite sums used by both boundary and scheduler counts -/

open PPartialSealSweepOverlaySol
open PPartialSealSweepUniformSchedulerSol
open PPartialSealSweepPositiveLandingSol

private theorem tasepSum_ofFn_eq
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

private theorem tasepSum_ofFn_le
    (f g : Fin n -> Nat) (hfg : forall i, f i <= g i) :
    (List.ofFn f).sum <= (List.ofFn g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      exact Nat.add_le_add (hfg 0)
        (ih (fun i => f i.succ) (fun i => g i.succ)
          (fun i => hfg i.succ))

private theorem tasepSum_ofFn_lt_of_single_lt
    (f g : Fin n -> Nat) (j : Fin n)
    (hle : forall i, f i <= g i) (hlt : f j < g j) :
    (List.ofFn f).sum < (List.ofFn g).sum := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      by_cases hj0 : j = 0
      · subst j
        have htail := tasepSum_ofFn_le
          (fun i : Fin n => f i.succ) (fun i => g i.succ)
          (fun i => hle i.succ)
        omega
      · have hjpos : 0 < j.val := by
          have hjne : j.val ≠ 0 := fun h =>
            hj0 (Fin.ext (by simpa using h))
          omega
        let j' : Fin n := ⟨j.val - 1, by omega⟩
        have hjsucc : j'.succ = j := Fin.ext (by simp [j']; omega)
        have hlt' : f j'.succ < g j'.succ := by
          simpa only [hjsucc] using hlt
        have htail := ih
          (fun i : Fin n => f i.succ)
          (fun i : Fin n => g i.succ) j'
          (fun i => hle i.succ) hlt'
        have hhead := hle 0
        omega

private theorem tasepSum_ofFn_add
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

private theorem tasepSum_ofFn_mul_left
    (c : Nat) (f : Fin n -> Nat) :
    (List.ofFn (fun i => c * f i)).sum =
      c * (List.ofFn f).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons, ih, Nat.mul_add]

private theorem tasepSum_ofFn_mul_right
    (f : Fin n -> Nat) (c : Nat) :
    (List.ofFn (fun i => f i * c)).sum =
      (List.ofFn f).sum * c := by
  calc
    (List.ofFn (fun i => f i * c)).sum =
        (List.ofFn (fun i => c * f i)).sum :=
      tasepSum_ofFn_eq _ _ (fun i => Nat.mul_comm _ _)
    _ = c * (List.ofFn f).sum := tasepSum_ofFn_mul_left c f
    _ = (List.ofFn f).sum * c := Nat.mul_comm _ _

private theorem tasepSum_ofFn_sum_comm
    {m q : Nat} (f : Fin m -> Fin q -> Nat) :
    (List.ofFn (fun i : Fin m =>
      (List.ofFn (fun j : Fin q => f i j)).sum)).sum =
      (List.ofFn (fun j : Fin q =>
        (List.ofFn (fun i : Fin m => f i j)).sum)).sum := by
  induction m with
  | zero =>
      have hzero :
          (List.ofFn (fun _ : Fin q => 0)).sum = 0 := by
        simpa using
          (tasepSum_ofFn_mul_left (n := q) 0 (fun _ : Fin q => 1))
      simpa using hzero.symm
  | succ m ih =>
      calc
        (List.ofFn (fun i : Fin (m + 1) =>
            (List.ofFn (fun j : Fin q => f i j)).sum)).sum =
            (List.ofFn (fun j : Fin q => f 0 j)).sum +
              (List.ofFn (fun i : Fin m =>
                (List.ofFn (fun j : Fin q => f i.succ j)).sum)).sum := by
          rw [List.ofFn_succ, List.sum_cons]
        _ = (List.ofFn (fun j : Fin q => f 0 j)).sum +
              (List.ofFn (fun j : Fin q =>
                (List.ofFn (fun i : Fin m => f i.succ j)).sum)).sum := by
          rw [ih (fun i j => f i.succ j)]
        _ = (List.ofFn (fun j : Fin q =>
              f 0 j + (List.ofFn (fun i : Fin m => f i.succ j)).sum)).sum :=
          (tasepSum_ofFn_add
            (fun j : Fin q => f 0 j)
            (fun j : Fin q =>
              (List.ofFn (fun i : Fin m => f i.succ j)).sum)).symm
        _ = (List.ofFn (fun j : Fin q =>
              (List.ofFn (fun i : Fin (m + 1) => f i j)).sum)).sum := by
          apply tasepSum_ofFn_eq
          intro j
          rw [List.ofFn_succ, List.sum_cons]

private theorem tasepSum_ofFn_const_one (m : Nat) :
    (List.ofFn (fun _ : Fin m => 1)).sum = m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons, ih]
      omega

private theorem tasepSum_map_const
    {alpha : Type} (xs : List alpha) (c : Nat) :
    (xs.map (fun _ => c)).sum = xs.length * c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
      rw [Nat.succ_mul]
      exact Nat.add_comm _ _

private theorem tasepLength_filter_flatMap
    {alpha beta : Type} (xs : List alpha) (f : alpha -> List beta)
    (p : beta -> Bool) :
    ((xs.flatMap f).filter p).length =
      (xs.map (fun x => (f x).countP p)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.filter_append,
        List.length_append, List.map_cons, List.sum_cons, ih]
      rw [List.countP_eq_length_filter]

private theorem tasepCountP_filter_eq_countP_and
    {alpha : Type} (xs : List alpha) (keep p : alpha -> Bool) :
    (xs.filter keep).countP p =
      xs.countP (fun x => keep x && p x) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases hk : keep x <;> cases hp : p x <;>
        simp [hk, hp, ih]

private theorem tasepSum_ofFn_rightNeighbor
    (ring : DirectedRing n) (f : Fin n -> Nat) :
    (List.ofFn (fun i => f (ring.rightNeighbor i))).sum =
      (List.ofFn f).sum := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt ring.hn)
  subst n
  rw [show List.ofFn
      (fun i : Fin (m + 1) => f (ring.rightNeighbor i)) =
    (List.ofFn (fun i : Fin m =>
      f (ring.rightNeighbor i.castSucc))) ++
      [f (ring.rightNeighbor (Fin.last m))] from List.ofFn_succ_last]
  rw [List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero,
    List.ofFn_succ, List.sum_cons]
  have hlast : ring.rightNeighbor (Fin.last m) = 0 := by
    apply Fin.ext
    simp [DirectedRing.rightNeighbor]
  have hsucc : forall i : Fin m,
      ring.rightNeighbor i.castSucc = i.succ := by
    intro i
    apply Fin.ext
    simp [DirectedRing.rightNeighbor,
      Nat.mod_eq_of_lt (by omega : i.val + 1 < m + 1)]
  rw [hlast]
  have hfun :
      (fun i : Fin m => f (ring.rightNeighbor i.castSucc)) =
        (fun i : Fin m => f i.succ) := by
    funext i
    rw [hsucc]
  rw [hfun]
  omega

private theorem tasepSum_ofFn_balance_one
    (f g : Fin n -> Nat) (j : Fin n)
    (hother : forall i, i ≠ j -> f i = g i) :
    (List.ofFn f).sum + g j = (List.ofFn g).sum + f j := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      by_cases hj0 : j = 0
      · subst j
        have htail :
            (List.ofFn (fun i : Fin n => f i.succ)).sum =
              (List.ofFn (fun i : Fin n => g i.succ)).sum := by
          apply tasepSum_ofFn_eq
          intro i
          apply hother i.succ
          intro hbad
          have hv := congrArg Fin.val hbad
          simp at hv
        rw [htail]
        omega
      · have hjpos : 0 < j.val := by
          have hjne : j.val ≠ 0 := by
            intro h
            apply hj0
            apply Fin.ext
            simpa using h
          omega
        let j' : Fin n := ⟨j.val - 1, by omega⟩
        have hjsucc : j'.succ = j := by
          apply Fin.ext
          change j.val - 1 + 1 = j.val
          omega
        have hhead : f 0 = g 0 := hother 0 (Ne.symm hj0)
        have htail := ih
          (fun i : Fin n => f i.succ)
          (fun i : Fin n => g i.succ) j'
          (by
            intro i hij
            apply hother i.succ
            intro hbad
            apply hij
            apply Fin.ext
            have hv := congrArg Fin.val hbad
            change i.val + 1 = j.val at hv
            change i.val = j.val - 1
            omega)
        change
          (List.ofFn (fun i : Fin n => f i.succ)).sum + g j'.succ =
            (List.ofFn (fun i : Fin n => g i.succ)).sum + f j'.succ
          at htail
        rw [hjsucc] at htail
        omega

private theorem tasepSum_ofFn_balance_two
    (f g : Fin n -> Nat) (a b : Fin n) (hab : a ≠ b)
    (hother : forall i, i ≠ a -> i ≠ b -> f i = g i) :
    (List.ofFn f).sum + g a + g b =
      (List.ofFn g).sum + f a + f b := by
  let mid : Fin n -> Nat := fun i => if i = a then f i else g i
  have hga : (List.ofFn mid).sum + g a =
      (List.ofFn g).sum + mid a := by
    apply tasepSum_ofFn_balance_one mid g a
    intro i hia
    simp [mid, hia]
  have hfb : (List.ofFn f).sum + mid b =
      (List.ofFn mid).sum + f b := by
    apply tasepSum_ofFn_balance_one f mid b
    intro i hib
    by_cases hia : i = a
    · subst i
      simp [mid]
    · simp [mid, hia, hother i hia hib]
  have hma : mid a = f a := by simp [mid]
  have hmb : mid b = g b := by simp [mid, Ne.symm hab]
  rw [hma] at hga
  rw [hmb] at hfb
  omega

/-! ## Explicit finite function-space slices -/

/-- Add one Boolean coordinate at the front of a finite configuration. -/
def prependTasepFront {m : Nat} (b : Bool)
    (F : Fin m -> Bool) : Fin (m + 1) -> Bool :=
  Fin.cases b F

/-- Every Boolean function on `Fin m`, enumerated recursively with
multiplicity one. -/
def tasepAllFrontConfigs : (m : Nat) -> List (Fin m -> Bool)
  | 0 => [fun i => Fin.elim0 i]
  | m + 1 =>
      (tasepAllFrontConfigs m).flatMap (fun F =>
        [prependTasepFront false F, prependTasepFront true F])

@[simp] theorem prependTasepFront_zero
    {m : Nat} (b : Bool) (F : Fin m -> Bool) :
    prependTasepFront b F 0 = b := rfl

@[simp] theorem prependTasepFront_succ
    {m : Nat} (b : Bool) (F : Fin m -> Bool) (i : Fin m) :
    prependTasepFront b F i.succ = F i := rfl

/-- Completeness of the explicit Boolean function enumeration. -/
theorem mem_tasepAllFrontConfigs
    {m : Nat} (F : Fin m -> Bool) :
    F ∈ tasepAllFrontConfigs m := by
  induction m with
  | zero =>
      have hF : F = fun i => Fin.elim0 i := by
        funext i
        exact Fin.elim0 i
      simp [tasepAllFrontConfigs, hF]
  | succ m ih =>
      let tail : Fin m -> Bool := fun i => F i.succ
      have htail : tail ∈ tasepAllFrontConfigs m := ih tail
      rw [tasepAllFrontConfigs, List.mem_flatMap]
      refine ⟨tail, htail, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      cases hzero : F 0
      · left
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [prependTasepFront, hzero]
        · simp [prependTasepFront, tail]
      · right
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [prependTasepFront, hzero]
        · simp [prependTasepFront, tail]

private theorem tasepConfigNodup_flatMap_of_nodup
    {alpha beta : Type} (xs : List alpha) (f : alpha -> List beta)
    (hxs : xs.Nodup)
    (hfn : forall x, x ∈ xs -> (f x).Nodup)
    (hdisjoint : forall x, x ∈ xs -> forall y, y ∈ xs -> x ≠ y ->
      forall a, a ∈ f x -> forall b, b ∈ f y -> a ≠ b) :
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

/-- No Boolean function is duplicated in `tasepAllFrontConfigs`. -/
theorem tasepAllFrontConfigs_nodup (m : Nat) :
    (tasepAllFrontConfigs m).Nodup := by
  induction m with
  | zero => simp [tasepAllFrontConfigs]
  | succ m ih =>
      rw [tasepAllFrontConfigs]
      apply tasepConfigNodup_flatMap_of_nodup _ _ ih
      · intro F _hF
        have hne : prependTasepFront false F ≠
            prependTasepFront true F := by
          intro h
          have hzero := congrFun h 0
          simp at hzero
        simp [hne]
      · intro F _hF G _hG hFG A hA B hB
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hA hB
        rcases hA with rfl | rfl <;>
          rcases hB with rfl | rfl <;>
            intro hEq <;> apply hFG <;> funext i <;>
              have hi := congrFun hEq i.succ <;>
              simpa using hi

/-- Prefixing a function matches prefixing its exact `List.ofFn` encoding. -/
theorem frontConfigWord_prependTasepFront
    {m : Nat} (b : Bool) (F : Fin m -> Bool) :
    frontConfigWord (prependTasepFront b F) =
      b :: frontConfigWord F := by
  simp [frontConfigWord, List.ofFn_succ, prependTasepFront]

/-- The function enumeration is termwise the existing word enumeration. -/
theorem tasepAllFrontConfigs_map_frontConfigWord (m : Nat) :
    (tasepAllFrontConfigs m).map frontConfigWord = allFrontWords m := by
  induction m with
  | zero => simp [tasepAllFrontConfigs, allFrontWords, frontConfigWord]
  | succ m ih =>
      rw [tasepAllFrontConfigs, allFrontWords, List.map_flatMap, ← ih,
        List.flatMap_map]
      congr
      funext F
      simp [frontConfigWord_prependTasepFront]

/-- Explicit list of all Boolean configurations of front mass `k`. -/
def tasepFrontConfigSlice (m k : Nat) : List (Fin m -> Bool) :=
  (tasepAllFrontConfigs m).filter
    (fun F => decide (frontConfigMass F = k))

/-- The slice predicate has no hidden reachability or protocol condition. -/
theorem mem_tasepFrontConfigSlice_iff
    {m k : Nat} (F : Fin m -> Bool) :
    F ∈ tasepFrontConfigSlice m k ↔ frontConfigMass F = k := by
  simp [tasepFrontConfigSlice, mem_tasepAllFrontConfigs]

private theorem tasepConfigNodup_filter_of_nodup
    {alpha : Type} (p : alpha -> Bool) (xs : List alpha)
    (hxs : xs.Nodup) : (xs.filter p).Nodup := by
  rw [List.nodup_iff_pairwise_ne] at hxs ⊢
  exact hxs.filter p

/-- The fixed-mass slice is itself multiplicity-free. -/
theorem tasepFrontConfigSlice_nodup (m k : Nat) :
    (tasepFrontConfigSlice m k).Nodup := by
  exact tasepConfigNodup_filter_of_nodup _ _
    (tasepAllFrontConfigs_nodup m)

/-- Its length is the existing explicit fixed-word count. -/
theorem tasepFrontConfigSlice_length_eq_wordCount (m k : Nat) :
    (tasepFrontConfigSlice m k).length = frontSliceWordCount m k := by
  unfold tasepFrontConfigSlice frontSliceWordCount
  rw [← List.countP_eq_length_filter]
  rw [← tasepAllFrontConfigs_map_frontConfigWord m, List.countP_map]
  apply congrArg (fun p => (tasepAllFrontConfigs m).countP p)
  funext F
  simp only [Function.comp_apply]
  rw [frontWordMass_frontConfigWord]

/-- Therefore the concrete function-space slice has Pascal cardinality. -/
theorem tasepFrontConfigSlice_length_eq_card (m k : Nat) :
    (tasepFrontConfigSlice m k).length = frontSliceCard m k := by
  rw [tasepFrontConfigSlice_length_eq_wordCount,
    frontSliceWordCount_eq_card]

/-! ## The `k = 1` and `k = n` boundary consumers -/

/-- The exact function-space front mass of a projected physical configuration
is the existing physical front count. -/
theorem frontConfigMass_physicalProjection
    (C : SealSweepConfig n psi kappa tau) :
    frontConfigMass
        (homeFrontFrontProjection (sealSweepHomeFrontConfig C)) =
      sealSweepFrontCount C := by
  rfl

/-- On a positive descendant, front mass one is already genuine semantic
safety; no TASEP estimate is needed for this boundary. -/
theorem positiveDescendant_frontMass_one_isSafe
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau)
    (hdesc : SealSweepPositiveDescendant ring C)
    (hmass : frontConfigMass
      (homeFrontFrontProjection (sealSweepHomeFrontConfig C)) = 1) :
    PopulationProtocol.IsSafe
      (P_partialSealSweepProtocol psi kappa tau) ring C
      isLeaderOutput := by
  apply positiveDescendant_leaderCount_one_isSafe ring C hdesc
  rw [← positiveDescendant_frontCount_eq_leaderCount ring C hdesc]
  rw [← frontConfigMass_physicalProjection C]
  exact hmass

/-- Quotient-facing form of the mass-one boundary.  The witness is the actual
positive physical carrier retained by `SealSweepPositiveHomeFrontState`. -/
theorem positiveHomeFront_frontMass_one_hasSafeCarrier
    (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite)
    (hX : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring X)
    (hmass : frontConfigMass (homeFrontFrontProjection X) = 1) :
    exists C : SealSweepConfig n psi kappa tau,
      sealSweepHomeFrontConfig C = X /\
      PopulationProtocol.IsSafe
        (P_partialSealSweepProtocol psi kappa tau) ring C
        isLeaderOutput := by
  obtain ⟨C, hdesc, hprojection⟩ := hX
  refine ⟨C, hprojection, ?_⟩
  apply positiveDescendant_frontMass_one_isSafe ring C hdesc
  rw [hprojection]
  exact hmass

/-- A Boolean function on `Fin n` whose exact occupied count is `n` is true
at every coordinate. -/
theorem frontConfigMass_eq_card_implies_all_true
    (F : Fin n -> Bool) (hmass : frontConfigMass F = n) :
    forall i, F i = true := by
  intro i
  cases hi : F i with
  | true => rfl
  | false =>
      have hle : forall j : Fin n,
          (if F j then 1 else 0) <= 1 := by
        intro j
        cases F j <;> simp
      have hlt : (if F i then 1 else 0) < 1 := by
        simp [hi]
      have hsumlt := tasepSum_ofFn_lt_of_single_lt
        (fun j : Fin n => if F j then 1 else 0)
        (fun _ : Fin n => 1) i hle hlt
      rw [tasepSum_ofFn_const_one] at hsumlt
      exact False.elim (by
        unfold frontConfigMass at hmass
        omega)

/-- Home count is the same finite Boolean sum as `frontConfigMass` applied to
the home projection. -/
theorem frontConfigMass_homeFrontHomeProjection
    (X : Fin n -> SealSweepHomeFrontSite) :
    frontConfigMass (homeFrontHomeProjection X) =
      homeFrontHomeCount X := by
  rfl

/-- Full front mass in the exact positive quotient image forces every site to
be `A = (true, true)`. -/
theorem positiveHomeFront_fullFrontMass_all_A
    (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite)
    (hX : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring X)
    (hmass : frontConfigMass (homeFrontFrontProjection X) = n) :
    forall i, X i = (true, true) := by
  obtain ⟨C, hdesc, hprojection⟩ := hX
  have hfrontPhysical : sealSweepFrontCount C = n := by
    rw [← frontConfigMass_physicalProjection C, hprojection]
    exact hmass
  have hleaders : sealSweepLeaderCount C = n := by
    rw [← positiveDescendant_frontCount_eq_leaderCount ring C hdesc]
    exact hfrontPhysical
  have hhomeMass : frontConfigMass (homeFrontHomeProjection X) = n := by
    rw [frontConfigMass_homeFrontHomeProjection]
    rw [← hprojection, homeFrontHomeCount_projection]
    exact hleaders
  have hallFront := frontConfigMass_eq_card_implies_all_true
    (homeFrontFrontProjection X) hmass
  have hallHome := frontConfigMass_eq_card_implies_all_true
    (homeFrontHomeProjection X) hhomeMass
  intro i
  exact Prod.ext (hallHome i) (hallFront i)

/-- The full-mass positive boundary is already in the corrected prefix gate
at time zero. -/
theorem positiveHomeFront_fullFrontMass_readyOrAB
    (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite)
    (hX : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring X)
    (hmass : frontConfigMass (homeFrontFrontProjection X) = n) :
    HomeFrontReadyOrAB ring X := by
  have hall := positiveHomeFront_fullFrontMass_all_A ring X hX hmass
  left
  let edge : Fin n := ⟨0, ring.hn⟩
  refine ⟨edge, ?_⟩
  simp [sealSweepFrontHitsHomePair, hall edge,
    hall (ring.rightNeighbor edge)]

/-- Consequently the corrected inverse-square prefix gate holds at horizon
zero on the full-mass boundary. -/
theorem positiveHomeFront_fullFrontMass_readyOrABHitGate_zero
    (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite)
    (hX : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring X)
    (hmass : frontConfigMass (homeFrontFrontProjection X) = n) :
    HomeFrontInverseSquareReadyOrABHitGate ring X 0 := by
  have hgate := positiveHomeFront_fullFrontMass_readyOrAB ring X hX hmass
  have hpositive : 0 < n ^ 2 := Nat.pow_pos ring.hn
  unfold HomeFrontInverseSquareReadyOrABHitGate
  simp [homeFrontReadyOrABHitTree, hgate]
  omega

/-! ## A local half-laziness estimate for clockwise TASEP -/

/-- The local `10 -> 01` rule preserves the number of occupied endpoints. -/
theorem clockwiseTasepPair_mass
    (l r : Bool) :
    (if (clockwiseTasepPair l r).1 then 1 else 0) +
        (if (clockwiseTasepPair l r).2 then 1 else 0) =
      (if l then 1 else 0) + (if r then 1 else 0) := by
  cases l <;> cases r <;> rfl

/-- Every exact clockwise-TASEP scheduler edge stays inside its fixed-front
mass slice. -/
theorem frontConfigMass_clockwiseTasep_localStep
    (ring : DirectedRing n) (hn : 1 < n)
    (F : Fin n -> Bool) (edge : Fin n) :
    frontConfigMass
        (localStep ring clockwiseTasepPair F edge) =
      frontConfigMass F := by
  let j := ring.rightNeighbor edge
  let after := localStep ring clockwiseTasepPair F edge
  let f : Fin n -> Nat := fun i => if after i then 1 else 0
  let g : Fin n -> Nat := fun i => if F i then 1 else 0
  have hje : j ≠ edge :=
    rightNeighbor_ne_self_of_one_lt ring hn edge
  have hother : forall i, i ≠ edge -> i ≠ j -> f i = g i := by
    intro i hie hij
    simp [f, g, after, localStep, j, hie, hij]
  have hbalance := tasepSum_ofFn_balance_two
    f g edge j hje.symm hother
  have hpairs : f edge + f j = g edge + g j := by
    simpa [f, g, after, localStep, j, hje] using
      clockwiseTasepPair_mass (F edge) (F j)
  unfold frontConfigMass
  change (List.ofFn f).sum = (List.ofFn g).sum
  omega

/-- Every finite clockwise-TASEP schedule stays in its initial front-mass
slice. -/
theorem frontConfigMass_runLocalSchedule_clockwiseTasep
    (ring : DirectedRing n) (hn : 1 < n)
    (F : Fin n -> Bool) (word : DetSchedule n) :
    frontConfigMass
        (runLocalSchedule ring clockwiseTasepPair F word) =
      frontConfigMass F := by
  induction word generalizing F with
  | nil => rfl
  | cons edge rest ih =>
      simp only [runLocalSchedule]
      rw [ih, frontConfigMass_clockwiseTasep_localStep ring hn]

/-- Boolean test for an active clockwise TASEP edge, namely `10`. -/
def tasepActive10Test (ring : DirectedRing n)
    (F : Fin n -> Bool) (edge : Fin n) : Bool :=
  F edge && !F (ring.rightNeighbor edge)

/-- Number of active scheduler edges in one TASEP row. -/
def tasepActive10EdgeCount (ring : DirectedRing n)
    (F : Fin n -> Bool) : Nat :=
  (List.ofFn (fun edge : Fin n =>
    if tasepActive10Test ring F edge then 1 else 0)).sum

/-- Number of scheduler edges on which the TASEP row stutters. -/
def tasepStutterEdgeCount (ring : DirectedRing n)
    (F : Fin n -> Bool) : Nat :=
  (List.ofFn (fun edge : Fin n =>
    if tasepActive10Test ring F edge then 0 else 1)).sum

/-- The successor of an active `10` edge starts with zero, so it is not itself
an active edge. -/
theorem tasepActive10Test_rightNeighbor_false_of_true
    (ring : DirectedRing n) (F : Fin n -> Bool) (edge : Fin n)
    (hactive : tasepActive10Test ring F edge = true) :
    tasepActive10Test ring F (ring.rightNeighbor edge) = false := by
  unfold tasepActive10Test at hactive ⊢
  have hright : F (ring.rightNeighbor edge) = false := by
    simpa using (Bool.and_eq_true_iff.mp hactive).2
  simp [hright]

/-- Pointwise packing: an edge and its clockwise successor cannot both be
active. -/
theorem tasepActive10_indicator_adjacent_le_one
    (ring : DirectedRing n) (F : Fin n -> Bool) (edge : Fin n) :
    (if tasepActive10Test ring F edge then 1 else 0) +
        (if tasepActive10Test ring F (ring.rightNeighbor edge)
          then 1 else 0) <= 1 := by
  cases hactive : tasepActive10Test ring F edge with
  | false =>
      cases tasepActive10Test ring F (ring.rightNeighbor edge) <;>
        simp [hactive]
  | true =>
      have hnext := tasepActive10Test_rightNeighbor_false_of_true
        ring F edge hactive
      simp [hactive, hnext]

/-- At most half of the directed edges are active `10` edges.  This is an
exact cyclic packing count, not a stationary assertion. -/
theorem two_mul_tasepActive10EdgeCount_le
    (ring : DirectedRing n) (F : Fin n -> Bool) :
    2 * tasepActive10EdgeCount ring F <= n := by
  let active : Fin n -> Nat := fun edge =>
    if tasepActive10Test ring F edge then 1 else 0
  have hpoint : forall edge : Fin n,
      active edge + active (ring.rightNeighbor edge) <= 1 := by
    intro edge
    exact tasepActive10_indicator_adjacent_le_one ring F edge
  have hsum := tasepSum_ofFn_le
    (fun edge : Fin n => active edge +
      active (ring.rightNeighbor edge))
    (fun _ : Fin n => 1) hpoint
  rw [tasepSum_ofFn_add,
    tasepSum_ofFn_rightNeighbor ring active,
    tasepSum_ofFn_const_one] at hsum
  dsimp [active] at hsum
  unfold tasepActive10EdgeCount
  omega

/-- Active and stuttering scheduler edges partition the `n` choices exactly. -/
theorem tasepActive10EdgeCount_add_stutterEdgeCount
    (ring : DirectedRing n) (F : Fin n -> Bool) :
    tasepActive10EdgeCount ring F + tasepStutterEdgeCount ring F = n := by
  unfold tasepActive10EdgeCount tasepStutterEdgeCount
  rw [← tasepSum_ofFn_add]
  rw [show
      (fun edge : Fin n =>
          (if tasepActive10Test ring F edge then 1 else 0) +
            (if tasepActive10Test ring F edge then 0 else 1)) =
        (fun _ : Fin n => 1) by
    funext edge
    cases tasepActive10Test ring F edge <;> rfl]
  exact tasepSum_ofFn_const_one n

/-- At least half of every clockwise-TASEP scheduler row consists of stutter
choices. -/
theorem n_le_two_mul_tasepStutterEdgeCount
    (ring : DirectedRing n) (F : Fin n -> Bool) :
    n <= 2 * tasepStutterEdgeCount ring F := by
  have hactive := two_mul_tasepActive10EdgeCount_le ring F
  have hpartition :=
    tasepActive10EdgeCount_add_stutterEdgeCount ring F
  omega

/-- An inactive TASEP clock is an actual configuration self-loop. -/
theorem clockwiseTasep_localStep_eq_self_of_inactive
    (ring : DirectedRing n) (hn : 1 < n)
    (F : Fin n -> Bool) (edge : Fin n)
    (hinactive : tasepActive10Test ring F edge = false) :
    localStep ring clockwiseTasepPair F edge = F := by
  let j := ring.rightNeighbor edge
  have hpair : clockwiseTasepPair (F edge) (F j) =
      (F edge, F j) := by
    change (F edge && Bool.not (F j)) = false at hinactive
    simp [clockwiseTasepPair, hinactive]
  funext i
  have hje : j ≠ edge :=
    rightNeighbor_ne_self_of_one_lt ring hn edge
  by_cases hie : i = edge
  · subst i
    simpa [localStep, j] using congrArg Prod.fst hpair
  · by_cases hij : i = j
    · subst i
      simpa [localStep, j, hie] using congrArg Prod.snd hpair
    · simp [localStep, j, hie, hij]

/-! ## Exact cyclic column weights -/

/-- Boolean test for a rising target edge `01`.  These are precisely the
target edges which have both the stuttering predecessor and the directed
`10 -> 01` predecessor. -/
def tasepRising01Test (ring : DirectedRing n)
    (F : Fin n -> Bool) (edge : Fin n) : Bool :=
  !F edge && F (ring.rightNeighbor edge)

/-- Number of rising `01` edges in one cyclic Boolean configuration. -/
def tasepRising01EdgeCount (ring : DirectedRing n)
    (F : Fin n -> Bool) : Nat :=
  (List.ofFn (fun edge : Fin n =>
    if tasepRising01Test ring F edge then 1 else 0)).sum

/-- Pointwise discrete-current identity.  Occupancy plus an incoming `01`
rise equals successor occupancy plus an outgoing `10` fall. -/
theorem tasep_occupancy_add_rising_eq_right_add_active
    (ring : DirectedRing n) (F : Fin n -> Bool) (edge : Fin n) :
    (if F edge then 1 else 0) +
        (if tasepRising01Test ring F edge then 1 else 0) =
      (if F (ring.rightNeighbor edge) then 1 else 0) +
        (if tasepActive10Test ring F edge then 1 else 0) := by
  cases hleft : F edge <;>
    cases hright : F (ring.rightNeighbor edge) <;>
      simp [tasepRising01Test, tasepActive10Test, hleft, hright]

/-- A cyclic Boolean word has equally many `01` and `10` boundary edges.
This is the exact cancellation needed for column sums; it does not use a
stationary distribution. -/
theorem tasepRising01EdgeCount_eq_active10EdgeCount
    (ring : DirectedRing n) (F : Fin n -> Bool) :
    tasepRising01EdgeCount ring F =
      tasepActive10EdgeCount ring F := by
  let occupied : Fin n -> Nat := fun edge =>
    if F edge then 1 else 0
  let rising : Fin n -> Nat := fun edge =>
    if tasepRising01Test ring F edge then 1 else 0
  let active : Fin n -> Nat := fun edge =>
    if tasepActive10Test ring F edge then 1 else 0
  have hpoint : forall edge : Fin n,
      occupied edge + rising edge =
        occupied (ring.rightNeighbor edge) + active edge := by
    intro edge
    exact tasep_occupancy_add_rising_eq_right_add_active ring F edge
  have hsum := tasepSum_ofFn_eq
    (fun edge : Fin n => occupied edge + rising edge)
    (fun edge : Fin n =>
      occupied (ring.rightNeighbor edge) + active edge) hpoint
  rw [tasepSum_ofFn_add, tasepSum_ofFn_add,
    tasepSum_ofFn_rightNeighbor ring occupied] at hsum
  unfold tasepRising01EdgeCount tasepActive10EdgeCount
  dsimp [rising, active] at hsum
  omega

/-- Local numeric weight of one target column.  Its truth table on the target
pair `00/11/10/01` is respectively `1/1/0/2`.  The later predecessor
classification below justifies this table without enumerating function space. -/
def tasepColumnWeightAt (ring : DirectedRing n)
    (G : Fin n -> Bool) (edge : Fin n) : Nat :=
  match G edge, G (ring.rightNeighbor edge) with
  | false, false => 1
  | true, true => 1
  | true, false => 0
  | false, true => 2

/-- The column weight differs from the baseline one exactly by adding a
rising `01` predecessor and deleting an impossible `10` target. -/
theorem tasepColumnWeightAt_add_active
    (ring : DirectedRing n) (G : Fin n -> Bool) (edge : Fin n) :
    tasepColumnWeightAt ring G edge +
        (if tasepActive10Test ring G edge then 1 else 0) =
      1 + (if tasepRising01Test ring G edge then 1 else 0) := by
  cases hleft : G edge <;>
    cases hright : G (ring.rightNeighbor edge) <;>
      simp [tasepColumnWeightAt, tasepActive10Test,
        tasepRising01Test, hleft, hright]

/-- Exact fixed-target column-weight sum.  The proof is the finite cyclic
identity `n + #01 - #10 = n`, expressed without subtraction. -/
theorem tasepColumnWeight_sum_eq_card
    (ring : DirectedRing n) (G : Fin n -> Bool) :
    (List.ofFn (fun edge : Fin n =>
      tasepColumnWeightAt ring G edge)).sum = n := by
  have hpoint : forall edge : Fin n,
      tasepColumnWeightAt ring G edge +
          (if tasepActive10Test ring G edge then 1 else 0) =
        1 + (if tasepRising01Test ring G edge then 1 else 0) :=
    tasepColumnWeightAt_add_active ring G
  have hsum := tasepSum_ofFn_eq
    (fun edge : Fin n => tasepColumnWeightAt ring G edge +
      (if tasepActive10Test ring G edge then 1 else 0))
    (fun edge : Fin n => 1 +
      (if tasepRising01Test ring G edge then 1 else 0)) hpoint
  rw [tasepSum_ofFn_add, tasepSum_ofFn_add,
    tasepSum_ofFn_const_one] at hsum
  have hcyclic := tasepRising01EdgeCount_eq_active10EdgeCount ring G
  unfold tasepActive10EdgeCount tasepRising01EdgeCount at hcyclic
  rw [hcyclic] at hsum
  exact Nat.add_right_cancel hsum

/-! ## Actual directed predecessor orientation -/

/-- For a target edge, overwrite its endpoints by `10`.  When the target is
`01`, this is the unique nonstuttering predecessor suggested by the column
truth table. -/
def tasepReverseSourceAt (ring : DirectedRing n)
    (G : Fin n -> Bool) (edge : Fin n) : Fin n -> Bool :=
  fun i => if i = edge then true
    else if i = ring.rightNeighbor edge then false else G i

/-- Symmetric adjacent transposition at one directed-ring edge.  This is a
pure coordinate swap, independent of the TASEP orientation. -/
def swapFrontConfigAt (ring : DirectedRing n)
    (F : Fin n -> Bool) (edge : Fin n) : Fin n -> Bool :=
  fun i => if i = edge then F (ring.rightNeighbor edge)
    else if i = ring.rightNeighbor edge then F edge else F i

@[simp] theorem swapFrontConfigAt_edge
    (ring : DirectedRing n) (F : Fin n -> Bool) (edge : Fin n) :
    swapFrontConfigAt ring F edge edge =
      F (ring.rightNeighbor edge) := by
  simp [swapFrontConfigAt]

theorem swapFrontConfigAt_rightNeighbor
    (ring : DirectedRing n) (hn : 1 < n)
    (F : Fin n -> Bool) (edge : Fin n) :
    swapFrontConfigAt ring F edge (ring.rightNeighbor edge) =
      F edge := by
  have hje := rightNeighbor_ne_self_of_one_lt ring hn edge
  simp [swapFrontConfigAt, hje]

/-- Swapping unequal adjacent endpoints changes the configuration. -/
theorem swapFrontConfigAt_ne_of_endpoint_ne
    (ring : DirectedRing n) (F : Fin n -> Bool) (edge : Fin n)
    (hne : F edge ≠ F (ring.rightNeighbor edge)) :
    swapFrontConfigAt ring F edge ≠ F := by
  intro heq
  have hedge := congrFun heq edge
  have hedge' : F (ring.rightNeighbor edge) = F edge := by
    simpa using hedge
  exact hne hedge'.symm

/-- On an active `10`, the directed TASEP step is exactly the symmetric
adjacent swap. -/
theorem clockwiseTasep_localStep_eq_swapFrontConfigAt_of_active
    (ring : DirectedRing n) (hn : 1 < n)
    (F : Fin n -> Bool) (edge : Fin n)
    (hactive : tasepActive10Test ring F edge = true) :
    localStep ring clockwiseTasepPair F edge =
      swapFrontConfigAt ring F edge := by
  let j := ring.rightNeighbor edge
  have hje : j ≠ edge :=
    rightNeighbor_ne_self_of_one_lt ring hn edge
  have hleft : F edge = true := by
    simpa [tasepActive10Test] using
      (Bool.and_eq_true_iff.mp hactive).1
  have hright : F j = false := by
    simpa [tasepActive10Test, j] using
      (Bool.and_eq_true_iff.mp hactive).2
  funext i
  by_cases hie : i = edge
  · subst i
    simp [localStep, clockwiseTasepPair, swapFrontConfigAt,
      j, hleft, hright]
  · by_cases hij : i = j
    · subst i
      simp [localStep, clockwiseTasepPair, swapFrontConfigAt,
        j, hje, hleft, hright]
    · simp [localStep, clockwiseTasepPair, swapFrontConfigAt,
        j, hie, hij, hleft, hright]

/-- On a rising `01` target, the symmetric swap is definitionally the
explicit active reverse source. -/
theorem swapFrontConfigAt_eq_tasepReverseSourceAt_of_rising
    (ring : DirectedRing n) (hn : 1 < n)
    (G : Fin n -> Bool) (edge : Fin n)
    (hrising : tasepRising01Test ring G edge = true) :
    swapFrontConfigAt ring G edge =
      tasepReverseSourceAt ring G edge := by
  let j := ring.rightNeighbor edge
  have hje : j ≠ edge :=
    rightNeighbor_ne_self_of_one_lt ring hn edge
  have hleft : G edge = false := by
    simpa [tasepRising01Test] using
      (Bool.and_eq_true_iff.mp hrising).1
  have hright : G j = true := by
    simpa [tasepRising01Test, j] using
      (Bool.and_eq_true_iff.mp hrising).2
  funext i
  by_cases hie : i = edge
  · subst i
    simp [swapFrontConfigAt, tasepReverseSourceAt, j, hright]
  · by_cases hij : i = j
    · subst i
      simp [swapFrontConfigAt, tasepReverseSourceAt,
        j, hje, hleft]
    · simp [swapFrontConfigAt, tasepReverseSourceAt,
        j, hie, hij]

/-- The local pair rule has only the stuttering input and the directed
`10 -> 01` input as possible preimage forms. -/
theorem clockwiseTasepPair_preimage_cases
    (l r gl gr : Bool)
    (hpair : clockwiseTasepPair l r = (gl, gr)) :
    (l = gl /\ r = gr) \/
      (gl = false /\ gr = true /\ l = true /\ r = false) := by
  cases l <;> cases r <;> cases gl <;> cases gr <;>
    simp_all [clockwiseTasepPair]

/-- Every one-edge predecessor of a target is either the target itself or the
explicit directed reverse source at a rising `01` edge.  This is the actual
function-space interpretation of the local column weights. -/
theorem clockwiseTasep_localStep_preimage_cases
    (ring : DirectedRing n) (hn : 1 < n)
    (F G : Fin n -> Bool) (edge : Fin n)
    (hstep : localStep ring clockwiseTasepPair F edge = G) :
    F = G \/
      (tasepRising01Test ring G edge = true /\
        F = tasepReverseSourceAt ring G edge) := by
  let j := ring.rightNeighbor edge
  have hje : j ≠ edge :=
    rightNeighbor_ne_self_of_one_lt ring hn edge
  have hedge := congrFun hstep edge
  have hj := congrFun hstep j
  have hpair : clockwiseTasepPair (F edge) (F j) =
      (G edge, G j) := by
    apply Prod.ext
    · simpa [localStep, j] using hedge
    · simpa [localStep, j, hje] using hj
  rcases clockwiseTasepPair_preimage_cases
      (F edge) (F j) (G edge) (G j) hpair with hsame | hmove
  · left
    funext i
    by_cases hie : i = edge
    · subst i
      exact hsame.1
    · by_cases hij : i = j
      · subst i
        exact hsame.2
      · have hi := congrFun hstep i
        simpa [localStep, j, hie, hij] using hi
  · right
    have hrising : tasepRising01Test ring G edge = true := by
      simp [tasepRising01Test, j, hmove.1, hmove.2.1]
    refine ⟨hrising, ?_⟩
    funext i
    by_cases hie : i = edge
    · subst i
      simp [tasepReverseSourceAt, hmove.2.2.1]
    · by_cases hij : i = j
      · subst i
        simp [tasepReverseSourceAt, j, hje, hmove.2.2.2]
      · have hi := congrFun hstep i
        have hFG : F i = G i := by
          simpa [localStep, j, hie, hij] using hi
        simpa [tasepReverseSourceAt, j, hie, hij] using hFG

/-- The explicit reverse source is active in the required clockwise
orientation. -/
theorem tasepReverseSourceAt_active10
    (ring : DirectedRing n) (hn : 1 < n)
    (G : Fin n -> Bool) (edge : Fin n) :
    tasepActive10Test ring (tasepReverseSourceAt ring G edge) edge =
      true := by
  have hje := rightNeighbor_ne_self_of_one_lt ring hn edge
  simp [tasepActive10Test, tasepReverseSourceAt, hje]

/-- A rising target `01` is reached exactly in the directed `10 -> 01`
orientation from the explicit reverse source. -/
theorem clockwiseTasep_reverseSource_localStep_of_rising
    (ring : DirectedRing n) (hn : 1 < n)
    (G : Fin n -> Bool) (edge : Fin n)
    (hrising : tasepRising01Test ring G edge = true) :
    localStep ring clockwiseTasepPair
      (tasepReverseSourceAt ring G edge) edge = G := by
  let j := ring.rightNeighbor edge
  have hje : j ≠ edge :=
    rightNeighbor_ne_self_of_one_lt ring hn edge
  have hleft : G edge = false := by
    simpa [tasepRising01Test] using
      (Bool.and_eq_true_iff.mp hrising).1
  have hright : G j = true := by
    simpa [tasepRising01Test, j] using
      (Bool.and_eq_true_iff.mp hrising).2
  funext i
  by_cases hie : i = edge
  · subst i
    simp [localStep, clockwiseTasepPair, tasepReverseSourceAt,
      j, hje, hleft]
  · by_cases hij : i = j
    · subst i
      simp [localStep, clockwiseTasepPair, tasepReverseSourceAt,
        j, hje, hright]
    · simp [localStep, clockwiseTasepPair, tasepReverseSourceAt,
        j, hje, hie, hij]

/-- Every nontrivial symmetric adjacent swap has one of the two exact
clockwise-TASEP orientations. -/
theorem nontrivial_swapFrontConfigAt_directed_orientation
    (ring : DirectedRing n) (hn : 1 < n)
    (F : Fin n -> Bool) (edge : Fin n)
    (hne : F edge ≠ F (ring.rightNeighbor edge)) :
    (localStep ring clockwiseTasepPair F edge =
        swapFrontConfigAt ring F edge) \/
      (localStep ring clockwiseTasepPair
        (swapFrontConfigAt ring F edge) edge = F) := by
  cases hleft : F edge <;>
    cases hright : F (ring.rightNeighbor edge)
  · exact False.elim (hne (by simp [hleft, hright]))
  · right
    have hrising : tasepRising01Test ring F edge = true := by
      simp [tasepRising01Test, hleft, hright]
    rw [swapFrontConfigAt_eq_tasepReverseSourceAt_of_rising
      ring hn F edge hrising]
    exact clockwiseTasep_reverseSource_localStep_of_rising
      ring hn F edge hrising
  · left
    apply clockwiseTasep_localStep_eq_swapFrontConfigAt_of_active
      ring hn F edge
    simp [tasepActive10Test, hleft, hright]
  · exact False.elim (hne (by simp [hleft, hright]))

/-- Two configurations related by a nontrivial adjacent swap are immediate
neighbors in one of the two directed orientations. -/
theorem eq_swapFrontConfigAt_implies_directed_neighbor
    (ring : DirectedRing n) (hn : 1 < n)
    (F G : Fin n -> Bool) (edge : Fin n)
    (hG : G = swapFrontConfigAt ring F edge)
    (hne : F edge ≠ F (ring.rightNeighbor edge)) :
    localStep ring clockwiseTasepPair F edge = G \/
      localStep ring clockwiseTasepPair G edge = F := by
  subst G
  exact nontrivial_swapFrontConfigAt_directed_orientation
    ring hn F edge hne

/-- A nontrivial symmetric adjacent swap stays inside the same front-mass
slice, proved through whichever directed TASEP orientation is active. -/
theorem frontConfigMass_swapFrontConfigAt_of_endpoint_ne
    (ring : DirectedRing n) (hn : 1 < n)
    (F : Fin n -> Bool) (edge : Fin n)
    (hne : F edge ≠ F (ring.rightNeighbor edge)) :
    frontConfigMass (swapFrontConfigAt ring F edge) =
      frontConfigMass F := by
  rcases nontrivial_swapFrontConfigAt_directed_orientation
      ring hn F edge hne with hforward | hreverse
  · have hmass := frontConfigMass_clockwiseTasep_localStep
      ring hn F edge
    rw [hforward] at hmass
    exact hmass
  · have hmass := frontConfigMass_clockwiseTasep_localStep
      ring hn (swapFrontConfigAt ring F edge) edge
    rw [hreverse] at hmass
    exact hmass.symm

/-- A one-edge self-loop cannot have been an active `10 -> 01` move. -/
theorem tasepActive10Test_eq_false_of_localStep_eq_self
    (ring : DirectedRing n)
    (F : Fin n -> Bool) (edge : Fin n)
    (hself : localStep ring clockwiseTasepPair F edge = F) :
    tasepActive10Test ring F edge = false := by
  cases hactive : tasepActive10Test ring F edge with
  | false => rfl
  | true =>
      have hleft : F edge = true := by
        simpa [tasepActive10Test] using
          (Bool.and_eq_true_iff.mp hactive).1
      have hright : F (ring.rightNeighbor edge) = false := by
        simpa [tasepActive10Test] using
          (Bool.and_eq_true_iff.mp hactive).2
      have hedge := congrFun hself edge
      simp [localStep, clockwiseTasepPair, hleft, hright] at hedge

/-- Exact fixed-edge predecessor characterization.  Thus the local column
contains one predecessor on `00` and `11`, none on `10`, and the two distinct
forms on `01`; no state-space enumeration premise is hidden here. -/
theorem clockwiseTasep_localStep_eq_iff_predecessor_forms
    (ring : DirectedRing n) (hn : 1 < n)
    (F G : Fin n -> Bool) (edge : Fin n) :
    localStep ring clockwiseTasepPair F edge = G ↔
      ((tasepActive10Test ring G edge = false /\ F = G) \/
        (tasepRising01Test ring G edge = true /\
          F = tasepReverseSourceAt ring G edge)) := by
  constructor
  · intro hstep
    rcases clockwiseTasep_localStep_preimage_cases
        ring hn F G edge hstep with hsame | hreverse
    · left
      subst F
      exact ⟨tasepActive10Test_eq_false_of_localStep_eq_self
        ring G edge hstep, rfl⟩
    · exact Or.inr hreverse
  · rintro (⟨hinactive, hFG⟩ | ⟨hrising, hFG⟩)
    · rw [hFG]
      exact clockwiseTasep_localStep_eq_self_of_inactive
        ring hn G edge hinactive
    · rw [hFG]
      exact clockwiseTasep_reverseSource_localStep_of_rising
        ring hn G edge hrising

/-- Explicit local predecessor list for one target edge. -/
noncomputable def tasepColumnPredecessorsAt
    (ring : DirectedRing n) (G : Fin n -> Bool) (edge : Fin n) :
    List (Fin n -> Bool) := by
  classical
  exact if tasepActive10Test ring G edge then []
    else if tasepRising01Test ring G edge then
      [G, tasepReverseSourceAt ring G edge]
    else [G]

/-- The explicit local predecessor list has exactly the numeric truth-table
weight used in the cyclic column sum. -/
theorem tasepColumnPredecessorsAt_length
    (ring : DirectedRing n) (G : Fin n -> Bool) (edge : Fin n) :
    (tasepColumnPredecessorsAt ring G edge).length =
      tasepColumnWeightAt ring G edge := by
  classical
  cases hleft : G edge <;>
    cases hright : G (ring.rightNeighbor edge) <;>
      simp [tasepColumnPredecessorsAt, tasepColumnWeightAt,
        tasepActive10Test, tasepRising01Test, hleft, hright]

/-- Membership in the local predecessor list is exactly the one-edge TASEP
preimage relation. -/
theorem mem_tasepColumnPredecessorsAt_iff
    (ring : DirectedRing n) (hn : 1 < n)
    (F G : Fin n -> Bool) (edge : Fin n) :
    F ∈ tasepColumnPredecessorsAt ring G edge ↔
      localStep ring clockwiseTasepPair F edge = G := by
  classical
  rw [clockwiseTasep_localStep_eq_iff_predecessor_forms
    ring hn F G edge]
  cases hleft : G edge <;>
    cases hright : G (ring.rightNeighbor edge) <;>
      simp [tasepColumnPredecessorsAt, tasepActive10Test,
        tasepRising01Test, hleft, hright]

/-- On a rising target edge the reverse source differs at the initiator. -/
theorem tasepReverseSourceAt_ne_of_rising
    (ring : DirectedRing n) (G : Fin n -> Bool) (edge : Fin n)
    (hrising : tasepRising01Test ring G edge = true) :
    tasepReverseSourceAt ring G edge ≠ G := by
  intro heq
  have hedge := congrFun heq edge
  have hleft : G edge = false := by
    simpa [tasepRising01Test] using
      (Bool.and_eq_true_iff.mp hrising).1
  simp [tasepReverseSourceAt, hleft] at hedge

/-- No local predecessor is duplicated in the explicit list. -/
theorem tasepColumnPredecessorsAt_nodup
    (ring : DirectedRing n) (G : Fin n -> Bool) (edge : Fin n) :
    (tasepColumnPredecessorsAt ring G edge).Nodup := by
  classical
  cases hactive : tasepActive10Test ring G edge with
  | true => simp [tasepColumnPredecessorsAt, hactive]
  | false =>
      cases hrising : tasepRising01Test ring G edge with
      | false => simp [tasepColumnPredecessorsAt, hactive, hrising]
      | true =>
          have hne := tasepReverseSourceAt_ne_of_rising
            ring G edge hrising
          simp [tasepColumnPredecessorsAt, hactive, hrising, hne.symm]

private theorem tasepNodup_map_of_injective
    {alpha beta : Type} {xs : List alpha}
    (hxs : xs.Nodup) (f : alpha -> beta) (hf : Function.Injective f) :
    (xs.map f).Nodup := by
  exact List.Pairwise.map f (fun _ _ hne => hf.ne hne) hxs

private theorem tasepNodup_ofFn_of_injective
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
        obtain ⟨i, hi⟩ := hmem
        have h := hf hi
        cases h
      · apply ih
        intro i j hij
        exact Fin.succ_inj.mp (hf hij)

private theorem tasepNodup_flatMap_of_nodup
    {alpha beta : Type} (xs : List alpha) (f : alpha -> List beta)
    (hxs : xs.Nodup)
    (hfn : forall x, x ∈ xs -> (f x).Nodup)
    (hdisjoint : forall x, x ∈ xs -> forall y, y ∈ xs -> x ≠ y ->
      forall a, a ∈ f x -> forall b, b ∈ f y -> a ≠ b) :
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

/-- Explicit list of all scheduler pairs `(source configuration, edge)` in
the column over target `G`. -/
noncomputable def tasepColumnPredecessorPairs
    (ring : DirectedRing n) (G : Fin n -> Bool) :
    List ((Fin n -> Bool) × Fin n) := by
  classical
  exact (List.ofFn (fun edge : Fin n => edge)).flatMap
    (fun edge => (tasepColumnPredecessorsAt ring G edge).map
      (fun F => (F, edge)))

/-- The explicit fixed-target scheduler column has exactly `n` entries. -/
theorem tasepColumnPredecessorPairs_length
    (ring : DirectedRing n) (G : Fin n -> Bool) :
    (tasepColumnPredecessorPairs ring G).length = n := by
  classical
  unfold tasepColumnPredecessorPairs
  simp only [List.length_flatMap, List.map_ofFn, List.length_map]
  change (List.ofFn (fun edge : Fin n =>
    (tasepColumnPredecessorsAt ring G edge).length)).sum = n
  rw [show
    (List.ofFn (fun edge : Fin n =>
      (tasepColumnPredecessorsAt ring G edge).length)).sum =
        (List.ofFn (fun edge : Fin n =>
          tasepColumnWeightAt ring G edge)).sum from
      tasepSum_ofFn_eq _ _
        (fun edge => tasepColumnPredecessorsAt_length ring G edge)]
  exact tasepColumnWeight_sum_eq_card ring G

/-- Membership in the explicit column list is the exact scheduler transition
relation, with the selected edge retained in the pair. -/
theorem mem_tasepColumnPredecessorPairs_iff
    (ring : DirectedRing n) (hn : 1 < n)
    (F G : Fin n -> Bool) (edge : Fin n) :
    (F, edge) ∈ tasepColumnPredecessorPairs ring G ↔
      localStep ring clockwiseTasepPair F edge = G := by
  classical
  unfold tasepColumnPredecessorPairs
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨other, _hother, hmem⟩
    rw [List.mem_map] at hmem
    obtain ⟨source, hsource, hp⟩ := hmem
    have hedgeEq : other = edge := congrArg Prod.snd hp
    subst other
    have hsourceEq : source = F := congrArg Prod.fst hp
    subst source
    exact (mem_tasepColumnPredecessorsAt_iff
      ring hn F G edge).mp hsource
  · intro hstep
    refine ⟨edge, List.mem_ofFn.mpr ⟨edge, rfl⟩, ?_⟩
    rw [List.mem_map]
    exact ⟨F, (mem_tasepColumnPredecessorsAt_iff
      ring hn F G edge).mpr hstep, rfl⟩

/-- Every entry of the exact target column lies in the same front-mass slice
as the target. -/
theorem frontConfigMass_eq_of_mem_tasepColumnPredecessorPairs
    (ring : DirectedRing n) (hn : 1 < n)
    (F G : Fin n -> Bool) (edge : Fin n)
    (hmem : (F, edge) ∈ tasepColumnPredecessorPairs ring G) :
    frontConfigMass F = frontConfigMass G := by
  have hstep := (mem_tasepColumnPredecessorPairs_iff
    ring hn F G edge).mp hmem
  have hmass := frontConfigMass_clockwiseTasep_localStep ring hn F edge
  rw [hstep] at hmass
  exact hmass.symm

/-- The column list is multiplicity-free: distinct outer edges have distinct
second components, and each local predecessor list is itself duplicate-free. -/
theorem tasepColumnPredecessorPairs_nodup
    (ring : DirectedRing n) (G : Fin n -> Bool) :
    (tasepColumnPredecessorPairs ring G).Nodup := by
  classical
  unfold tasepColumnPredecessorPairs
  apply tasepNodup_flatMap_of_nodup
  · exact tasepNodup_ofFn_of_injective
      (fun edge : Fin n => edge) (fun _ _ h => h)
  · intro edge _hedge
    apply tasepNodup_map_of_injective
      (tasepColumnPredecessorsAt_nodup ring G edge)
    intro F H hpair
    exact congrArg Prod.fst hpair
  · intro edge _hedge other _hother hne a ha b hb
    rw [List.mem_map] at ha hb
    obtain ⟨F, _hF, rfl⟩ := ha
    obtain ⟨H, _hH, rfl⟩ := hb
    intro hpair
    exact hne (congrArg Prod.snd hpair)

/-! ## One-step fixed-slice kernel assembly -/

/-- Every source configuration in the fixed-mass slice paired with each of
the `n` scheduler edges. -/
def tasepSliceSchedulerPairs (m k : Nat) :
    List ((Fin m -> Bool) × Fin m) :=
  (tasepFrontConfigSlice m k).flatMap (fun F =>
    List.ofFn (fun edge : Fin m => (F, edge)))

/-- Row-pair membership remembers exactly the fixed-slice source. -/
theorem mem_tasepSliceSchedulerPairs_iff
    {m k : Nat} (F : Fin m -> Bool) (edge : Fin m) :
    (F, edge) ∈ tasepSliceSchedulerPairs m k ↔
      F ∈ tasepFrontConfigSlice m k := by
  unfold tasepSliceSchedulerPairs
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨source, hsource, hpair⟩
    rw [List.mem_ofFn] at hpair
    obtain ⟨other, hp⟩ := hpair
    have hsourceEq : source = F := congrArg Prod.fst hp
    subst source
    exact hsource
  · intro hsource
    exact ⟨F, hsource, List.mem_ofFn.mpr ⟨edge, rfl⟩⟩

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

/-- The global list of slice scheduler rows has no duplicate `(source, edge)`
pairs. -/
theorem tasepSliceSchedulerPairs_nodup (m k : Nat) :
    (tasepSliceSchedulerPairs m k).Nodup := by
  classical
  unfold tasepSliceSchedulerPairs
  apply tasepNodup_flatMap_of_nodup
  · exact tasepFrontConfigSlice_nodup m k
  · intro F _hF
    apply tasepNodup_ofFn_of_injective
    intro edge other hp
    exact congrArg Prod.snd hp
  · intro F _hF G _hG hFG a ha b hb
    rw [List.mem_ofFn] at ha hb
    obtain ⟨edge, rfl⟩ := ha
    obtain ⟨other, rfl⟩ := hb
    intro hp
    exact hFG (congrArg Prod.fst hp)

/-- The part of the fixed-slice row table whose one-step endpoint is `G`. -/
def tasepSliceIncomingPairs
    (ring : DirectedRing n) (k : Nat) (G : Fin n -> Bool) :
    List ((Fin n -> Bool) × Fin n) :=
  (tasepSliceSchedulerPairs n k).filter (fun p =>
    decide (localStep ring clockwiseTasepPair p.1 p.2 = G))

theorem mem_tasepSliceIncomingPairs_iff
    (ring : DirectedRing n) (k : Nat)
    (F G : Fin n -> Bool) (edge : Fin n) :
    (F, edge) ∈ tasepSliceIncomingPairs ring k G ↔
      F ∈ tasepFrontConfigSlice n k /\
        localStep ring clockwiseTasepPair F edge = G := by
  simp [tasepSliceIncomingPairs,
    mem_tasepSliceSchedulerPairs_iff]

theorem tasepSliceIncomingPairs_nodup
    (ring : DirectedRing n) (k : Nat) (G : Fin n -> Bool) :
    (tasepSliceIncomingPairs ring k G).Nodup := by
  unfold tasepSliceIncomingPairs
  exact tasepConfigNodup_filter_of_nodup _ _
    (tasepSliceSchedulerPairs_nodup n k)

/-- If the target has mass `k`, every member of its exact unrestricted column
is already a fixed-slice scheduler row. -/
theorem tasepColumnPredecessorPairs_source_mem_slice
    (ring : DirectedRing n) (hn : 1 < n) (k : Nat)
    (F G : Fin n -> Bool) (edge : Fin n)
    (hG : G ∈ tasepFrontConfigSlice n k)
    (hcol : (F, edge) ∈ tasepColumnPredecessorPairs ring G) :
    F ∈ tasepFrontConfigSlice n k := by
  rw [mem_tasepFrontConfigSlice_iff] at hG ⊢
  exact (frontConfigMass_eq_of_mem_tasepColumnPredecessorPairs
    ring hn F G edge hcol).trans hG

/-- On a fixed-mass target, the filtered row table and the explicit target
column have exactly the same members. -/
theorem mem_tasepSliceIncomingPairs_iff_mem_column
    (ring : DirectedRing n) (hn : 1 < n) (k : Nat)
    (F G : Fin n -> Bool) (edge : Fin n)
    (hG : G ∈ tasepFrontConfigSlice n k) :
    (F, edge) ∈ tasepSliceIncomingPairs ring k G ↔
      (F, edge) ∈ tasepColumnPredecessorPairs ring G := by
  constructor
  · intro hin
    have hstep := (mem_tasepSliceIncomingPairs_iff
      ring k F G edge).mp hin
    exact (mem_tasepColumnPredecessorPairs_iff
      ring hn F G edge).mpr hstep.2
  · intro hcol
    apply (mem_tasepSliceIncomingPairs_iff
      ring k F G edge).mpr
    exact ⟨tasepColumnPredecessorPairs_source_mem_slice
      ring hn k F G edge hG hcol,
      (mem_tasepColumnPredecessorPairs_iff
        ring hn F G edge).mp hcol⟩

/-- Exact list-level one-step double stochasticity: each target in the
fixed-mass slice has exactly `n` incoming scheduler pairs. -/
theorem tasepSliceIncomingPairs_length
    (ring : DirectedRing n) (hn : 1 < n) (k : Nat)
    (G : Fin n -> Bool)
    (hG : G ∈ tasepFrontConfigSlice n k) :
    (tasepSliceIncomingPairs ring k G).length = n := by
  classical
  have hperm : List.Perm (tasepSliceIncomingPairs ring k G)
      (tasepColumnPredecessorPairs ring G) := by
    apply (List.perm_ext_iff_of_nodup
      (tasepSliceIncomingPairs_nodup ring k G)
      (tasepColumnPredecessorPairs_nodup ring G)).2
    intro p
    rcases p with ⟨F, edge⟩
    exact mem_tasepSliceIncomingPairs_iff_mem_column
      ring hn k F G edge hG
  exact hperm.length_eq.trans
    (tasepColumnPredecessorPairs_length ring G)

/-! ## Exact iterated target columns -/

/-- Backward enumeration of every length-`t` scheduler history ending at a
fixed target.  Each recursive layer chooses one entry of the exact one-step
target column and records the chosen edge at the end of the schedule. -/
noncomputable def tasepBackwardHistories
    (ring : DirectedRing n) :
    (t : Nat) -> (Fin n -> Bool) ->
      List ((Fin n -> Bool) × DetSchedule n)
  | 0, G => [(G, [])]
  | t + 1, G =>
      (tasepColumnPredecessorPairs ring G).flatMap (fun p =>
        (tasepBackwardHistories ring t p.1).map (fun h =>
          (h.1, h.2 ++ [p.2])))

/-- The exact length-`t` target column has `n^t` scheduler histories.  This is
the iterated, denominator-cleared column-stochasticity statement. -/
theorem tasepBackwardHistories_length
    (ring : DirectedRing n) (t : Nat) (G : Fin n -> Bool) :
    (tasepBackwardHistories ring t G).length = n ^ t := by
  induction t generalizing G with
  | zero => rfl
  | succ t ih =>
      simp only [tasepBackwardHistories, List.length_flatMap,
        List.length_map, ih]
      rw [tasepSum_map_const,
        tasepColumnPredecessorPairs_length, Nat.pow_succ]
      exact Nat.mul_comm _ _

/-- Every enumerated backward history has exactly the advertised horizon and
executes to its named target. -/
theorem mem_tasepBackwardHistories_sound
    (ring : DirectedRing n) (hn : 1 < n)
    (t : Nat) (G start : Fin n -> Bool) (word : DetSchedule n)
    (hmem : (start, word) ∈ tasepBackwardHistories ring t G) :
    word.length = t /\
      runLocalSchedule ring clockwiseTasepPair start word = G := by
  induction t generalizing G start word with
  | zero =>
      have hp : (start, word) = (G, []) := by
        simpa [tasepBackwardHistories] using hmem
      cases hp
      exact ⟨rfl, rfl⟩
  | succ t ih =>
      rw [tasepBackwardHistories, List.mem_flatMap] at hmem
      obtain ⟨p, hpColumn, hpMap⟩ := hmem
      rw [List.mem_map] at hpMap
      obtain ⟨h, hh, hp⟩ := hpMap
      rcases p with ⟨middle, edge⟩
      rcases h with ⟨source, pre⟩
      have hstart : source = start := congrArg Prod.fst hp
      have hword : pre ++ [edge] = word := congrArg Prod.snd hp
      subst start
      subst word
      have hpre := ih middle source pre hh
      have hstep :
          localStep ring clockwiseTasepPair middle edge = G :=
        (mem_tasepColumnPredecessorPairs_iff
          ring hn middle G edge).mp hpColumn
      constructor
      · simp [hpre.1]
      · rw [PPLLSchedulerBlocks.runLocalSchedule_append]
        simp only [runLocalSchedule]
        rw [hpre.2]
        exact hstep

/-- Conversely, every typed length-`t` schedule whose endpoint is `G` occurs
in the explicit backward column. -/
theorem mem_tasepBackwardHistories_of_length_endpoint
    (ring : DirectedRing n) (hn : 1 < n)
    (t : Nat) (G start : Fin n -> Bool) (word : DetSchedule n)
    (hlen : word.length = t)
    (hend : runLocalSchedule ring clockwiseTasepPair start word = G) :
    (start, word) ∈ tasepBackwardHistories ring t G := by
  induction t generalizing G start word with
  | zero =>
      have hnil : word = [] := List.eq_nil_of_length_eq_zero hlen
      subst word
      simp only [runLocalSchedule] at hend
      subst G
      simp [tasepBackwardHistories]
  | succ t ih =>
      have hne : word ≠ [] := by
        intro heq
        subst word
        simp at hlen
      let pre := word.dropLast
      let edge := word.getLast hne
      have hword : pre ++ [edge] = word :=
        List.dropLast_concat_getLast hne
      have hpreLength : pre.length = t := by
        simp only [pre, List.length_dropLast, hlen]
        omega
      let middle :=
        runLocalSchedule ring clockwiseTasepPair start pre
      have hstep :
          localStep ring clockwiseTasepPair middle edge = G := by
        rw [← hword, PPLLSchedulerBlocks.runLocalSchedule_append] at hend
        simpa only [middle, runLocalSchedule] using hend
      have hpColumn :
          (middle, edge) ∈ tasepColumnPredecessorPairs ring G :=
        (mem_tasepColumnPredecessorPairs_iff
          ring hn middle G edge).mpr hstep
      have hpPre :
          (start, pre) ∈ tasepBackwardHistories ring t middle :=
        ih middle start pre hpreLength rfl
      rw [tasepBackwardHistories, List.mem_flatMap]
      refine ⟨(middle, edge), hpColumn, ?_⟩
      rw [List.mem_map]
      exact ⟨(start, pre), hpPre, by simp only [hword]⟩

/-- Exact membership characterization of an iterated target column. -/
theorem mem_tasepBackwardHistories_iff
    (ring : DirectedRing n) (hn : 1 < n)
    (t : Nat) (G start : Fin n -> Bool) (word : DetSchedule n) :
    (start, word) ∈ tasepBackwardHistories ring t G ↔
      word.length = t /\
        runLocalSchedule ring clockwiseTasepPair start word = G := by
  constructor
  · exact mem_tasepBackwardHistories_sound
      ring hn t G start word
  · rintro ⟨hlen, hend⟩
    exact mem_tasepBackwardHistories_of_length_endpoint
      ring hn t G start word hlen hend

/-- The schedule component of every backward history is one of the uniform
length-`t` scheduler words. -/
theorem schedule_mem_allSchedules_of_mem_tasepBackwardHistories
    (ring : DirectedRing n) (hn : 1 < n)
    (t : Nat) (G start : Fin n -> Bool) (word : DetSchedule n)
    (hmem : (start, word) ∈ tasepBackwardHistories ring t G) :
    word ∈ allSchedules n t := by
  exact mem_allSchedules_of_length n t word
    (mem_tasepBackwardHistories_sound
      ring hn t G start word hmem).1

/-- Iterated backward columns never leave the target's front-mass slice. -/
theorem frontConfigMass_eq_of_mem_tasepBackwardHistories
    (ring : DirectedRing n) (hn : 1 < n)
    (t : Nat) (G start : Fin n -> Bool) (word : DetSchedule n)
    (hmem : (start, word) ∈ tasepBackwardHistories ring t G) :
    frontConfigMass start = frontConfigMass G := by
  have hend := (mem_tasepBackwardHistories_sound
    ring hn t G start word hmem).2
  have hmass := frontConfigMass_runLocalSchedule_clockwiseTasep
    ring hn start word
  rw [hend] at hmass
  exact hmass.symm

/-- The iterated target-column enumeration is multiplicity-free.  The last
recorded edge identifies the outer one-step column entry, while the common
prefix endpoint identifies its predecessor configuration. -/
theorem tasepBackwardHistories_nodup
    (ring : DirectedRing n) (hn : 1 < n)
    (t : Nat) (G : Fin n -> Bool) :
    (tasepBackwardHistories ring t G).Nodup := by
  classical
  induction t generalizing G with
  | zero => simp [tasepBackwardHistories]
  | succ t ih =>
      rw [tasepBackwardHistories]
      apply tasepNodup_flatMap_of_nodup
      · exact tasepColumnPredecessorPairs_nodup ring G
      · intro p hp
        apply tasepNodup_map_of_injective (ih p.1)
        intro a b hab
        rcases p with ⟨middle, edge⟩
        rcases a with ⟨source, pre⟩
        rcases b with ⟨other, rest⟩
        apply Prod.ext
        · simpa using congrArg Prod.fst hab
        · have hsched : pre ++ [edge] = rest ++ [edge] := by
            simpa using congrArg Prod.snd hab
          exact List.append_cancel_right hsched
      · intro p hp q hq hpq a ha b hb
        rw [List.mem_map] at ha hb
        obtain ⟨ha0, hha, hmapa⟩ := ha
        obtain ⟨hb0, hhb, hmapb⟩ := hb
        rcases p with ⟨middle, edge⟩
        rcases q with ⟨other, otherEdge⟩
        rcases ha0 with ⟨source, pre⟩
        rcases hb0 with ⟨otherSource, rest⟩
        intro hab
        have hmapped :
            (source, pre ++ [edge]) =
              (otherSource, rest ++ [otherEdge]) :=
          hmapa.trans (hab.trans hmapb.symm)
        have hsource : source = otherSource :=
          congrArg Prod.fst hmapped
        have hsched : pre ++ [edge] = rest ++ [otherEdge] :=
          congrArg Prod.snd hmapped
        have hpreSound := mem_tasepBackwardHistories_sound
          ring hn t middle source pre hha
        have hrestSound := mem_tasepBackwardHistories_sound
          ring hn t other otherSource rest hhb
        have hpre : pre = rest := by
          apply List.append_inj_left hsched
          rw [hpreSound.1, hrestSound.1]
        have hedge : edge = otherEdge := by
          subst rest
          exact List.singleton_inj.mp (List.append_cancel_left hsched)
        have hmiddle : middle = other := by
          subst otherSource
          subst rest
          exact hpreSound.2.symm.trans hrestSound.2
        exact hpq (Prod.ext hmiddle hedge)

/-! ## Iterated fixed-slice kernel assembly -/

/-- Every source of a backward history ending in the `k`-slice is itself in
that slice. -/
theorem tasepBackwardHistories_source_mem_slice
    (ring : DirectedRing n) (hn : 1 < n) (k t : Nat)
    (G start : Fin n -> Bool) (word : DetSchedule n)
    (hG : G ∈ tasepFrontConfigSlice n k)
    (hmem : (start, word) ∈ tasepBackwardHistories ring t G) :
    start ∈ tasepFrontConfigSlice n k := by
  rw [mem_tasepFrontConfigSlice_iff] at hG ⊢
  exact (frontConfigMass_eq_of_mem_tasepBackwardHistories
    ring hn t G start word hmem).trans hG

/-- Cartesian row table of every source in a fixed mass slice and every
uniform length-`t` scheduler word. -/
def tasepSliceSchedulerHistories (m k t : Nat) :
    List ((Fin m -> Bool) × DetSchedule m) :=
  (tasepFrontConfigSlice m k).flatMap (fun F =>
    (allSchedules m t).map (fun word => (F, word)))

/-- Membership in the iterated row table is exactly fixed source mass together
with a typed uniform scheduler word. -/
theorem mem_tasepSliceSchedulerHistories_iff
    {m k t : Nat} (F : Fin m -> Bool) (word : DetSchedule m) :
    (F, word) ∈ tasepSliceSchedulerHistories m k t ↔
      F ∈ tasepFrontConfigSlice m k /\ word ∈ allSchedules m t := by
  unfold tasepSliceSchedulerHistories
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨source, hsource, hpair⟩
    rw [List.mem_map] at hpair
    obtain ⟨otherWord, hotherWord, hp⟩ := hpair
    have hsourceEq : source = F := congrArg Prod.fst hp
    have hwordEq : otherWord = word := congrArg Prod.snd hp
    subst source
    subst otherWord
    exact ⟨hsource, hotherWord⟩
  · rintro ⟨hF, hword⟩
    refine ⟨F, hF, ?_⟩
    rw [List.mem_map]
    exact ⟨word, hword, rfl⟩

/-- The full iterated row table has no duplicate `(source, schedule)` entries. -/
theorem tasepSliceSchedulerHistories_nodup (m k t : Nat) :
    (tasepSliceSchedulerHistories m k t).Nodup := by
  classical
  unfold tasepSliceSchedulerHistories
  apply tasepNodup_flatMap_of_nodup
  · exact tasepFrontConfigSlice_nodup m k
  · intro F _hF
    apply tasepNodup_map_of_injective
      (PPartialSealSweepReadySuffixHalfMassSol.allSchedules_nodup m t)
    intro word other hp
    exact congrArg Prod.snd hp
  · intro F _hF G _hG hFG a ha b hb
    rw [List.mem_map] at ha hb
    obtain ⟨word, _hword, rfl⟩ := ha
    obtain ⟨otherWord, _hotherWord, rfl⟩ := hb
    intro hp
    exact hFG (congrArg Prod.fst hp)

/-- The portion of the iterated fixed-slice row table whose endpoint is `G`. -/
def tasepSliceIncomingHistories
    (ring : DirectedRing n) (k t : Nat) (G : Fin n -> Bool) :
    List ((Fin n -> Bool) × DetSchedule n) :=
  (tasepSliceSchedulerHistories n k t).filter (fun p =>
    decide (runLocalSchedule ring clockwiseTasepPair p.1 p.2 = G))

/-- Exact membership theorem for the filtered iterated target column. -/
theorem mem_tasepSliceIncomingHistories_iff
    (ring : DirectedRing n) (k t : Nat)
    (F G : Fin n -> Bool) (word : DetSchedule n) :
    (F, word) ∈ tasepSliceIncomingHistories ring k t G ↔
      F ∈ tasepFrontConfigSlice n k /\
        word ∈ allSchedules n t /\
          runLocalSchedule ring clockwiseTasepPair F word = G := by
  simp [tasepSliceIncomingHistories,
    mem_tasepSliceSchedulerHistories_iff, and_assoc]

/-- Filtering the duplicate-free row table by endpoint preserves
duplicate-freedom. -/
theorem tasepSliceIncomingHistories_nodup
    (ring : DirectedRing n) (k t : Nat) (G : Fin n -> Bool) :
    (tasepSliceIncomingHistories ring k t G).Nodup := by
  unfold tasepSliceIncomingHistories
  exact tasepConfigNodup_filter_of_nodup _ _
    (tasepSliceSchedulerHistories_nodup n k t)

/-- For a target in the fixed slice, the filtered row table and the recursive
backward column enumerate exactly the same `(source, schedule)` histories. -/
theorem tasepSliceIncomingHistories_perm_backwardHistories
    (ring : DirectedRing n) (hn : 1 < n) (k t : Nat)
    (G : Fin n -> Bool)
    (hG : G ∈ tasepFrontConfigSlice n k) :
    List.Perm (tasepSliceIncomingHistories ring k t G)
      (tasepBackwardHistories ring t G) := by
  classical
  apply (List.perm_ext_iff_of_nodup
    (tasepSliceIncomingHistories_nodup ring k t G)
    (tasepBackwardHistories_nodup ring hn t G)).2
  intro p
  rcases p with ⟨F, word⟩
  constructor
  · intro hin
    have h := (mem_tasepSliceIncomingHistories_iff
      ring k t F G word).mp hin
    exact (mem_tasepBackwardHistories_iff
      ring hn t G F word).mpr
        ⟨allSchedules_schedule_length n t word h.2.1, h.2.2⟩
  · intro hback
    have h := (mem_tasepBackwardHistories_iff
      ring hn t G F word).mp hback
    exact (mem_tasepSliceIncomingHistories_iff
      ring k t F G word).mpr
        ⟨tasepBackwardHistories_source_mem_slice
          ring hn k t G F word hG hback,
          schedule_mem_allSchedules_of_mem_tasepBackwardHistories
            ring hn t G F word hback,
          h.2⟩

/-- Exact iterated double stochasticity on every fixed-front-mass slice: each
target has exactly `n^t` incoming uniform scheduler histories. -/
theorem tasepSliceIncomingHistories_length
    (ring : DirectedRing n) (hn : 1 < n) (k t : Nat)
    (G : Fin n -> Bool)
    (hG : G ∈ tasepFrontConfigSlice n k) :
    (tasepSliceIncomingHistories ring k t G).length = n ^ t := by
  exact (tasepSliceIncomingHistories_perm_backwardHistories
    ring hn k t G hG).length_eq.trans
      (tasepBackwardHistories_length ring t G)

/-! ## Exact stationary endpoint aggregate -/

/-- Fixed-mass function configurations whose exact `List.ofFn` encoding has
the canonical first two coordinates occupied. -/
def tasepCanonicalMarkedFrontConfigSlice (m k : Nat) :
    List (Fin m -> Bool) :=
  (tasepFrontConfigSlice m k).filter (fun F =>
    frontWordHasCanonicalMarkedPair (frontConfigWord F))

/-- The canonical marked function slice realizes the existing marked word
count exactly. -/
theorem tasepCanonicalMarkedFrontConfigSlice_length_eq_wordCount
    (m k : Nat) :
    (tasepCanonicalMarkedFrontConfigSlice m k).length =
      markedPairWordCount m k := by
  unfold tasepCanonicalMarkedFrontConfigSlice
  rw [← List.countP_eq_length_filter]
  unfold tasepFrontConfigSlice
  rw [tasepCountP_filter_eq_countP_and]
  rw [markedPairWordCount_eq_countP_canonical]
  rw [← tasepAllFrontConfigs_map_frontConfigWord m, List.countP_map]
  apply congrArg (fun p => (tasepAllFrontConfigs m).countP p)
  funext F
  simp only [Function.comp_apply]
  rw [frontWordMass_frontConfigWord]

theorem mem_tasepCanonicalMarkedFrontConfigSlice_iff
    {m k : Nat} (F : Fin m -> Bool) :
    F ∈ tasepCanonicalMarkedFrontConfigSlice m k ↔
      F ∈ tasepFrontConfigSlice m k /\
        frontWordHasCanonicalMarkedPair (frontConfigWord F) = true := by
  simp [tasepCanonicalMarkedFrontConfigSlice]

theorem tasepCanonicalMarkedFrontConfigSlice_nodup (m k : Nat) :
    (tasepCanonicalMarkedFrontConfigSlice m k).Nodup := by
  unfold tasepCanonicalMarkedFrontConfigSlice
  exact tasepConfigNodup_filter_of_nodup _ _
    (tasepFrontConfigSlice_nodup m k)

/-- The duplicate-free list of fixed-slice configurations carrying the marked
`11` event on a selected directed edge. -/
noncomputable def tasepMarkedFrontConfigSlice
    (ring : DirectedRing n) (k : Nat) (edge : Fin n) :
    List (Fin n -> Bool) :=
  (tasepFrontConfigSlice n k).filter
    (tasepMarked11EndpointTest ring edge)

theorem mem_tasepMarkedFrontConfigSlice_iff
    (ring : DirectedRing n) (k : Nat) (edge : Fin n)
    (G : Fin n -> Bool) :
    G ∈ tasepMarkedFrontConfigSlice ring k edge ↔
      G ∈ tasepFrontConfigSlice n k /\
        tasepMarked11EndpointTest ring edge G = true := by
  simp [tasepMarkedFrontConfigSlice]

theorem tasepMarkedFrontConfigSlice_nodup
    (ring : DirectedRing n) (k : Nat) (edge : Fin n) :
    (tasepMarkedFrontConfigSlice ring k edge).Nodup := by
  unfold tasepMarkedFrontConfigSlice
  exact tasepConfigNodup_filter_of_nodup _ _
    (tasepFrontConfigSlice_nodup n k)

theorem tasepMarkedFrontConfigSlice_map_rotate_perm_canonical
    (ring : DirectedRing n) (hn : 2 <= n)
    (k : Nat) (edge : Fin n) :
    List.Perm
      ((tasepMarkedFrontConfigSlice ring k edge).map
        (rotateFrontConfigFrom ring edge))
      (tasepCanonicalMarkedFrontConfigSlice n k) := by
  classical
  have hleftNodup :
      ((tasepMarkedFrontConfigSlice ring k edge).map
        (rotateFrontConfigFrom ring edge)).Nodup := by
    apply tasepNodup_map_of_injective
      (tasepMarkedFrontConfigSlice_nodup ring k edge)
    exact (rotateFrontConfigFrom_bijective ring edge).1
  apply (List.perm_ext_iff_of_nodup hleftNodup
    (tasepCanonicalMarkedFrontConfigSlice_nodup n k)).2
  intro D
  rw [List.mem_map]
  constructor
  · rintro ⟨C, hC, rfl⟩
    have hc := (mem_tasepMarkedFrontConfigSlice_iff
      ring k edge C).1 hC
    have hmass : frontConfigMass C = k :=
      (mem_tasepFrontConfigSlice_iff
        (m := n) (k := k) C).1 hc.1
    have hmark : FrontConfigMarkedEdge ring C edge :=
      (tasepMarked11EndpointTest_spec ring edge C).1 hc.2
    refine (mem_tasepCanonicalMarkedFrontConfigSlice_iff
      (m := n) (k := k)
      (rotateFrontConfigFrom ring edge C)).2 ?_
    constructor
    · refine (mem_tasepFrontConfigSlice_iff
        (m := n) (k := k)
        (rotateFrontConfigFrom ring edge C)).2 ?_
      rw [frontConfigMass_rotateFrontConfigFrom]
      exact hmass
    · apply (frontConfigWord_hasCanonicalMarkedPair_iff hn
        (rotateFrontConfigFrom ring edge C)).2
      exact (rotateFrontConfigFrom_canonicalMarkedPair_iff
        ring hn edge C).2 hmark
  · intro hD
    let C := unrotateFrontConfigFrom ring edge D
    have hrotate : rotateFrontConfigFrom ring edge C = D := by
      simp [C]
    have hd := (mem_tasepCanonicalMarkedFrontConfigSlice_iff
      (m := n) (k := k) D).1 hD
    have hmassD : frontConfigMass D = k :=
      (mem_tasepFrontConfigSlice_iff
        (m := n) (k := k) D).1 hd.1
    have hcanonicalD : FrontConfigCanonicalMarkedPair hn D :=
      (frontConfigWord_hasCanonicalMarkedPair_iff hn D).1 hd.2
    have hmassRotate := frontConfigMass_rotateFrontConfigFrom ring edge C
    rw [hrotate] at hmassRotate
    have hmassC : frontConfigMass C = k :=
      hmassRotate.symm.trans hmassD
    have hcanonicalRotate :
        FrontConfigCanonicalMarkedPair hn
          (rotateFrontConfigFrom ring edge C) := by
      simpa only [hrotate] using hcanonicalD
    have hmarkC : FrontConfigMarkedEdge ring C edge :=
      (rotateFrontConfigFrom_canonicalMarkedPair_iff
        ring hn edge C).1 hcanonicalRotate
    refine ⟨C, ?_, hrotate⟩
    exact (mem_tasepMarkedFrontConfigSlice_iff
      ring k edge C).2
        ⟨(mem_tasepFrontConfigSlice_iff
            (m := n) (k := k) C).2 hmassC,
          (tasepMarked11EndpointTest_spec ring edge C).2 hmarkC⟩

/-- The arbitrary-edge marked function slice has exactly the existing
canonical marked-word cardinality. -/
theorem tasepMarkedFrontConfigSlice_length_eq_wordCount
    (ring : DirectedRing n) (hn : 2 <= n)
    (k : Nat) (edge : Fin n) :
    (tasepMarkedFrontConfigSlice ring k edge).length =
      markedPairWordCount n k := by
  have hlen := (tasepMarkedFrontConfigSlice_map_rotate_perm_canonical
    ring hn k edge).length_eq
  rw [List.length_map,
    tasepCanonicalMarkedFrontConfigSlice_length_eq_wordCount] at hlen
  exact hlen

/-- Exact arbitrary-edge stationary normalization on the concrete function
slice. -/
theorem tasepFrontConfigSlice_length_le_square_mul_marked_length
    (ring : DirectedRing n) (hn : 3 <= n)
    (k : Nat) (hk : 2 <= k) (hkn : k < n) (edge : Fin n) :
    (tasepFrontConfigSlice n k).length <=
      n ^ 2 * (tasepMarkedFrontConfigSlice ring k edge).length := by
  rw [tasepFrontConfigSlice_length_eq_wordCount,
    tasepMarkedFrontConfigSlice_length_eq_wordCount ring (by omega)]
  exact frontSliceWordCount_le_square_mul_markedPairWordCount
    n k hn hk hkn

/-- Disjoint union of the exact incoming scheduler histories over every
marked target in the fixed slice. -/
noncomputable def tasepMarkedSliceIncomingHistories
    (ring : DirectedRing n) (k t : Nat) (edge : Fin n) :
    List ((Fin n -> Bool) × DetSchedule n) := by
  classical
  exact (tasepMarkedFrontConfigSlice ring k edge).flatMap (fun G =>
    tasepSliceIncomingHistories ring k t G)

/-- Incoming histories associated with distinct target configurations are
disjoint because deterministic execution has a unique endpoint. -/
theorem tasepMarkedSliceIncomingHistories_nodup
    (ring : DirectedRing n) (k t : Nat) (edge : Fin n) :
    (tasepMarkedSliceIncomingHistories ring k t edge).Nodup := by
  classical
  unfold tasepMarkedSliceIncomingHistories
  apply tasepNodup_flatMap_of_nodup
  · exact tasepMarkedFrontConfigSlice_nodup ring k edge
  · intro G _hG
    exact tasepSliceIncomingHistories_nodup ring k t G
  · intro G _hG H _hH hGH a ha b hb
    intro hab
    subst b
    rcases a with ⟨F, word⟩
    have haEnd := (mem_tasepSliceIncomingHistories_iff
      ring k t F G word).mp ha
    have hbEnd := (mem_tasepSliceIncomingHistories_iff
      ring k t F H word).mp hb
    exact hGH (haEnd.2.2.symm.trans hbEnd.2.2)

/-- The marked-target aggregate contains exactly `markedTargets * n^t`
scheduler histories.  This is uniform stationarity as an integer list identity,
not yet a pointwise mixing bound for any selected source. -/
theorem tasepMarkedSliceIncomingHistories_length
    (ring : DirectedRing n) (hn : 1 < n)
    (k t : Nat) (edge : Fin n) :
    (tasepMarkedSliceIncomingHistories ring k t edge).length =
      (tasepMarkedFrontConfigSlice ring k edge).length * n ^ t := by
  unfold tasepMarkedSliceIncomingHistories
  simp only [List.length_flatMap]
  rw [show
    (tasepMarkedFrontConfigSlice ring k edge).map (fun G =>
      (tasepSliceIncomingHistories ring k t G).length) =
      (tasepMarkedFrontConfigSlice ring k edge).map
        (fun _ => n ^ t) by
          apply List.map_congr_left
          intro G hG
          exact tasepSliceIncomingHistories_length
            ring hn k t G
              ((mem_tasepMarkedFrontConfigSlice_iff
                ring k edge G).mp hG).1]
  exact tasepSum_map_const
    (tasepMarkedFrontConfigSlice ring k edge) (n ^ t)

/-- The same marked endpoint event, now filtered directly from the fixed-slice
row table. -/
noncomputable def tasepSliceMarkedEndpointHistories
    (ring : DirectedRing n) (k t : Nat) (edge : Fin n) :
    List ((Fin n -> Bool) × DetSchedule n) := by
  classical
  exact (tasepSliceSchedulerHistories n k t).filter (fun p =>
    tasepMarked11EndpointTest ring edge
      (runLocalSchedule ring clockwiseTasepPair p.1 p.2))

theorem mem_tasepSliceMarkedEndpointHistories_iff
    (ring : DirectedRing n) (k t : Nat) (edge : Fin n)
    (F : Fin n -> Bool) (word : DetSchedule n) :
    (F, word) ∈ tasepSliceMarkedEndpointHistories ring k t edge ↔
      F ∈ tasepFrontConfigSlice n k /\
        word ∈ allSchedules n t /\
          tasepMarked11EndpointTest ring edge
            (runLocalSchedule ring clockwiseTasepPair F word) = true := by
  simp [tasepSliceMarkedEndpointHistories,
    mem_tasepSliceSchedulerHistories_iff, and_assoc]

theorem tasepSliceMarkedEndpointHistories_nodup
    (ring : DirectedRing n) (k t : Nat) (edge : Fin n) :
    (tasepSliceMarkedEndpointHistories ring k t edge).Nodup := by
  unfold tasepSliceMarkedEndpointHistories
  exact tasepConfigNodup_filter_of_nodup _ _
    (tasepSliceSchedulerHistories_nodup n k t)

theorem tasepSliceMarkedEndpointHistories_perm_incoming
    (ring : DirectedRing n) (hn : 1 < n)
    (k t : Nat) (edge : Fin n) :
    List.Perm (tasepSliceMarkedEndpointHistories ring k t edge)
      (tasepMarkedSliceIncomingHistories ring k t edge) := by
  classical
  apply (List.perm_ext_iff_of_nodup
    (tasepSliceMarkedEndpointHistories_nodup ring k t edge)
    (tasepMarkedSliceIncomingHistories_nodup ring k t edge)).2
  intro p
  rcases p with ⟨F, word⟩
  constructor
  · intro hrow
    have h := (mem_tasepSliceMarkedEndpointHistories_iff
      ring k t edge F word).1 hrow
    let G := runLocalSchedule ring clockwiseTasepPair F word
    have hGmass : frontConfigMass G = k := by
      rw [frontConfigMass_runLocalSchedule_clockwiseTasep
        ring hn F word]
      exact (mem_tasepFrontConfigSlice_iff
        (m := n) (k := k) F).1 h.1
    have hGslice : G ∈ tasepFrontConfigSlice n k :=
      (mem_tasepFrontConfigSlice_iff
        (m := n) (k := k) G).2 hGmass
    have hGmarked : G ∈ tasepMarkedFrontConfigSlice ring k edge :=
      (mem_tasepMarkedFrontConfigSlice_iff ring k edge G).2
        ⟨hGslice, h.2.2⟩
    rw [tasepMarkedSliceIncomingHistories, List.mem_flatMap]
    refine ⟨G, hGmarked, ?_⟩
    exact (mem_tasepSliceIncomingHistories_iff
      ring k t F G word).2 ⟨h.1, h.2.1, rfl⟩
  · intro hagg
    rw [tasepMarkedSliceIncomingHistories, List.mem_flatMap] at hagg
    obtain ⟨G, hG, hin⟩ := hagg
    have hmarked := (mem_tasepMarkedFrontConfigSlice_iff
      ring k edge G).1 hG
    have hi := (mem_tasepSliceIncomingHistories_iff
      ring k t F G word).1 hin
    exact (mem_tasepSliceMarkedEndpointHistories_iff
      ring k t edge F word).2
        ⟨hi.1, hi.2.1, by rw [hi.2.2]; exact hmarked.2⟩

/-- Exact aggregate stationarity of the marked endpoint event at every finite
horizon.  The equality is averaged over all fixed-slice starting states; the
remaining theorem needs a pointwise lower bound for each individual start. -/
theorem tasepSliceMarkedEndpointHistories_length
    (ring : DirectedRing n) (hn : 1 < n)
    (k t : Nat) (edge : Fin n) :
    (tasepSliceMarkedEndpointHistories ring k t edge).length =
      (tasepMarkedFrontConfigSlice ring k edge).length * n ^ t := by
  exact (tasepSliceMarkedEndpointHistories_perm_incoming
    ring hn k t edge).length_eq.trans
      (tasepMarkedSliceIncomingHistories_length ring hn k t edge)

/-- Direct row-table length is the sum of the existing per-source marked
endpoint counts. -/
theorem tasepSliceMarkedEndpointHistories_length_eq_count_sum
    (ring : DirectedRing n) (k t : Nat) (edge : Fin n) :
    (tasepSliceMarkedEndpointHistories ring k t edge).length =
      ((tasepFrontConfigSlice n k).map (fun F =>
        tasepMarked11EndpointCount ring F edge t)).sum := by
  unfold tasepSliceMarkedEndpointHistories
  unfold tasepSliceSchedulerHistories
  rw [tasepLength_filter_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro F _hF
  unfold tasepMarked11EndpointCount
  rw [List.countP_map]
  rfl

/-- Integer stationary-sum identity in the exact endpoint-count vocabulary. -/
theorem tasepMarked11EndpointCount_sum_fixedSlice
    (ring : DirectedRing n) (hn : 1 < n)
    (k t : Nat) (edge : Fin n) :
    ((tasepFrontConfigSlice n k).map (fun F =>
      tasepMarked11EndpointCount ring F edge t)).sum =
      (tasepMarkedFrontConfigSlice ring k edge).length * n ^ t := by
  rw [← tasepSliceMarkedEndpointHistories_length_eq_count_sum]
  exact tasepSliceMarkedEndpointHistories_length ring hn k t edge

/-- Division-free stationary average lower bound.  It controls the sum over
all sources but deliberately does not select an arbitrary source. -/
theorem tasepFixedSlice_average_inverseSquare_markedEndpoint
    (ring : DirectedRing n) (hn : 3 <= n)
    (k : Nat) (hk : 2 <= k) (hkn : k < n)
    (t : Nat) (edge : Fin n) :
    (tasepFrontConfigSlice n k).length * n ^ t <=
      n ^ 2 * ((tasepFrontConfigSlice n k).map (fun F =>
        tasepMarked11EndpointCount ring F edge t)).sum := by
  have hstatic :=
    tasepFrontConfigSlice_length_le_square_mul_marked_length
      ring hn k hk hkn edge
  have hmul := Nat.mul_le_mul_right (n ^ t) hstatic
  calc
    (tasepFrontConfigSlice n k).length * n ^ t <=
        (n ^ 2 * (tasepMarkedFrontConfigSlice ring k edge).length) *
          n ^ t := hmul
    _ = n ^ 2 *
          ((tasepMarkedFrontConfigSlice ring k edge).length * n ^ t) := by
      ac_rfl
    _ = n ^ 2 * ((tasepFrontConfigSlice n k).map (fun F =>
          tasepMarked11EndpointCount ring F edge t)).sum := by
      rw [tasepMarked11EndpointCount_sum_fixedSlice
        ring (by omega) k t edge]

/-- The reverse-source witness stays in the same fixed-front slice. -/
theorem frontConfigMass_tasepReverseSourceAt_of_rising
    (ring : DirectedRing n) (hn : 1 < n)
    (G : Fin n -> Bool) (edge : Fin n)
    (hrising : tasepRising01Test ring G edge = true) :
    frontConfigMass (tasepReverseSourceAt ring G edge) =
      frontConfigMass G := by
  have hmass := frontConfigMass_clockwiseTasep_localStep ring hn
    (tasepReverseSourceAt ring G edge) edge
  rw [clockwiseTasep_reverseSource_localStep_of_rising
    ring hn G edge hrising] at hmass
  exact hmass.symm

/-! ## Exact common-successor witnesses -/

/-- Ordered edge pairs whose two one-step TASEP rows have a common successor.
The fixed-slice row/column theorems above prove double stochasticity at the
list level.  A later analytic layer must still identify the normalized
operator and prove a comparison bound before this concrete count can be used
as the numerator of `P P*`.  Its denominator `n^2` is not hidden inside a
rational-valued kernel. -/
noncomputable def tasepCommonSuccessorPairCount
    (ring : DirectedRing n) (F G : Fin n -> Bool) : Nat := by
  classical
  exact (List.ofFn (fun first : Fin n =>
    (List.ofFn (fun second : Fin n =>
      if localStep ring clockwiseTasepPair F first =
          localStep ring clockwiseTasepPair G second
        then 1 else 0)).sum)).sum

theorem tasepCommonSuccessorPairCount_symm
    (ring : DirectedRing n) (F G : Fin n -> Bool) :
    tasepCommonSuccessorPairCount ring F G =
      tasepCommonSuccessorPairCount ring G F := by
  classical
  unfold tasepCommonSuccessorPairCount
  calc
    (List.ofFn (fun first : Fin n =>
        (List.ofFn (fun second : Fin n =>
          if localStep ring clockwiseTasepPair F first =
              localStep ring clockwiseTasepPair G second
            then 1 else 0)).sum)).sum =
        (List.ofFn (fun second : Fin n =>
          (List.ofFn (fun first : Fin n =>
            if localStep ring clockwiseTasepPair F first =
                localStep ring clockwiseTasepPair G second
              then 1 else 0)).sum)).sum :=
      tasepSum_ofFn_sum_comm _
    _ = (List.ofFn (fun second : Fin n =>
          (List.ofFn (fun first : Fin n =>
            if localStep ring clockwiseTasepPair G second =
                localStep ring clockwiseTasepPair F first
              then 1 else 0)).sum)).sum := by
      apply tasepSum_ofFn_eq
      intro second
      apply tasepSum_ofFn_eq
      intro first
      by_cases h : localStep ring clockwiseTasepPair F first =
          localStep ring clockwiseTasepPair G second
      · rw [if_pos h, if_pos h.symm]
      · have hrev : localStep ring clockwiseTasepPair G second ≠
            localStep ring clockwiseTasepPair F first :=
          fun h' => h h'.symm
        rw [if_neg h, if_neg hrev]

private theorem tasepNat_le_sum_of_mem
    {x : Nat} {xs : List Nat} (hx : x ∈ xs) : x <= xs.sum := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · simp
      · have htail := ih hx
        simp only [List.sum_cons]
        omega

theorem tasepStutterEdgeCount_sq_le_commonSuccessorPairCount_self
    (ring : DirectedRing n) (hn : 1 < n)
    (F : Fin n -> Bool) :
    tasepStutterEdgeCount ring F * tasepStutterEdgeCount ring F <=
      tasepCommonSuccessorPairCount ring F F := by
  classical
  let stutter : Fin n -> Nat := fun edge =>
    if tasepActive10Test ring F edge then 0 else 1
  let common : Fin n -> Fin n -> Nat := fun first second =>
    if localStep ring clockwiseTasepPair F first =
        localStep ring clockwiseTasepPair F second then 1 else 0
  have hpoint : forall first second : Fin n,
      stutter first * stutter second <= common first second := by
    intro first second
    cases hfirst : tasepActive10Test ring F first with
    | true => simp [stutter, hfirst]
    | false =>
        cases hsecond : tasepActive10Test ring F second with
        | true => simp [stutter, hsecond]
        | false =>
            have hselfFirst :=
              clockwiseTasep_localStep_eq_self_of_inactive
                ring hn F first hfirst
            have hselfSecond :=
              clockwiseTasep_localStep_eq_self_of_inactive
                ring hn F second hsecond
            have heq : localStep ring clockwiseTasepPair F first =
                localStep ring clockwiseTasepPair F second :=
              hselfFirst.trans hselfSecond.symm
            simp [stutter, common, hfirst, hsecond, heq]
  have hinner : forall first : Fin n,
      (List.ofFn (fun second : Fin n =>
        stutter first * stutter second)).sum <=
      (List.ofFn (fun second : Fin n =>
        common first second)).sum := by
    intro first
    exact tasepSum_ofFn_le _ _ (hpoint first)
  have hdouble := tasepSum_ofFn_le
    (fun first : Fin n =>
      (List.ofFn (fun second : Fin n =>
        stutter first * stutter second)).sum)
    (fun first : Fin n =>
      (List.ofFn (fun second : Fin n =>
        common first second)).sum) hinner
  have hleft :
      (List.ofFn (fun first : Fin n =>
        (List.ofFn (fun second : Fin n =>
          stutter first * stutter second)).sum)).sum =
        (List.ofFn stutter).sum * (List.ofFn stutter).sum := by
    calc
      (List.ofFn (fun first : Fin n =>
          (List.ofFn (fun second : Fin n =>
            stutter first * stutter second)).sum)).sum =
          (List.ofFn (fun first : Fin n =>
            stutter first * (List.ofFn stutter).sum)).sum :=
        tasepSum_ofFn_eq _ _ (fun first =>
          tasepSum_ofFn_mul_left (stutter first) stutter)
      _ = (List.ofFn stutter).sum * (List.ofFn stutter).sum :=
        tasepSum_ofFn_mul_right stutter (List.ofFn stutter).sum
  unfold tasepStutterEdgeCount
  change (List.ofFn stutter).sum * (List.ofFn stutter).sum <=
    tasepCommonSuccessorPairCount ring F F
  calc
    (List.ofFn stutter).sum * (List.ofFn stutter).sum =
        (List.ofFn (fun first : Fin n =>
          (List.ofFn (fun second : Fin n =>
            stutter first * stutter second)).sum)).sum := hleft.symm
    _ <= (List.ofFn (fun first : Fin n =>
          (List.ofFn (fun second : Fin n =>
            common first second)).sum)).sum := hdouble
    _ = tasepCommonSuccessorPairCount ring F F := by
      unfold tasepCommonSuccessorPairCount
      rfl

/-- Half-laziness gives a denominator-cleared diagonal lower bound for the
common-successor double count. -/
theorem n_sq_le_four_mul_tasepCommonSuccessorPairCount_self
    (ring : DirectedRing n) (hn : 1 < n)
    (F : Fin n -> Bool) :
    n ^ 2 <= 4 * tasepCommonSuccessorPairCount ring F F := by
  let s := tasepStutterEdgeCount ring F
  have hs : n <= 2 * s := n_le_two_mul_tasepStutterEdgeCount ring F
  have hsquare : n * n <= (2 * s) * (2 * s) :=
    Nat.mul_le_mul hs hs
  have hcommon : s * s <= tasepCommonSuccessorPairCount ring F F :=
    tasepStutterEdgeCount_sq_le_commonSuccessorPairCount_self ring hn F
  calc
    n ^ 2 = n * n := by simp [Nat.pow_two]
    _ <= (2 * s) * (2 * s) := hsquare
    _ = 4 * (s * s) := by ac_rfl
    _ <= 4 * tasepCommonSuccessorPairCount ring F F :=
      Nat.mul_le_mul_left 4 hcommon

/-- If `G` is a one-clock successor of `F`, every stuttering clock of `G`
gives a distinct common-successor witness `(chosen, stutter)`. -/
theorem tasepStutterEdgeCount_le_commonSuccessorPairCount_forward
    (ring : DirectedRing n) (hn : 1 < n)
    (F : Fin n -> Bool) (chosen : Fin n) :
    tasepStutterEdgeCount ring
        (localStep ring clockwiseTasepPair F chosen) <=
      tasepCommonSuccessorPairCount ring F
        (localStep ring clockwiseTasepPair F chosen) := by
  classical
  let G := localStep ring clockwiseTasepPair F chosen
  let inner : Fin n -> Nat := fun first =>
    (List.ofFn (fun second : Fin n =>
      if localStep ring clockwiseTasepPair F first =
          localStep ring clockwiseTasepPair G second
        then 1 else 0)).sum
  have hpoint : forall second : Fin n,
      (if tasepActive10Test ring G second then 0 else 1) <=
        (if localStep ring clockwiseTasepPair F chosen =
            localStep ring clockwiseTasepPair G second
          then 1 else 0) := by
    intro second
    cases hactive : tasepActive10Test ring G second with
    | true => simp [hactive]
    | false =>
        have hself := clockwiseTasep_localStep_eq_self_of_inactive
          ring hn G second hactive
        have heq : localStep ring clockwiseTasepPair F chosen =
            localStep ring clockwiseTasepPair G second := by
          rw [hself]
        simp [hactive, heq]
  have hinner : tasepStutterEdgeCount ring G <= inner chosen := by
    unfold tasepStutterEdgeCount
    dsimp [inner]
    exact tasepSum_ofFn_le _ _ hpoint
  have hchosenMem : inner chosen ∈ List.ofFn inner :=
    List.mem_ofFn.mpr ⟨chosen, rfl⟩
  have houter : inner chosen <= (List.ofFn inner).sum :=
    tasepNat_le_sum_of_mem hchosenMem
  exact Nat.le_trans hinner (by
    unfold tasepCommonSuccessorPairCount
    simpa [inner, G] using houter)

/-- The transposed orientation has equally explicit witnesses: every
stuttering clock of `G = step F chosen` reaches `G`, while `F` reaches `G`
through `chosen`. -/
theorem tasepStutterEdgeCount_le_commonSuccessorPairCount_reverse
    (ring : DirectedRing n) (hn : 1 < n)
    (F : Fin n -> Bool) (chosen : Fin n) :
    tasepStutterEdgeCount ring
        (localStep ring clockwiseTasepPair F chosen) <=
      tasepCommonSuccessorPairCount ring
        (localStep ring clockwiseTasepPair F chosen) F := by
  classical
  let G := localStep ring clockwiseTasepPair F chosen
  let inner : Fin n -> Nat := fun first =>
    (List.ofFn (fun second : Fin n =>
      if localStep ring clockwiseTasepPair G first =
          localStep ring clockwiseTasepPair F second
        then 1 else 0)).sum
  have hpoint : forall first : Fin n,
      (if tasepActive10Test ring G first then 0 else 1) <= inner first := by
    intro first
    cases hactive : tasepActive10Test ring G first with
    | true => simp [hactive, inner]
    | false =>
        have hself := clockwiseTasep_localStep_eq_self_of_inactive
          ring hn G first hactive
        have heq : localStep ring clockwiseTasepPair G first =
            localStep ring clockwiseTasepPair F chosen := by
          rw [hself]
        have hone : 1 <= inner first := by
          dsimp [inner]
          apply tasepNat_le_sum_of_mem
          apply List.mem_ofFn.mpr
          refine ⟨chosen, ?_⟩
          simp [heq]
        simpa [hactive] using hone
  have hsum : tasepStutterEdgeCount ring G <=
      (List.ofFn inner).sum := by
    unfold tasepStutterEdgeCount
    exact tasepSum_ofFn_le _ _ hpoint
  unfold tasepCommonSuccessorPairCount
  simpa [inner, G] using hsum

/-- Forward orientation: an immediate TASEP neighbor has at least `n/2`
ordered common-successor witnesses. -/
theorem n_le_two_mul_tasepCommonSuccessorPairCount_forward
    (ring : DirectedRing n) (hn : 1 < n)
    (F : Fin n -> Bool) (chosen : Fin n) :
    n <= 2 * tasepCommonSuccessorPairCount ring F
      (localStep ring clockwiseTasepPair F chosen) := by
  exact Nat.le_trans
    (n_le_two_mul_tasepStutterEdgeCount ring
      (localStep ring clockwiseTasepPair F chosen))
    (Nat.mul_le_mul_left 2
      (tasepStutterEdgeCount_le_commonSuccessorPairCount_forward
        ring hn F chosen))

/-- Reverse orientation of the same exact common-successor count. -/
theorem n_le_two_mul_tasepCommonSuccessorPairCount_reverse
    (ring : DirectedRing n) (hn : 1 < n)
    (F : Fin n -> Bool) (chosen : Fin n) :
    n <= 2 * tasepCommonSuccessorPairCount ring
      (localStep ring clockwiseTasepPair F chosen) F := by
  exact Nat.le_trans
    (n_le_two_mul_tasepStutterEdgeCount ring
      (localStep ring clockwiseTasepPair F chosen))
    (Nat.mul_le_mul_left 2
      (tasepStutterEdgeCount_le_commonSuccessorPairCount_reverse
        ring hn F chosen))

/-- Every nontrivial symmetric adjacent-swap edge receives the same exact
`n/2` common-successor comparison, regardless of which endpoint is the
clockwise `10` source. -/
theorem n_le_two_mul_tasepCommonSuccessorPairCount_swap
    (ring : DirectedRing n) (hn : 1 < n)
    (F : Fin n -> Bool) (edge : Fin n)
    (hne : F edge ≠ F (ring.rightNeighbor edge)) :
    n <= 2 * tasepCommonSuccessorPairCount ring F
      (swapFrontConfigAt ring F edge) := by
  rcases nontrivial_swapFrontConfigAt_directed_orientation
      ring hn F edge hne with hforward | hreverse
  · simpa only [hforward] using
      n_le_two_mul_tasepCommonSuccessorPairCount_forward
        ring hn F edge
  · simpa only [hreverse] using
      n_le_two_mul_tasepCommonSuccessorPairCount_reverse
        ring hn (swapFrontConfigAt ring F edge) edge

/-! Exact kernel assembly is now closed at the list-relation level.  For every
horizon, the duplicate-free target column has length `n^t`, membership is
equivalent to exact schedule execution, it equals the filtered fixed-slice row
table, and summing the marked columns gives the exact stationary aggregate.
Every nontrivial symmetric adjacent swap is also oriented as one of the two
directed immediate-neighbor cases.  The first unproved implication is now the
analytic pointwise step: a Poincare or moving-particle estimate for the
normalized finite kernel strong enough to turn the stationary aggregate into
an arbitrary-start marked-`11` endpoint lower bound.  No missing implication
is carried as a premise. -/

#print axioms positiveDescendant_frontMass_one_isSafe
#print axioms positiveHomeFront_fullFrontMass_readyOrABHitGate_zero
#print axioms mem_tasepAllFrontConfigs
#print axioms tasepAllFrontConfigs_nodup
#print axioms tasepAllFrontConfigs_map_frontConfigWord
#print axioms mem_tasepFrontConfigSlice_iff
#print axioms tasepFrontConfigSlice_nodup
#print axioms tasepFrontConfigSlice_length_eq_card
#print axioms frontConfigMass_clockwiseTasep_localStep
#print axioms two_mul_tasepActive10EdgeCount_le
#print axioms n_le_two_mul_tasepStutterEdgeCount
#print axioms tasepRising01EdgeCount_eq_active10EdgeCount
#print axioms tasepColumnWeight_sum_eq_card
#print axioms nontrivial_swapFrontConfigAt_directed_orientation
#print axioms frontConfigMass_swapFrontConfigAt_of_endpoint_ne
#print axioms clockwiseTasep_localStep_eq_iff_predecessor_forms
#print axioms tasepColumnPredecessorPairs_length
#print axioms mem_tasepColumnPredecessorPairs_iff
#print axioms tasepColumnPredecessorPairs_nodup
#print axioms frontConfigMass_eq_of_mem_tasepColumnPredecessorPairs
#print axioms mem_tasepSliceSchedulerPairs_iff
#print axioms tasepSliceSchedulerPairs_nodup
#print axioms mem_tasepSliceIncomingPairs_iff
#print axioms tasepSliceIncomingPairs_length
#print axioms tasepBackwardHistories_length
#print axioms mem_tasepBackwardHistories_iff
#print axioms tasepBackwardHistories_nodup
#print axioms tasepSliceIncomingHistories_perm_backwardHistories
#print axioms tasepSliceIncomingHistories_length
#print axioms tasepMarkedFrontConfigSlice_map_rotate_perm_canonical
#print axioms tasepFrontConfigSlice_length_le_square_mul_marked_length
#print axioms tasepMarkedSliceIncomingHistories_length
#print axioms tasepSliceMarkedEndpointHistories_perm_incoming
#print axioms tasepMarked11EndpointCount_sum_fixedSlice
#print axioms tasepFixedSlice_average_inverseSquare_markedEndpoint
#print axioms frontConfigMass_tasepReverseSourceAt_of_rising
#print axioms tasepCommonSuccessorPairCount_symm
#print axioms tasepStutterEdgeCount_sq_le_commonSuccessorPairCount_self
#print axioms n_sq_le_four_mul_tasepCommonSuccessorPairCount_self
#print axioms n_le_two_mul_tasepCommonSuccessorPairCount_forward
#print axioms n_le_two_mul_tasepCommonSuccessorPairCount_reverse
#print axioms n_le_two_mul_tasepCommonSuccessorPairCount_swap

end PPartialSealSweepTasepFiniteTimeSol
end PPLLCompleteMultiLeaderCleanup
