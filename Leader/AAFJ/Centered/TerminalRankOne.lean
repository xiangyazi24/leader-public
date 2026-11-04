import Leader.AAFJ.Centered.TerminalLanding
import Leader.AAFJ.Centered.ComplexityConstants

/-!
# Literal terminal process for centered AAFJ rank one

This module treats every canonical one-barrier configuration with `Phi = 1`.
The stopped transition is the literal centered successor in the successor cut;
it stops exactly on `CanonicalClean` and has no failure branch.  The numerical
certificate is the state-local four-mode rank (clean, dirty-tail refresh,
zero-leader probe front, unique leader), multiplied by the scheduler degree.
-/

namespace AAFJPK
namespace CenteredRenewal
namespace TerminalRankOne

open BarrierAlgebra
open SingleBarrierSanitation
open OneBarrierCleanup
open NoDropLaterShield
open ZeroLeaderTrial
open TerminalLanding
open FiniteUniformStoppingTree

set_option autoImplicit false

/-- Canonical rank-one data retained at every literal endpoint. -/
structure RankOneCut {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (X : Fin n -> State k) : Prop where
  canonical : CanonicalOneBarrier hk ring X
  phiOne : Phi X = 1

private theorem one_le_bitCount_of_true {n : Nat} (bits : Fin n -> Bool)
    (i : Fin n) (hi : bits i = true) : 1 <= bitCount bits := by
  let after : Fin n -> Bool := fun j => if j = i then false else bits j
  have hdrop := bitCount_single_drop bits after i hi (by simp [after]) (by
    intro j hji
    simp [after, hji])
  omega

private theorem two_le_bitCount_of_two_true {n : Nat}
    (bits : Fin n -> Bool) (i j : Fin n) (hi : bits i = true)
    (hj : bits j = true) (hne : j ≠ i) : 2 <= bitCount bits := by
  let after : Fin n -> Bool := fun x => if x = i then false else bits x
  have hafterJ : after j = true := by simp [after, hne, hj]
  have hone := one_le_bitCount_of_true after j hafterJ
  have hdrop := bitCount_single_drop bits after i hi (by simp [after]) (by
    intro x hxi
    simp [after, hxi])
  omega

theorem RankOneCut.leaderCount_le_one
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {X : Fin n -> State k} (R : RankOneCut hk ring X) :
    leaderCount X <= 1 := by
  have hsum : leaderCount X + dangerBit X <= 1 := by
    calc
      leaderCount X + dangerBit X <=
          max 1 (leaderCount X + dangerBit X) := Nat.le_max_right _ _
      _ = 1 := R.phiOne
  omega

theorem RankOneCut.uniqueLeader
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {X : Fin n -> State k} (R : RankOneCut hk ring X)
    {ell : Fin n} (hell : (X ell).leader = true) :
    forall i : Fin n, (X i).leader = true -> i = ell := by
  intro i hi
  by_cases hie : i = ell
  · exact hie
  · have htwo : 2 <= leaderCount X :=
      two_le_bitCount_of_two_true (fun j => (X j).leader)
        ell i hell hi hie
    have hle := R.leaderCount_le_one
    omega

theorem RankOneCut.tailProbe_false_of_leader
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {X : Fin n -> State k} (R : RankOneCut hk ring X)
    (ell : Fin n) (hell : (X ell).leader = true) :
    (X (tailCoord ring)).probe = false := by
  cases hp : (X (tailCoord ring)).probe
  · rfl
  · have hcount : 1 <= leaderCount X :=
      one_le_bitCount_of_true (fun i => (X i).leader) ell hell
    have hdanger : Dangerous X := dangerous_of_tail_probe ring X hp
    have hbit : dangerBit X = 1 := by simp [dangerBit, hdanger]
    have hsum : leaderCount X + dangerBit X <= 1 := by
      calc
        leaderCount X + dangerBit X <=
            max 1 (leaderCount X + dangerBit X) := Nat.le_max_right _ _
        _ = 1 := R.phiOne
    omega

/-- Every literal centered successor remains in the canonical rank-one lane. -/
theorem RankOneCut.successor
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {X : Fin n -> State k} (R : RankOneCut hk ring X)
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n) (edge : Fin n) :
    RankOneCut hk ring (Rank.cutSuccessor hk ring X edge) := by
  have hn2 : 1 < n := by omega
  refine
    { canonical := canonicalOneBarrier_cutSuccessor
        hk ring hn2 X edge hndvd R.canonical
      phiOne := ?_ }
  have hle := Rank.canonical_phi_step_le hk ring hn3 X R.canonical edge
  have hone : 1 <= Phi (Rank.cutSuccessor hk ring X edge) :=
    Nat.le_max_left _ _
  apply Nat.le_antisymm
  · calc
      Phi (Rank.cutSuccessor hk ring X edge) <= Phi X := hle
      _ = 1 := R.phiOne
  · exact hone

/-- A maximum probe exists whenever some probe exists. -/
theorem exists_maxProbeAt {n k : Nat} (X : Fin n -> State k)
    (h : exists i : Fin n, (X i).probe = true) :
    exists m : Fin n, MaxProbeAt X m := by
  induction n with
  | zero =>
      obtain ⟨i, _⟩ := h
      exact Fin.elim0 i
  | succ n ih =>
      by_cases hlast : (X (Fin.last n)).probe = true
      · refine ⟨Fin.last n, hlast, ?_⟩
        intro i _
        exact Nat.le_of_lt_succ i.isLt
      · have hsmall : exists i : Fin n, (X i.castSucc).probe = true := by
          obtain ⟨i, hi⟩ := h
          by_cases hilast : i = Fin.last n
          · subst i
            exact False.elim (hlast hi)
          · have hlt : i.val < n := by
              have hiLt := i.isLt
              have hne : i.val ≠ n := by
                intro hv
                apply hilast
                apply Fin.ext
                exact hv
              omega
            let j : Fin n := ⟨i.val, hlt⟩
            have hcast : j.castSucc = i := by apply Fin.ext; rfl
            exact ⟨j, by simpa [hcast] using hi⟩
        obtain ⟨m, hm⟩ := ih (fun i : Fin n => X i.castSucc) hsmall
        refine ⟨m.castSucc, hm.1, ?_⟩
        intro i hi
        by_cases hilast : i = Fin.last n
        · subst i
          exact False.elim (hlast hi)
        · have hlt : i.val < n := by
            have hiLt := i.isLt
            have hne : i.val ≠ n := by
              intro hv
              apply hilast
              apply Fin.ext
              exact hv
            omega
          let j : Fin n := ⟨i.val, hlt⟩
          have hcast : j.castSucc = i := by apply Fin.ext; rfl
          have hj : (X j.castSucc).probe = true := by simpa [hcast] using hi
          exact hm.2 j hj

/-- Number of current-tail selections needed for the next advance. -/
def phaseNeed (phase : Bool) : Nat := if phase then 1 else 2

/-- Complementary phase credit for the zero-leader probe-front score. -/
def phaseCredit (phase : Bool) : Nat := if phase then 2 else 1

/-- Farthest probe coordinate plus one, with zero reserved for no probes. -/
noncomputable def probeFront {n k : Nat} (X : Fin n -> State k) : Nat :=
  if h : exists i : Fin n, (X i).probe = true then
    (Classical.choose (exists_maxProbeAt X h)).val + 1
  else 0

theorem probeFront_le {n k : Nat} (X : Fin n -> State k) :
    probeFront X <= n := by
  unfold probeFront
  split
  · exact Nat.succ_le_iff.mpr (Classical.choose
      (exists_maxProbeAt X ‹exists i : Fin n, (X i).probe = true›)).isLt
  · omega

theorem probeFront_eq_zero_of_no_probe {n k : Nat}
    (X : Fin n -> State k)
    (h : forall i : Fin n, (X i).probe = false) :
    probeFront X = 0 := by
  simp only [probeFront]
  rw [dif_neg]
  intro hex
  obtain ⟨i, hi⟩ := hex
  rw [h i] at hi
  contradiction

theorem probeFront_eq_of_maxProbeAt {n k : Nat}
    (X : Fin n -> State k) (m : Fin n) (hm : MaxProbeAt X m) :
    probeFront X = m.val + 1 := by
  have hex : exists i : Fin n, (X i).probe = true := ⟨m, hm.1⟩
  rw [probeFront, dif_pos hex]
  let chosen := Classical.choose (exists_maxProbeAt X hex)
  have hc := Classical.choose_spec (exists_maxProbeAt X hex)
  have hcm : chosen.val <= m.val := hm.2 chosen hc.1
  have hmc : m.val <= chosen.val := hc.2 m hm.1
  omega

/-- State-local four-mode terminal rank.  Its branch order is part of the
certificate: done, dirty-tail refresh, unique leader, then zero leader. -/
noncomputable def directRank {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (X : Fin n -> State k) : Nat :=
  if _hclean : exists ell : Fin n, CanonicalClean hk ring X ell then 0
  else if _hbullet : (X (tailCoord ring)).bullet = true then
    4 * n + phaseNeed (X (tailCoord ring)).phase
  else if hleader : exists ell : Fin n, (X ell).leader = true then
    let ell := Classical.choose hleader
    2 * n + 2 +
      if ell = tailCoord ring then 1
      else 2 * ell.val + phaseNeed (X (tailCoord ring)).phase
  else
    2 * (n - probeFront X) + phaseCredit (X (tailCoord ring)).phase

/-- A live node consists only of the literal configuration and its closed
canonical rank-one certificate. -/
structure TerminalState {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) where
  configuration : Fin n -> State k
  rankOne : RankOneCut hk ring configuration
  notClean : ¬ exists ell : Fin n, CanonicalClean hk ring configuration ell

/-- Scheduler-scaled direct rank. -/
noncomputable def terminalPotential {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} : StopNode (TerminalState hk ring) -> Nat
  | .success => 0
  | .failure => 0
  | .active state => n * directRank hk ring state.configuration

/-- Unified literal terminal transition. -/
noncomputable def terminalStep {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (state : TerminalState hk ring) (edge : Fin n) :
    StopNode (TerminalState hk ring) :=
  let D := Rank.cutSuccessor hk ring state.configuration edge
  let RD := state.rankOne.successor hn3 hndvd edge
  if _hclean : exists ell : Fin n, CanonicalClean hk ring D ell then
    .success
  else .active ⟨D, RD, by assumption⟩

/-- Every active child carries the exact literal successor configuration. -/
theorem terminalStep_active_configuration
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (state child : TerminalState hk ring) (edge : Fin n)
    (hactive : terminalStep hn3 hndvd state edge = .active child) :
    child.configuration =
      Rank.cutSuccessor hk ring state.configuration edge := by
  simp only [terminalStep] at hactive
  split at hactive
  · contradiction
  · injection hactive with hchild
    subst child
    rfl

/-- Success is exactly an actual clean witness on the literal child. -/
theorem terminalStep_eq_success_iff
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (state : TerminalState hk ring) (edge : Fin n) :
    terminalStep hn3 hndvd state edge = .success <->
      exists ell : Fin n, CanonicalClean hk ring
        (Rank.cutSuccessor hk ring state.configuration edge) ell := by
  simp [terminalStep]

theorem terminalStep_success_canonicalClean
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (state : TerminalState hk ring) (edge : Fin n)
    (hsuccess : terminalStep hn3 hndvd state edge = .success) :
    exists ell : Fin n, CanonicalClean hk ring
      (Rank.cutSuccessor hk ring state.configuration edge) ell :=
  (terminalStep_eq_success_iff hn3 hndvd state edge).mp hsuccess

/-- No stopped branch can hide mass in the failure constructor. -/
theorem terminalStep_ne_failure
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (state : TerminalState hk ring) (edge : Fin n) :
    terminalStep hn3 hndvd state edge ≠ .failure := by
  by_cases hclean : exists ell : Fin n, CanonicalClean hk ring
      (Rank.cutSuccessor hk ring state.configuration edge) ell
  · simp [terminalStep, hclean]
  · simp [terminalStep, hclean]

/-- Initial node, stopped at time zero precisely when already clean. -/
noncomputable def initialNode
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (X : Fin n -> State k) (R : RankOneCut hk ring X) :
    StopNode (TerminalState hk ring) :=
  if _hclean : exists ell : Fin n, CanonicalClean hk ring X ell then
    .success
  else .active ⟨X, R, by assumption⟩

theorem initialNode_eq_success_iff
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (X : Fin n -> State k) (R : RankOneCut hk ring X) :
    initialNode X R = .success <->
      exists ell : Fin n, CanonicalClean hk ring X ell := by
  simp [initialNode]

theorem initialNode_ne_failure
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (X : Fin n -> State k) (R : RankOneCut hk ring X) :
    initialNode X R ≠ .failure := by
  by_cases hclean : exists ell : Fin n, CanonicalClean hk ring X ell
  · simp [initialNode, hclean]
  · simp [initialNode, hclean]

/-- Strong budget supplied by the direct rank. -/
def dirtyBudget (n : Nat) : Nat := 4 * n * n + 2 * n

theorem directRank_le_four_mul_add_two
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 3 <= n) (X : Fin n -> State k) :
    directRank hk ring X <= 4 * n + 2 := by
  unfold directRank
  split
  · omega
  split
  · cases hphase : (X (tailCoord ring)).phase <;>
      simp [phaseNeed, hphase] <;> omega
  split
  · let ell := Classical.choose
        ‹exists ell : Fin n, (X ell).leader = true›
    change 2 * n + 2 +
        (if ell = tailCoord ring then 1
          else 2 * ell.val + phaseNeed (X (tailCoord ring)).phase) <=
      4 * n + 2
    by_cases helt : ell = tailCoord ring
    · simp [helt]
      omega
    · have hellt := ell.isLt
      have hval : ell.val <= n - 2 := by
        have hne : ell.val ≠ n - 1 := by
          intro hv
          apply helt
          apply Fin.ext
          change ell.val = n - 1
          exact hv
        omega
      cases hphase : (X (tailCoord ring)).phase <;>
        simp [helt, phaseNeed, hphase] <;> omega
  · have hfront := probeFront_le X
    cases hphase : (X (tailCoord ring)).phase <;>
      simp [phaseCredit, hphase] <;> omega

theorem initialNode_potential_le_dirtyBudget
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (X : Fin n -> State k) (R : RankOneCut hk ring X) :
    terminalPotential (initialNode X R) <= dirtyBudget n := by
  by_cases hclean : exists ell : Fin n, CanonicalClean hk ring X ell
  · simp [initialNode, hclean, terminalPotential, dirtyBudget]
  · simp only [initialNode, hclean, dite_false, terminalPotential,
      dirtyBudget]
    have hrank := directRank_le_four_mul_add_two hk ring hn3 X
    have hmul := Nat.mul_le_mul_left n hrank
    calc
      n * directRank hk ring X <= n * (4 * n + 2) := hmul
      _ = 4 * n * n + 2 * n := by
        rw [Nat.mul_add]
        ac_rfl

theorem dirtyBudget_le_terminalBudget (n : Nat) :
    dirtyBudget n <= ComplexityConstants.terminalBudget n := by
  unfold dirtyBudget ComplexityConstants.terminalBudget
  simp only [Nat.pow_two]
  apply Nat.add_le_add
  · calc
      4 * n * n <= 8 * n * n :=
        Nat.mul_le_mul_right n
          (Nat.mul_le_mul_right n (by omega : 4 <= 8))
      _ = 8 * (n * n) := by ac_rfl
  · exact Nat.mul_le_mul_right n (by omega : 2 <= 9)

/-! ## Rank branch equations -/

theorem directRank_eq_refresh
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {X : Fin n -> State k}
    (hclean : ¬ exists ell : Fin n, CanonicalClean hk ring X ell)
    (hbullet : (X (tailCoord ring)).bullet = true) :
    directRank hk ring X =
      4 * n + phaseNeed (X (tailCoord ring)).phase := by
  simp [directRank, hclean, hbullet]

theorem directRank_eq_zero_of_clean
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {X : Fin n -> State k}
    (hclean : exists ell : Fin n, CanonicalClean hk ring X ell) :
    directRank hk ring X = 0 := by
  simp [directRank, hclean]

theorem directRank_eq_one
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {X : Fin n -> State k} (R : RankOneCut hk ring X)
    (hclean : ¬ exists witness : Fin n,
      CanonicalClean hk ring X witness)
    (hbullet : (X (tailCoord ring)).bullet = false)
    (ell : Fin n) (hell : (X ell).leader = true) :
    directRank hk ring X = 2 * n + 2 +
      if ell = tailCoord ring then 1
      else 2 * ell.val + phaseNeed (X (tailCoord ring)).phase := by
  have hleader : exists witness : Fin n, (X witness).leader = true :=
    ⟨ell, hell⟩
  have hchoose : Classical.choose hleader = ell :=
    R.uniqueLeader hell _ (Classical.choose_spec hleader)
  simp [directRank, hclean, hbullet, hleader, hchoose]

theorem directRank_eq_zero
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {X : Fin n -> State k}
    (hclean : ¬ exists witness : Fin n,
      CanonicalClean hk ring X witness)
    (hbullet : (X (tailCoord ring)).bullet = false)
    (hzero : forall i : Fin n, (X i).leader = false) :
    directRank hk ring X =
      2 * (n - probeFront X) +
        phaseCredit (X (tailCoord ring)).phase := by
  have hleader : ¬ exists witness : Fin n, (X witness).leader = true := by
    rintro ⟨i, hi⟩
    rw [hzero i] at hi
    contradiction
  simp [directRank, hclean, hbullet, hleader]

theorem directRank_pos_of_rankOne_notClean
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {X : Fin n -> State k} (R : RankOneCut hk ring X)
    (hclean : ¬ exists ell : Fin n, CanonicalClean hk ring X ell) :
    0 < directRank hk ring X := by
  unfold directRank
  simp only [hclean, dite_false]
  split
  · cases hphase : (X (tailCoord ring)).phase <;>
      simp [phaseNeed]
  split
  · split <;> omega
  · have hfront := probeFront_le X
    cases hphase : (X (tailCoord ring)).phase <;>
      simp [phaseCredit] <;> omega

/-! ## Finite-sum arithmetic -/

private theorem sum_map_const {A : Type} (xs : List A) (c : Nat) :
    (xs.map (fun _ => c)).sum = xs.length * c := by
  induction xs with
  | nil => simp
  | cons _ xs ih =>
      rw [List.map_cons, List.sum_cons, List.length_cons, ih]
      simp only [Nat.succ_mul]
      omega

private theorem pred_mul (m c : Nat) (hm : 0 < m) :
    m * c = c + (m - 1) * c := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  simp [Nat.succ_mul, Nat.add_comm]

private theorem sum_one_exception
    {A : Type} [BEq A] [LawfulBEq A]
    (xs : List A) (a : A) (f : A -> Nat) (c : Nat)
    (hnodup : xs.Nodup) (ha : a ∈ xs)
    (hother : forall z, z ∈ xs -> z ≠ a -> f z = c) :
    (xs.map f).sum = f a + (xs.length - 1) * c := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
      rw [List.nodup_cons] at hnodup
      by_cases hxa : x = a
      · subst x
        have hall : xs.map f = xs.map (fun _ => c) := by
          apply List.map_congr_left
          intro z hz
          exact hother z (by simp [hz]) (by
            intro hza
            subst z
            exact hnodup.1 hz)
        rw [List.map_cons, List.sum_cons, hall, sum_map_const]
        simp
      · have hat : a ∈ xs := by
          rcases List.mem_cons.mp ha with hax | hat
          · exact absurd hax.symm hxa
          · exact hat
        have hi := ih hnodup.2 hat (by
          intro z hz
          exact hother z (by simp [hz]))
        have hx : f x = c := hother x (by simp) hxa
        rw [List.map_cons, List.sum_cons, hx, hi, List.length_cons]
        have hpos : 0 < xs.length :=
          List.length_pos_iff.mpr (List.ne_nil_of_mem hat)
        have hc := pred_mul xs.length c hpos
        have hsub : xs.length + 1 - 1 = xs.length := by omega
        rw [hsub]
        omega

private theorem nodup_ofFn_of_injective {n : Nat} {A : Type}
    (f : Fin n -> A) (hf : Function.Injective f) :
    (List.ofFn f).Nodup := by
  induction n with
  | zero => simp
  | succ n ih =>
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

private theorem nodup_ofFn_fin (n : Nat) :
    (List.ofFn (fun i : Fin n => i)).Nodup :=
  nodup_ofFn_of_injective (fun i : Fin n => i) Function.injective_id

/-- All children are nonincreasing and one named child drops by one. -/
theorem childSum_le_of_one_drop {n r : Nat} (child : Fin n -> Nat)
    (qedge : Fin n) (hall : forall edge, child edge <= r)
    (hdrop : child qedge + 1 <= r) :
    1 + (List.ofFn child).sum <= n * r := by
  let cap : Fin n -> Nat := fun edge =>
    if edge = qedge then r - 1 else r
  have hchild : forall edge, child edge <= cap edge := by
    intro edge
    by_cases he : edge = qedge
    · subst edge
      simp only [cap, if_pos]
      omega
    · simp [cap, he, hall]
  have hsum := ofFn_sum_le child cap hchild
  have hcap := sum_one_exception
    (List.ofFn (fun edge : Fin n => edge)) qedge cap r
    (nodup_ofFn_fin n) (List.mem_ofFn.mpr ⟨qedge, rfl⟩) (by
      intro edge _ he
      simp [cap, he])
  simp only [List.map_ofFn, Function.comp_def, List.length_ofFn,
    cap, if_pos] at hcap
  rw [hcap] at hsum
  have hr : 1 <= r := by omega
  have hnpos : 0 < n := by have := qedge.isLt; omega
  have hmul := pred_mul n r hnpos
  omega

/-- One child drops by two and a distinct child may rise by one. -/
theorem childSum_le_of_compensated_pair {n r : Nat}
    (child : Fin n -> Nat) (pedge qedge : Fin n) (hne : pedge ≠ qedge)
    (hprogress : child pedge + 2 <= r)
    (hbarrier : child qedge <= r + 1)
    (hother : forall edge, edge ≠ pedge -> edge ≠ qedge ->
      child edge <= r) :
    1 + (List.ofFn child).sum <= n * r := by
  let cap : Fin n -> Nat := fun edge =>
    if edge = pedge then r - 2
    else if edge = qedge then r + 1 else r
  have hchild : forall edge, child edge <= cap edge := by
    intro edge
    by_cases hep : edge = pedge
    · subst edge
      simp only [cap, if_pos]
      omega
    · by_cases heq : edge = qedge
      · subst edge
        simp [cap, Ne.symm hne]
        exact hbarrier
      · simp [cap, hep, heq, hother]
  have hsum := ofFn_sum_le child cap hchild
  have hcap := PlusTwoMinusOneFiniteTree.sum_two_exceptions
    (List.ofFn (fun edge : Fin n => edge)) pedge qedge cap r
    (nodup_ofFn_fin n) (List.mem_ofFn.mpr ⟨pedge, rfl⟩)
    (List.mem_ofFn.mpr ⟨qedge, rfl⟩) hne (by
      intro edge _ hep heq
      simp [cap, hep, heq])
  have hqne : qedge ≠ pedge := Ne.symm hne
  simp only [List.map_ofFn, Function.comp_def, List.length_ofFn,
    cap, if_pos, hqne, if_false] at hcap
  rw [hcap] at hsum
  have hr : 2 <= r := by omega
  have hn2 : 2 <= n := by
    have hp := pedge.isLt
    have hq := qedge.isLt
    have hv : pedge.val ≠ qedge.val := by
      intro hv
      apply hne
      exact Fin.ext hv
    omega
  have hn : n = (n - 2) + 2 := by omega
  have hmul : n * r = (n - 2) * r + 2 * r := by
    calc
      n * r = ((n - 2) + 2) * r := congrArg (fun x => x * r) hn
      _ = (n - 2) * r + 2 * r := Nat.add_mul _ _ _
  omega

/-! ## Zero-leader probe-front branch -/

theorem not_clean_of_zero_leaders
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {X : Fin n -> State k}
    (hzero : forall i : Fin n, (X i).leader = false) :
    ¬ exists ell : Fin n, CanonicalClean hk ring X ell := by
  rintro ⟨ell, hclean⟩
  have hleader := hclean.2.1
  rw [hzero ell] at hleader
  contradiction

theorem prepared_directRank_eq
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {X : Fin n -> State k} (S : Prepared hk ring X) :
    directRank hk ring X = 2 * n + 1 - q ring X S.maxProbe := by
  have hclean := not_clean_of_zero_leaders (hk := hk) (ring := ring)
    S.zeroLeaders
  rw [directRank_eq_zero hclean S.tailBullet S.zeroLeaders,
    probeFront_eq_of_maxProbeAt X S.maxProbe S.maxProbeAt]
  have hm := S.maxProbe_le_n_sub_two
  cases hphase : (X (tailCoord ring)).phase <;>
    simp [q, trialPhase, phaseNat, phaseCredit, hphase] <;> omega

theorem restartReady_directRank_eq
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {X : Fin n -> State k} (S : RestartReady hk ring X) :
    directRank hk ring X = 2 * n + 1 := by
  have hclean := not_clean_of_zero_leaders (hk := hk) (ring := ring)
    S.zeroLeaders
  rw [directRank_eq_zero hclean S.tailBullet S.zeroLeaders,
    probeFront_eq_zero_of_no_probe X S.allProbesCleared]
  simp [phaseCredit, S.tailPhase]

theorem tailProbeReady_directRank_eq
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {X : Fin n -> State k} (S : TailProbeReady hk ring X) :
    directRank hk ring X = phaseCredit (X (tailCoord ring)).phase := by
  have hclean := not_clean_of_zero_leaders (hk := hk) (ring := ring)
    S.zeroLeaders
  have hmax : MaxProbeAt X (tailCoord ring) := by
    refine ⟨S.tailProbe, ?_⟩
    intro i _
    change i.val <= n - 1
    have hi := i.isLt
    omega
  rw [directRank_eq_zero hclean S.tailBullet S.zeroLeaders,
    probeFront_eq_of_maxProbeAt X (tailCoord ring) hmax]
  change 2 * (n - (n - 1 + 1)) +
      phaseCredit (X (tailCoord ring)).phase = _
  have hn := ring.hn
  omega

theorem prepared_progress_directRank_drop_two
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    {X : Fin n -> State k} (S : Prepared hk ring X) :
    directRank hk ring
        (trialStep hk ring X (progressEdge S.maxProbe)) + 2 <=
      directRank hk ring X := by
  by_cases htop : S.maxProbe.val = n - 2
  · let D := trialStep hk ring X (progressEdge S.maxProbe)
    have T : TailProbeReady hk ring D :=
      TerminalLanding.Prepared.progress_top_tailProbeReady
        S hn3 hndvd htop
    have hend := S.progress_top_terminal_success hn3 htop
    have hrankD := tailProbeReady_directRank_eq T
    have hrankX := prepared_directRank_eq S
    have hqle := S.q_le_two_n_sub_two
    dsimp only [D] at T hend hrankD
    have htailPhase := hend.2.2.1
    rw [htailPhase] at hrankD
    cases hphase : (X (tailCoord ring)).phase <;>
      simp [phaseCredit, hphase] at hrankD <;>
      simp [q, trialPhase, phaseNat, hphase, htop] at hrankX <;>
      omega
  · have hnonterminal : S.maxProbe.val <= n - 3 := by
      have hle := S.maxProbe_le_n_sub_two
      omega
    let S' := S.progressProofPrepared hn3 hnonterminal
    have hrankD := prepared_directRank_eq S'
    have hrankX := prepared_directRank_eq S
    have hq := S.q_progress_add_two hn3 hnonterminal
    have hqle := S.q_le_two_n_sub_two
    change directRank hk ring
        (trialStep hk ring X (progressEdge S.maxProbe)) =
      2 * n + 1 - q ring
        (trialStep hk ring X (progressEdge S.maxProbe))
        (ring.rightNeighbor S.maxProbe) at hrankD
    omega

theorem prepared_barrier_directRank_le_add_one
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) {X : Fin n -> State k}
    (S : Prepared hk ring X) :
    directRank hk ring (trialStep hk ring X (barrierEdge ring)) <=
      directRank hk ring X + 1 := by
  have hrankX := prepared_directRank_eq S
  cases hphase : (X (barrierEdge ring)).phase with
  | false =>
      let S' := S.phaseZeroProofPrepared hn3 hphase
      have hrankD := prepared_directRank_eq S'
      have hq := S.q_barrier_phase_zero_sub_one hn3 hphase
      change directRank hk ring
          (trialStep hk ring X (barrierEdge ring)) =
        2 * n + 1 - q ring
          (trialStep hk ring X (barrierEdge ring)) S.maxProbe at hrankD
      omega
  | true =>
      by_cases hzero : S.maxProbe.val = 0
      · let F := S.barrier_phase_one_zero_restartReady hn3 hphase hzero
        have hrankD := restartReady_directRank_eq F
        have hterminal :=
          S.barrier_phase_one_zero_terminal_failure hn3 hphase hzero
        omega
      · have hpos : 0 < S.maxProbe.val := by omega
        let S' := S.phaseOneProofPrepared hn3 hphase hpos
        have hrankD := prepared_directRank_eq S'
        have hq := S.q_barrier_phase_one_sub_one hn3 hphase hpos
        change directRank hk ring
            (trialStep hk ring X (barrierEdge ring)) =
          2 * n + 1 - q ring
            (trialStep hk ring X (barrierEdge ring))
            (ring.leftNeighbor S.maxProbe) at hrankD
        omega

theorem prepared_other_directRank_eq
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) {X : Fin n -> State k}
    (S : Prepared hk ring X) (edge : Fin n)
    (hP : edge ≠ progressEdge S.maxProbe)
    (hQ : edge ≠ barrierEdge ring) :
    directRank hk ring (trialStep hk ring X edge) =
      directRank hk ring X := by
  let S' := S.otherProofPrepared hn3 edge hP hQ
  have hrankD := prepared_directRank_eq S'
  have hrankX := prepared_directRank_eq S
  have hq := S.q_other hn3 edge hP hQ
  change directRank hk ring (trialStep hk ring X edge) =
    2 * n + 1 - q ring (trialStep hk ring X edge) S.maxProbe at hrankD
  omega

theorem prepared_directRank_childSum
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    {X : Fin n -> State k} (S : Prepared hk ring X) :
    1 + (List.ofFn (fun edge : Fin n =>
      directRank hk ring (Rank.cutSuccessor hk ring X edge))).sum <=
      n * directRank hk ring X := by
  apply childSum_le_of_compensated_pair
    (fun edge : Fin n =>
      directRank hk ring (Rank.cutSuccessor hk ring X edge))
    (progressEdge S.maxProbe) (barrierEdge ring) S.progress_ne_barrier
  · exact prepared_progress_directRank_drop_two hn3 hndvd S
  · exact prepared_barrier_directRank_le_add_one hn3 S
  · intro edge hP hQ
    exact Nat.le_of_eq (prepared_other_directRank_eq hn3 S edge hP hQ)

theorem restartReady_barrier_directRank_drop_one
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) {X : Fin n -> State k}
    (S : RestartReady hk ring X) :
    directRank hk ring
        (trialStep hk ring X (barrierEdge ring)) + 1 =
      directRank hk ring X := by
  let P := S.restartPrepared hn3
  have hrankD := prepared_directRank_eq P
  have hrankX := restartReady_directRank_eq S
  have hq := S.q_restartPrepared hn3
  dsimp only at hq
  change q ring (trialStep hk ring X (barrierEdge ring)) P.maxProbe = 1 at hq
  omega

theorem restartReady_directRank_childSum
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) {X : Fin n -> State k}
    (S : RestartReady hk ring X) :
    1 + (List.ofFn (fun edge : Fin n =>
      directRank hk ring (Rank.cutSuccessor hk ring X edge))).sum <=
      n * directRank hk ring X := by
  apply childSum_le_of_one_drop
    (fun edge : Fin n =>
      directRank hk ring (Rank.cutSuccessor hk ring X edge))
    (barrierEdge ring)
  · intro edge
    by_cases he : edge = barrierEdge ring
    · subst edge
      have hdrop := restartReady_barrier_directRank_drop_one hn3 S
      change directRank hk ring
          (trialStep hk ring X (barrierEdge ring)) <=
        directRank hk ring X
      omega
    · have S' := S.otherRestartReady hn3 edge he
      change directRank hk ring (trialStep hk ring X edge) <=
        directRank hk ring X
      rw [restartReady_directRank_eq S', restartReady_directRank_eq S]
      exact Nat.le_refl _
  · exact Nat.le_of_eq (restartReady_barrier_directRank_drop_one hn3 S)

/-! ## Ordinary-tail framing -/

theorem RankOneCut.cutSuccessor_eq_raw_of_ne_barrier
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {X : Fin n -> State k} (R : RankOneCut hk ring X)
    (edge : Fin n) (he : edge ≠ barrierEdge ring) :
    Rank.cutSuccessor hk ring X edge = rawStep hk ring X edge := by
  have hnot : ¬ CenteredRenewal.AdvanceReady hk ring X edge := by
    intro hready
    have het : edge = tailCoord ring := (R.canonical edge).1 hready.1
    exact he (by simpa [barrierEdge] using het)
  unfold Rank.cutSuccessor rawStep
  simp only [hnot, if_false]
  rfl

private theorem nonBarrierStep_responder_phase {k : Nat}
    (u v : State k) : (nonBarrierStep u v).2.phase = v.phase := by
  cases hl : v.leader <;> cases hb : v.bullet <;>
    cases hp : u.probe <;> simp [nonBarrierStep, hl, hb, hp]

private theorem nonBarrierStep_responder_bullet_false {k : Nat}
    (u v : State k) (hbullet : v.bullet = false) :
    (nonBarrierStep u v).2.bullet = false := by
  cases hl : v.leader <;> cases hp : u.probe <;>
    simp [nonBarrierStep, hl, hbullet, hp]

private theorem nonBarrierStep_responder_probe_true {k : Nat}
    (u v : State k) (hprobe : v.probe = true) :
    (nonBarrierStep u v).2.probe = true := by
  cases hl : v.leader <;> cases hb : v.bullet <;>
    cases hp : u.probe <;> simp [nonBarrierStep, hl, hb, hp, hprobe]

theorem ordinary_tail_phase
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {X : Fin n -> State k} (R : RankOneCut hk ring X)
    (hn3 : 3 <= n) (edge : Fin n) (he : edge ≠ barrierEdge ring) :
    ((Rank.cutSuccessor hk ring X edge) (tailCoord ring)).phase =
      (X (tailCoord ring)).phase := by
  have hn2 : 1 < n := by omega
  rw [R.cutSuccessor_eq_raw_of_ne_barrier edge he]
  have hte : tailCoord ring ≠ edge := by
    intro h
    exact he (by simpa [barrierEdge] using h.symm)
  by_cases htr : tailCoord ring = ring.rightNeighbor edge
  · rw [htr, rawStep_at_responder hk ring hn2 X edge]
    have hnon : ¬ IsBarrier hk (X edge)
        (X (ring.rightNeighbor edge)) := by
      intro hb
      have het := (R.canonical edge).1 hb
      exact he (by simpa [barrierEdge] using het)
    rw [CenteredRenewal.transition_of_nonbarrier hk _ _ hnon]
    exact nonBarrierStep_responder_phase _ _
  · rw [rawStep_frame hk ring X edge (tailCoord ring) hte htr]

theorem ordinary_tail_bullet_false
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {X : Fin n -> State k} (R : RankOneCut hk ring X)
    (hn3 : 3 <= n) (edge : Fin n) (he : edge ≠ barrierEdge ring)
    (hbullet : (X (tailCoord ring)).bullet = false) :
    ((Rank.cutSuccessor hk ring X edge) (tailCoord ring)).bullet = false := by
  have hn2 : 1 < n := by omega
  rw [R.cutSuccessor_eq_raw_of_ne_barrier edge he]
  have hte : tailCoord ring ≠ edge := by
    intro h
    exact he (by simpa [barrierEdge] using h.symm)
  by_cases htr : tailCoord ring = ring.rightNeighbor edge
  · rw [htr, rawStep_at_responder hk ring hn2 X edge]
    have hnon : ¬ IsBarrier hk (X edge)
        (X (ring.rightNeighbor edge)) := by
      intro hb
      have het := (R.canonical edge).1 hb
      exact he (by simpa [barrierEdge] using het)
    rw [CenteredRenewal.transition_of_nonbarrier hk _ _ hnon]
    apply nonBarrierStep_responder_bullet_false
    simpa [htr] using hbullet
  · rw [rawStep_frame hk ring X edge (tailCoord ring) hte htr]
    exact hbullet

theorem ordinary_tail_probe_true
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {X : Fin n -> State k} (R : RankOneCut hk ring X)
    (hn3 : 3 <= n) (edge : Fin n) (he : edge ≠ barrierEdge ring)
    (hprobe : (X (tailCoord ring)).probe = true) :
    ((Rank.cutSuccessor hk ring X edge) (tailCoord ring)).probe = true := by
  have hn2 : 1 < n := by omega
  rw [R.cutSuccessor_eq_raw_of_ne_barrier edge he]
  have hte : tailCoord ring ≠ edge := by
    intro h
    exact he (by simpa [barrierEdge] using h.symm)
  by_cases htr : tailCoord ring = ring.rightNeighbor edge
  · rw [htr, rawStep_at_responder hk ring hn2 X edge]
    have hnon : ¬ IsBarrier hk (X edge)
        (X (ring.rightNeighbor edge)) := by
      intro hb
      have het := (R.canonical edge).1 hb
      exact he (by simpa [barrierEdge] using het)
    rw [CenteredRenewal.transition_of_nonbarrier hk _ _ hnon]
    apply nonBarrierStep_responder_probe_true
    simpa [htr] using hprobe
  · rw [rawStep_frame hk ring X edge (tailCoord ring) hte htr]
    exact hprobe

theorem ordinary_zero_leaders
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {X : Fin n -> State k} (R : RankOneCut hk ring X)
    (hn3 : 3 <= n) (edge : Fin n) (he : edge ≠ barrierEdge ring)
    (hzero : forall i : Fin n, (X i).leader = false) :
    forall i : Fin n,
      ((Rank.cutSuccessor hk ring X edge) i).leader = false := by
  have hn2 : 1 < n := by omega
  rw [R.cutSuccessor_eq_raw_of_ne_barrier edge he]
  have hnon : ¬ IsBarrier hk (X edge)
      (X (ring.rightNeighbor edge)) := by
    intro hb
    have het := (R.canonical edge).1 hb
    exact he (by simpa [barrierEdge] using het)
  intro i
  cases hi : (rawStep hk ring X edge i).leader
  · rfl
  · have hold := step_no_leader_birth_of_nonbarrier
      hk ring hn2 X edge hnon i
    have holdTrue := hold hi
    rw [hzero i] at holdTrue
    contradiction

theorem tailProbeReady_other
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    {X : Fin n -> State k} (S : TailProbeReady hk ring X)
    (edge : Fin n) (he : edge ≠ barrierEdge ring) :
    TailProbeReady hk ring (Rank.cutSuccessor hk ring X edge) := by
  let R : RankOneCut hk ring X :=
    { canonical := S.canonical
      phiOne := by
        have hzeroCount : leaderCount X = 0 := by
          unfold leaderCount bitCount
          have hfun : (fun i : Fin n => (X i).leader) =
              (fun _ : Fin n => false) := by
            funext i
            exact S.zeroLeaders i
          rw [hfun]
          rw [ofFn_sum_const]
          simp
        have hdanger : Dangerous X :=
          dangerous_of_tail_probe ring X S.tailProbe
        simp [Phi, hzeroCount, dangerBit, hdanger] }
  exact
    { canonical := (R.successor hn3 hndvd edge).canonical
      zeroLeaders := ordinary_zero_leaders R hn3 edge he S.zeroLeaders
      tailBullet := ordinary_tail_bullet_false R hn3 edge he S.tailBullet
      tailProbe := ordinary_tail_probe_true R hn3 edge he S.tailProbe }

theorem tailProbeReady_directRank_childSum
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    {X : Fin n -> State k} (S : TailProbeReady hk ring X) :
    1 + (List.ofFn (fun edge : Fin n =>
      directRank hk ring (Rank.cutSuccessor hk ring X edge))).sum <=
      n * directRank hk ring X := by
  apply childSum_le_of_one_drop
    (fun edge : Fin n =>
      directRank hk ring (Rank.cutSuccessor hk ring X edge))
    (barrierEdge ring)
  · intro edge
    by_cases he : edge = barrierEdge ring
    · subst edge
      have hclean := S.barrier_reaches_canonicalClean hn3 hndvd
      rw [directRank_eq_zero_of_clean hclean]
      exact Nat.zero_le _
    · have S' := tailProbeReady_other hn3 hndvd S edge he
      rw [tailProbeReady_directRank_eq S', tailProbeReady_directRank_eq S,
        ordinary_tail_phase
          { canonical := S.canonical
            phiOne := by
              have hzeroCount : leaderCount X = 0 := by
                unfold leaderCount bitCount
                have hfun : (fun i : Fin n => (X i).leader) =
                    (fun _ : Fin n => false) := by
                  funext i
                  exact S.zeroLeaders i
                rw [hfun]
                rw [ofFn_sum_const]
                simp
              have hdanger : Dangerous X :=
                dangerous_of_tail_probe ring X S.tailProbe
              simp [Phi, hzeroCount, dangerBit, hdanger] }
          hn3 edge he]
      exact Nat.le_refl _
  · have hclean := S.barrier_reaches_canonicalClean hn3 hndvd
    rw [directRank_eq_zero_of_clean hclean,
      tailProbeReady_directRank_eq S]
    cases hphase : (X (tailCoord ring)).phase <;>
      simp [phaseCredit]

/-! ## Probe-free armed zero-leader branch -/

/-- The sole zero-leader state not covered by `Prepared`, `RestartReady`, or
`TailProbeReady`: no probes and an armed, bullet-free canonical tail. -/
structure ArmedEmpty {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (X : Fin n -> State k) : Prop extends RankOneCut hk ring X where
  zeroLeaders : forall i : Fin n, (X i).leader = false
  tailBullet : (X (tailCoord ring)).bullet = false
  tailPhase : (X (tailCoord ring)).phase = true
  allProbes : forall i : Fin n, (X i).probe = false

theorem armedEmpty_directRank_eq
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {X : Fin n -> State k} (S : ArmedEmpty hk ring X) :
    directRank hk ring X = 2 * n + 2 := by
  have hclean := not_clean_of_zero_leaders (hk := hk) (ring := ring)
    S.zeroLeaders
  rw [directRank_eq_zero hclean S.tailBullet S.zeroLeaders,
    probeFront_eq_zero_of_no_probe X S.allProbes]
  simp [phaseCredit, S.tailPhase]

theorem armedEmpty_other
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    {X : Fin n -> State k} (S : ArmedEmpty hk ring X)
    (edge : Fin n) (he : edge ≠ barrierEdge ring) :
    ArmedEmpty hk ring (Rank.cutSuccessor hk ring X edge) := by
  let R : RankOneCut hk ring X := S.toRankOneCut
  have hn2 : 1 < n := by omega
  have hnon : ¬ IsBarrier hk (X edge) (X (ring.rightNeighbor edge)) := by
    intro hb
    have het := (R.canonical edge).1 hb
    exact he (by simpa [barrierEdge] using het)
  have hprobeRaw : forall i : Fin n,
      (rawStep hk ring X edge i).probe = false := by
    intro i
    have hp := step_probes_eq_of_nonbarrier_initiator_clear
      hk ring hn2 X edge hnon (S.allProbes edge) i
    simpa [rawStep, OneBarrierCleanup.step, S.allProbes i] using hp
  refine
    { toRankOneCut := R.successor hn3 hndvd edge
      zeroLeaders := ordinary_zero_leaders R hn3 edge he S.zeroLeaders
      tailBullet := ordinary_tail_bullet_false R hn3 edge he S.tailBullet
      tailPhase := by
        rw [ordinary_tail_phase R hn3 edge he]
        exact S.tailPhase
      allProbes := ?_ }
  rw [R.cutSuccessor_eq_raw_of_ne_barrier edge he]
  exact hprobeRaw

theorem ArmedEmpty.barrierRestartReady
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    {X : Fin n -> State k} (S : ArmedEmpty hk ring X) :
    RestartReady hk ring
      (Rank.cutSuccessor hk ring X (barrierEdge ring)) := by
  have hn2 : 1 < n := by omega
  let tail := barrierEdge ring
  let head := ring.rightNeighbor tail
  let D0 := rawStep hk ring X tail
  have hbar : IsBarrier hk (X tail) (X head) :=
    (S.canonical tail).2 (by rfl)
  have hready : CenteredRenewal.AdvanceReady hk ring X tail :=
    ⟨hbar, by simpa [tail, barrierEdge] using S.tailPhase⟩
  have hpair : CenteredRenewal.transition hk (X tail) (X head) =
      (X tail,
        { X head with
          label := succLabel hk (X tail).label
          phase := false
          bullet := false
          probe := false }) := by
    rw [CenteredRenewal.transition_of_barrier hk _ _ hbar]
    rw [CenteredRenewal.barrierStep_phase_one hk _ _
      (by simpa [tail, barrierEdge] using S.tailPhase)]
    simp [probeHitsBarrier, S.allProbes tail]
  have hcut : Rank.cutSuccessor hk ring X tail = rotateCut ring D0 := by
    simp [Rank.cutSuccessor, hready, D0, rawStep]
  have hzeroRaw : forall i : Fin n, (D0 i).leader = false := by
    intro i
    have hone : OneBarrierAt hk ring X tail := by
      simpa [tail, barrierEdge] using
        canonicalOneBarrier_oneBarrierAt_tail hk ring X S.canonical
    have hleaders := barrier_phase_one_leaders_eq hk ring hn2 X tail hone
      (by simpa [tail, barrierEdge] using S.tailPhase)
      (S.allProbes tail)
    simpa [D0, rawStep, step, S.zeroLeaders i] using hleaders i
  have hprobesRaw : forall i : Fin n, (D0 i).probe = false := by
    intro i
    change (rawStep hk ring X tail i).probe = false
    by_cases hit : i = tail
    · subst i
      rw [rawStep_at_initiator hk ring X tail, hpair]
      exact S.allProbes tail
    · by_cases hih : i = head
      · subst i
        rw [show head = ring.rightNeighbor tail by rfl,
          rawStep_at_responder hk ring hn2 X tail, hpair]
      · rw [rawStep_frame hk ring X tail i hit (by simpa [head] using hih)]
        exact S.allProbes i
  have hheadState : D0 head =
      { X head with
        label := succLabel hk (X tail).label
        phase := false
        bullet := false
        probe := false } := by
    change rawStep hk ring X tail head = _
    rw [show head = ring.rightNeighbor tail by rfl,
      rawStep_at_responder hk ring hn2 X tail, hpair]
  rw [hcut]
  refine
    { canonical := by
        simpa [hcut] using
          (S.toRankOneCut.successor hn3 hndvd tail).canonical
      zeroLeaders := by
        intro i
        change (D0 (ring.rightNeighbor i)).leader = false
        exact hzeroRaw _
      tailBullet := by
        change (D0 (ring.rightNeighbor (tailCoord ring))).bullet = false
        have hrt : ring.rightNeighbor (tailCoord ring) = head := by
          simp [head, tail, barrierEdge]
        rw [hrt, hheadState]
      tailPhase := by
        change (D0 (ring.rightNeighbor (tailCoord ring))).phase = false
        have hrt : ring.rightNeighbor (tailCoord ring) = head := by
          simp [head, tail, barrierEdge]
        rw [hrt, hheadState]
      allProbesCleared := by
        intro i
        change (D0 (ring.rightNeighbor i)).probe = false
        exact hprobesRaw _ }

theorem armedEmpty_directRank_childSum
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    {X : Fin n -> State k} (S : ArmedEmpty hk ring X) :
    1 + (List.ofFn (fun edge : Fin n =>
      directRank hk ring (Rank.cutSuccessor hk ring X edge))).sum <=
      n * directRank hk ring X := by
  apply childSum_le_of_one_drop
    (fun edge : Fin n =>
      directRank hk ring (Rank.cutSuccessor hk ring X edge))
    (barrierEdge ring)
  · intro edge
    by_cases he : edge = barrierEdge ring
    · subst edge
      rw [restartReady_directRank_eq (S.barrierRestartReady hn3 hndvd),
        armedEmpty_directRank_eq S]
      omega
    · rw [armedEmpty_directRank_eq (armedEmpty_other hn3 hndvd S edge he),
        armedEmpty_directRank_eq S]
      exact Nat.le_refl _
  · rw [restartReady_directRank_eq (S.barrierRestartReady hn3 hndvd),
      armedEmpty_directRank_eq S]
    omega

/-! ## Exhaustive zero-leader branch -/

noncomputable def preparedOfZeroLeader
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {X : Fin n -> State k} (R : RankOneCut hk ring X)
    (hzero : forall i : Fin n, (X i).leader = false)
    (hbullet : (X (tailCoord ring)).bullet = false)
    (htailProbe : (X (tailCoord ring)).probe = false)
    (hprobe : exists i : Fin n, (X i).probe = true) :
    Prepared hk ring X :=
  let m := Classical.choose (exists_maxProbeAt X hprobe)
  { toActive :=
      { canonical := R.canonical
        zeroLeaders := hzero
        tailBullet := hbullet
        tailProbe := htailProbe
        hasProbe := hprobe }
    maxProbe := m
    maxProbeAt := Classical.choose_spec (exists_maxProbeAt X hprobe) }

theorem zeroLeader_directRank_childSum
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    {X : Fin n -> State k} (R : RankOneCut hk ring X)
    (hzero : forall i : Fin n, (X i).leader = false)
    (hbullet : (X (tailCoord ring)).bullet = false) :
    1 + (List.ofFn (fun edge : Fin n =>
      directRank hk ring (Rank.cutSuccessor hk ring X edge))).sum <=
      n * directRank hk ring X := by
  cases htailProbe : (X (tailCoord ring)).probe with
  | true =>
      let S : TailProbeReady hk ring X :=
        { canonical := R.canonical
          zeroLeaders := hzero
          tailBullet := hbullet
          tailProbe := htailProbe }
      exact tailProbeReady_directRank_childSum hn3 hndvd S
  | false =>
      by_cases hprobe : exists i : Fin n, (X i).probe = true
      · let S := preparedOfZeroLeader R hzero hbullet htailProbe hprobe
        exact prepared_directRank_childSum hn3 hndvd S
      · have hall : forall i : Fin n, (X i).probe = false := by
          intro i
          cases hi : (X i).probe
          · rfl
          · exact False.elim (hprobe ⟨i, hi⟩)
        cases hphase : (X (tailCoord ring)).phase with
        | false =>
            let S : RestartReady hk ring X :=
              { canonical := R.canonical
                zeroLeaders := hzero
                tailBullet := hbullet
                tailPhase := hphase
                allProbesCleared := hall }
            exact restartReady_directRank_childSum hn3 S
        | true =>
            let S : ArmedEmpty hk ring X :=
              { toRankOneCut := R
                zeroLeaders := hzero
                tailBullet := hbullet
                tailPhase := hphase
                allProbes := hall }
            exact armedEmpty_directRank_childSum hn3 hndvd S

/-! ## Shared one-leader and refresh facts -/

theorem directRank_le_four_mul_of_tail_bullet_false
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 3 <= n) (X : Fin n -> State k)
    (hbullet : (X (tailCoord ring)).bullet = false) :
    directRank hk ring X <= 4 * n := by
  by_cases hclean : exists ell : Fin n, CanonicalClean hk ring X ell
  · rw [directRank_eq_zero_of_clean hclean]
    omega
  · simp only [directRank, hclean, dite_false, hbullet, Bool.false_eq_true,
      if_false]
    split
    · let ell := Classical.choose
          ‹exists ell : Fin n, (X ell).leader = true›
      change 2 * n + 2 +
          (if ell = tailCoord ring then 1
            else 2 * ell.val + phaseNeed (X (tailCoord ring)).phase) <=
        4 * n
      by_cases helt : ell = tailCoord ring
      · simp [helt]
        omega
      · have hellt := ell.isLt
        have hval : ell.val <= n - 2 := by
          have hne : ell.val ≠ n - 1 := by
            intro hv
            apply helt
            apply Fin.ext
            exact hv
          omega
        cases hphase : (X (tailCoord ring)).phase <;>
          simp [helt, phaseNeed] <;> omega
    · have hfront := probeFront_le X
      cases hphase : (X (tailCoord ring)).phase <;>
        simp [phaseCredit] <;> omega

theorem RankOneCut.canonicalClean_of_tail_leader
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {X : Fin n -> State k} (R : RankOneCut hk ring X)
    (hell : (X (tailCoord ring)).leader = true)
    (hbullet : (X (tailCoord ring)).bullet = false) :
    CanonicalClean hk ring X (tailCoord ring) := by
  have hprobe := R.tailProbe_false_of_leader (tailCoord ring) hell
  refine ⟨R.canonical, hell, R.uniqueLeader hell, ?_⟩
  intro i hmarked
  by_cases hit : i = tailCoord ring
  · subst i
    rcases hmarked with hb | hp
    · rw [hbullet] at hb
      contradiction
    · rw [hprobe] at hp
      contradiction
  · change i.val < n - 1
    have hi := i.isLt
    have hne : i.val ≠ n - 1 := by
      intro hv
      apply hit
      apply Fin.ext
      exact hv
    omega

theorem RankOneCut.leader_ne_tail_of_notClean
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {X : Fin n -> State k} (R : RankOneCut hk ring X)
    (hclean : ¬ exists witness : Fin n,
      CanonicalClean hk ring X witness)
    (hbullet : (X (tailCoord ring)).bullet = false)
    (ell : Fin n) (hell : (X ell).leader = true) :
    ell ≠ tailCoord ring := by
  intro helt
  subst ell
  exact hclean ⟨tailCoord ring,
    R.canonicalClean_of_tail_leader hell hbullet⟩

theorem barrier_raw_leaders_eq_of_tail_probe_false
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) {X : Fin n -> State k}
    (R : RankOneCut hk ring X)
    (hprobe : (X (tailCoord ring)).probe = false) :
    forall i : Fin n,
      (rawStep hk ring X (barrierEdge ring) i).leader = (X i).leader := by
  have hn2 : 1 < n := by omega
  let tail := barrierEdge ring
  let head := ring.rightNeighbor tail
  have hbar : IsBarrier hk (X tail) (X head) :=
    (R.canonical tail).2 (by rfl)
  have hprobeTail : (X tail).probe = false := by
    simpa [tail, barrierEdge] using hprobe
  intro i
  by_cases hit : i = tail
  · subst i
    rw [rawStep_at_initiator hk ring X tail]
    rw [CenteredRenewal.transition_of_barrier hk _ _ hbar]
    cases hphase : (X tail).phase <;>
      simp [CenteredRenewal.barrierStep, hphase, probeHitsBarrier, hprobeTail]
  · by_cases hih : i = head
    · subst i
      rw [show head = ring.rightNeighbor tail by rfl,
        rawStep_at_responder hk ring hn2 X tail]
      rw [CenteredRenewal.transition_of_barrier hk _ _ hbar]
      cases hphase : (X tail).phase <;>
        cases hleader : (X head).leader <;>
        simp [CenteredRenewal.barrierStep, hphase, hleader]
    · exact congrArg State.leader
        (rawStep_frame hk ring X tail i hit (by simpa [head] using hih))

theorem barrier_phase_zero_tail_fields
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) {X : Fin n -> State k}
    (R : RankOneCut hk ring X)
    (hphase : (X (tailCoord ring)).phase = false) :
    let D := Rank.cutSuccessor hk ring X (barrierEdge ring)
    (D (tailCoord ring)).phase = true ∧
      (D (tailCoord ring)).bullet = (X (tailCoord ring)).bullet := by
  have hn2 : 1 < n := by omega
  let tail := barrierEdge ring
  let head := ring.rightNeighbor tail
  have hbar : IsBarrier hk (X tail) (X head) :=
    (R.canonical tail).2 (by rfl)
  have hnot : ¬ CenteredRenewal.AdvanceReady hk ring X tail := by
    intro hready
    have hp : (X (tailCoord ring)).phase = true := by
      simpa [tail, barrierEdge] using hready.2
    rw [hphase] at hp
    contradiction
  have hcut : Rank.cutSuccessor hk ring X tail = rawStep hk ring X tail := by
    unfold Rank.cutSuccessor
    simp only [hnot, if_false]
    rfl
  change
    ((Rank.cutSuccessor hk ring X tail) tail).phase = true ∧
      ((Rank.cutSuccessor hk ring X tail) tail).bullet = (X tail).bullet
  rw [hcut, rawStep_at_initiator hk ring X tail]
  rw [CenteredRenewal.transition_of_barrier hk _ _ hbar]
  rw [CenteredRenewal.barrierStep_phase_zero hk _ _
    (by simpa [tail, barrierEdge] using hphase)]
  cases hp : (X tail).probe <;> simp [probeHitsBarrier, hp]

theorem barrier_phase_one_tail_fields
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) {X : Fin n -> State k}
    (R : RankOneCut hk ring X)
    (hphase : (X (tailCoord ring)).phase = true) :
    let D := Rank.cutSuccessor hk ring X (barrierEdge ring)
    (D (tailCoord ring)).phase = false ∧
      (D (tailCoord ring)).bullet = false ∧
      (D (tailCoord ring)).probe = false := by
  have hn2 : 1 < n := by omega
  let tail := barrierEdge ring
  have hone : OneBarrierAt hk ring X tail := by
    simpa [tail, barrierEdge] using
      canonicalOneBarrier_oneBarrierAt_tail hk ring X R.canonical
  have hfresh := advance_sanitizes_new_tail hk ring hn2 X tail hone
    (by simpa [tail, barrierEdge] using hphase)
  have hbar : IsBarrier hk (X tail) (X (ring.rightNeighbor tail)) :=
    (R.canonical tail).2 (by rfl)
  have hready : CenteredRenewal.AdvanceReady hk ring X tail :=
    ⟨hbar, by simpa [tail, barrierEdge] using hphase⟩
  have hcut : Rank.cutSuccessor hk ring X tail =
      rotateCut ring (rawStep hk ring X tail) := by
    simp [Rank.cutSuccessor, rawStep, hready]
  rw [show barrierEdge ring = tail by rfl, hcut]
  change
    (rawStep hk ring X tail
        (ring.rightNeighbor (tailCoord ring))).phase = false ∧
      (rawStep hk ring X tail
        (ring.rightNeighbor (tailCoord ring))).bullet = false ∧
      (rawStep hk ring X tail
        (ring.rightNeighbor (tailCoord ring))).probe = false
  simpa [rawStep, OneBarrierCleanup.step, tail, barrierEdge] using hfresh

/-! ## Unique-leader branch -/

theorem oneLeader_other_directRank_le
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    {X : Fin n -> State k} (R : RankOneCut hk ring X)
    (hclean : ¬ exists witness : Fin n,
      CanonicalClean hk ring X witness)
    (hbullet : (X (tailCoord ring)).bullet = false)
    (ell : Fin n) (hell : (X ell).leader = true)
    (edge : Fin n) (he : edge ≠ barrierEdge ring) :
    directRank hk ring (Rank.cutSuccessor hk ring X edge) <=
      directRank hk ring X := by
  let D := Rank.cutSuccessor hk ring X edge
  let RD : RankOneCut hk ring D := R.successor hn3 hndvd edge
  have hbulletD : (D (tailCoord ring)).bullet = false :=
    ordinary_tail_bullet_false R hn3 edge he hbullet
  have hphaseD : (D (tailCoord ring)).phase =
      (X (tailCoord ring)).phase := ordinary_tail_phase R hn3 edge he
  by_cases hcleanD : exists witness : Fin n,
      CanonicalClean hk ring D witness
  · rw [directRank_eq_zero_of_clean hcleanD]
    exact Nat.zero_le _
  · by_cases hleaderD : exists witness : Fin n,
        (D witness).leader = true
    · obtain ⟨j, hj⟩ := hleaderD
      have hn2 : 1 < n := by omega
      have hnon : ¬ IsBarrier hk (X edge)
          (X (ring.rightNeighbor edge)) := by
        intro hb
        have het := (R.canonical edge).1 hb
        exact he (by simpa [barrierEdge] using het)
      have hjX : (X j).leader = true := by
        have hold := step_no_leader_birth_of_nonbarrier
          hk ring hn2 X edge hnon j
        apply hold
        have hcut := R.cutSuccessor_eq_raw_of_ne_barrier edge he
        simpa [D, hcut, rawStep, OneBarrierCleanup.step] using hj
      have hjeq : j = ell := R.uniqueLeader hell j hjX
      subst j
      rw [directRank_eq_one RD hcleanD hbulletD ell hj,
        directRank_eq_one R hclean hbullet ell hell, hphaseD]
      exact Nat.le_refl _
    · have hzeroD : forall i : Fin n, (D i).leader = false := by
        intro i
        cases hi : (D i).leader
        · rfl
        · exact False.elim (hleaderD ⟨i, hi⟩)
      have hfront := probeFront_le D
      have helt := R.leader_ne_tail_of_notClean hclean hbullet ell hell
      rw [directRank_eq_zero hcleanD hbulletD hzeroD,
        directRank_eq_one R hclean hbullet ell hell, hphaseD]
      cases hphase : (X (tailCoord ring)).phase <;>
        simp [helt, phaseCredit, phaseNeed] <;> omega

theorem oneLeader_barrier_phase_zero_drop
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    {X : Fin n -> State k} (R : RankOneCut hk ring X)
    (hclean : ¬ exists witness : Fin n,
      CanonicalClean hk ring X witness)
    (hbullet : (X (tailCoord ring)).bullet = false)
    (ell : Fin n) (hell : (X ell).leader = true)
    (hphase : (X (tailCoord ring)).phase = false) :
    directRank hk ring
        (Rank.cutSuccessor hk ring X (barrierEdge ring)) + 1 <=
      directRank hk ring X := by
  let D := Rank.cutSuccessor hk ring X (barrierEdge ring)
  let RD : RankOneCut hk ring D :=
    R.successor hn3 hndvd (barrierEdge ring)
  have hprobe := R.tailProbe_false_of_leader ell hell
  have helt := R.leader_ne_tail_of_notClean hclean hbullet ell hell
  have hfields := barrier_phase_zero_tail_fields hn3 R hphase
  have hphaseD : (D (tailCoord ring)).phase = true := hfields.1
  have hbulletD : (D (tailCoord ring)).bullet = false := by
    rw [hfields.2, hbullet]
  have hnot : ¬ CenteredRenewal.AdvanceReady hk ring X
      (barrierEdge ring) := by
    intro hready
    have hp : (X (tailCoord ring)).phase = true := by
      simpa [barrierEdge] using hready.2
    rw [hphase] at hp
    contradiction
  have hcut : D = rawStep hk ring X (barrierEdge ring) := by
    dsimp only [D]
    unfold Rank.cutSuccessor
    simp only [hnot, if_false]
    rfl
  have hellD : (D ell).leader = true := by
    rw [hcut, barrier_raw_leaders_eq_of_tail_probe_false hn3 R hprobe ell]
    exact hell
  change directRank hk ring D + 1 <= directRank hk ring X
  by_cases hcleanD : exists witness : Fin n,
      CanonicalClean hk ring D witness
  · have hpos := directRank_pos_of_rankOne_notClean R hclean
    rw [directRank_eq_zero_of_clean hcleanD]
    omega
  · rw [directRank_eq_one RD hcleanD hbulletD ell hellD,
      directRank_eq_one R hclean hbullet ell hell]
    simp [helt, hphase, hphaseD, phaseNeed]
    omega

theorem oneLeader_barrier_phase_one_drop
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    {X : Fin n -> State k} (R : RankOneCut hk ring X)
    (hclean : ¬ exists witness : Fin n,
      CanonicalClean hk ring X witness)
    (hbullet : (X (tailCoord ring)).bullet = false)
    (ell : Fin n) (hell : (X ell).leader = true)
    (hphase : (X (tailCoord ring)).phase = true) :
    directRank hk ring
        (Rank.cutSuccessor hk ring X (barrierEdge ring)) + 1 <=
      directRank hk ring X := by
  let D := Rank.cutSuccessor hk ring X (barrierEdge ring)
  let RD : RankOneCut hk ring D :=
    R.successor hn3 hndvd (barrierEdge ring)
  let left := ring.leftNeighbor ell
  have hprobe := R.tailProbe_false_of_leader ell hell
  have helt := R.leader_ne_tail_of_notClean hclean hbullet ell hell
  have hfields := barrier_phase_one_tail_fields hn3 R hphase
  have hphaseD : (D (tailCoord ring)).phase = false := hfields.1
  have hbulletD : (D (tailCoord ring)).bullet = false := hfields.2.1
  have hbar : IsBarrier hk (X (barrierEdge ring))
      (X (ring.rightNeighbor (barrierEdge ring))) :=
    (R.canonical (barrierEdge ring)).2 rfl
  have hready : CenteredRenewal.AdvanceReady hk ring X
      (barrierEdge ring) := ⟨hbar, by simpa [barrierEdge] using hphase⟩
  have hcut : D = rotateCut ring
      (rawStep hk ring X (barrierEdge ring)) := by
    dsimp only [D]
    simp [Rank.cutSuccessor, rawStep, hready]
  have hellD : (D left).leader = true := by
    rw [hcut]
    change (rawStep hk ring X (barrierEdge ring)
      (ring.rightNeighbor left)).leader = true
    rw [show ring.rightNeighbor left = ell by
      exact rightNeighbor_leftNeighbor_clean ring ell]
    rw [barrier_raw_leaders_eq_of_tail_probe_false hn3 R hprobe ell]
    exact hell
  change directRank hk ring D + 1 <= directRank hk ring X
  by_cases hellzero : ell.val = 0
  · have hleftTail : left = tailCoord ring := by
      apply Fin.ext
      simp [left, DirectedRing.leftNeighbor, hellzero, tailCoord]
    have hcleanD : CanonicalClean hk ring D (tailCoord ring) := by
      have hellTailD : (D (tailCoord ring)).leader = true := by
        simpa [hleftTail] using hellD
      exact RD.canonicalClean_of_tail_leader hellTailD hbulletD
    have hpos := directRank_pos_of_rankOne_notClean R hclean
    rw [directRank_eq_zero_of_clean ⟨tailCoord ring, hcleanD⟩]
    omega
  · have hellpos : 0 < ell.val := by omega
    have hleftVal : left.val = ell.val - 1 :=
      leftNeighbor_val_of_pos ring ell hellpos
    have hleftNeTail : left ≠ tailCoord ring := by
      intro hlt
      have htailVal : left.val = n - 1 := congrArg Fin.val hlt
      have hellLt := ell.isLt
      omega
    by_cases hcleanD : exists witness : Fin n,
        CanonicalClean hk ring D witness
    · have hpos := directRank_pos_of_rankOne_notClean R hclean
      rw [directRank_eq_zero_of_clean hcleanD]
      omega
    · rw [directRank_eq_one RD hcleanD hbulletD left hellD,
        directRank_eq_one R hclean hbullet ell hell]
      simp [hleftNeTail, helt, hphase, hphaseD, phaseNeed]
      omega

theorem oneLeader_barrier_directRank_drop
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    {X : Fin n -> State k} (R : RankOneCut hk ring X)
    (hclean : ¬ exists witness : Fin n,
      CanonicalClean hk ring X witness)
    (hbullet : (X (tailCoord ring)).bullet = false)
    (ell : Fin n) (hell : (X ell).leader = true) :
    directRank hk ring
        (Rank.cutSuccessor hk ring X (barrierEdge ring)) + 1 <=
      directRank hk ring X := by
  cases hphase : (X (tailCoord ring)).phase with
  | false =>
      exact oneLeader_barrier_phase_zero_drop
        hn3 hndvd R hclean hbullet ell hell hphase
  | true =>
      exact oneLeader_barrier_phase_one_drop
        hn3 hndvd R hclean hbullet ell hell hphase

theorem oneLeader_directRank_childSum
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    {X : Fin n -> State k} (R : RankOneCut hk ring X)
    (hclean : ¬ exists witness : Fin n,
      CanonicalClean hk ring X witness)
    (hbullet : (X (tailCoord ring)).bullet = false)
    (ell : Fin n) (hell : (X ell).leader = true) :
    1 + (List.ofFn (fun edge : Fin n =>
      directRank hk ring (Rank.cutSuccessor hk ring X edge))).sum <=
      n * directRank hk ring X := by
  apply childSum_le_of_one_drop
    (fun edge : Fin n =>
      directRank hk ring (Rank.cutSuccessor hk ring X edge))
    (barrierEdge ring)
  · intro edge
    by_cases he : edge = barrierEdge ring
    · subst edge
      have hdrop := oneLeader_barrier_directRank_drop
        hn3 hndvd R hclean hbullet ell hell
      omega
    · exact oneLeader_other_directRank_le
        hn3 hndvd R hclean hbullet ell hell edge he
  · exact oneLeader_barrier_directRank_drop
      hn3 hndvd R hclean hbullet ell hell

/-! ## Dirty-tail refresh branch -/

theorem refresh_other_directRank_le
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) {X : Fin n -> State k}
    (R : RankOneCut hk ring X)
    (hclean : ¬ exists witness : Fin n,
      CanonicalClean hk ring X witness)
    (hbullet : (X (tailCoord ring)).bullet = true)
    (edge : Fin n) (he : edge ≠ barrierEdge ring) :
    directRank hk ring (Rank.cutSuccessor hk ring X edge) <=
      directRank hk ring X := by
  let D := Rank.cutSuccessor hk ring X edge
  have hphaseD : (D (tailCoord ring)).phase =
      (X (tailCoord ring)).phase := ordinary_tail_phase R hn3 edge he
  change directRank hk ring D <= directRank hk ring X
  by_cases hcleanD : exists witness : Fin n,
      CanonicalClean hk ring D witness
  · rw [directRank_eq_zero_of_clean hcleanD]
    exact Nat.zero_le _
  · cases hbulletD : (D (tailCoord ring)).bullet
    · have hcore := directRank_le_four_mul_of_tail_bullet_false
          hk ring hn3 D hbulletD
      rw [directRank_eq_refresh hclean hbullet]
      cases hphase : (X (tailCoord ring)).phase <;>
        simp [phaseNeed] <;> omega
    · rw [directRank_eq_refresh hcleanD hbulletD,
        directRank_eq_refresh hclean hbullet, hphaseD]
      exact Nat.le_refl _

theorem refresh_barrier_phase_zero_drop
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) {X : Fin n -> State k}
    (R : RankOneCut hk ring X)
    (hclean : ¬ exists witness : Fin n,
      CanonicalClean hk ring X witness)
    (hbullet : (X (tailCoord ring)).bullet = true)
    (hphase : (X (tailCoord ring)).phase = false) :
    directRank hk ring
        (Rank.cutSuccessor hk ring X (barrierEdge ring)) + 1 <=
      directRank hk ring X := by
  let D := Rank.cutSuccessor hk ring X (barrierEdge ring)
  have hfields := barrier_phase_zero_tail_fields hn3 R hphase
  have hphaseD : (D (tailCoord ring)).phase = true := hfields.1
  have hbulletD : (D (tailCoord ring)).bullet = true := by
    rw [hfields.2, hbullet]
  change directRank hk ring D + 1 <= directRank hk ring X
  by_cases hcleanD : exists witness : Fin n,
      CanonicalClean hk ring D witness
  · rw [directRank_eq_zero_of_clean hcleanD,
      directRank_eq_refresh hclean hbullet]
    simp [phaseNeed, hphase]
  · rw [directRank_eq_refresh hcleanD hbulletD,
      directRank_eq_refresh hclean hbullet]
    simp [phaseNeed, hphase, hphaseD]

theorem refresh_barrier_phase_one_drop
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) {X : Fin n -> State k}
    (R : RankOneCut hk ring X)
    (hclean : ¬ exists witness : Fin n,
      CanonicalClean hk ring X witness)
    (hbullet : (X (tailCoord ring)).bullet = true)
    (hphase : (X (tailCoord ring)).phase = true) :
    directRank hk ring
        (Rank.cutSuccessor hk ring X (barrierEdge ring)) + 1 <=
      directRank hk ring X := by
  let D := Rank.cutSuccessor hk ring X (barrierEdge ring)
  have hfields := barrier_phase_one_tail_fields hn3 R hphase
  have hbulletD : (D (tailCoord ring)).bullet = false := hfields.2.1
  have hcore := directRank_le_four_mul_of_tail_bullet_false
    hk ring hn3 D hbulletD
  change directRank hk ring D + 1 <= directRank hk ring X
  rw [directRank_eq_refresh hclean hbullet]
  simp [phaseNeed, hphase]
  omega

theorem refresh_barrier_directRank_drop
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) {X : Fin n -> State k}
    (R : RankOneCut hk ring X)
    (hclean : ¬ exists witness : Fin n,
      CanonicalClean hk ring X witness)
    (hbullet : (X (tailCoord ring)).bullet = true) :
    directRank hk ring
        (Rank.cutSuccessor hk ring X (barrierEdge ring)) + 1 <=
      directRank hk ring X := by
  cases hphase : (X (tailCoord ring)).phase with
  | false =>
      exact refresh_barrier_phase_zero_drop
        hn3 R hclean hbullet hphase
  | true =>
      exact refresh_barrier_phase_one_drop
        hn3 R hclean hbullet hphase

theorem refresh_directRank_childSum
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) {X : Fin n -> State k}
    (R : RankOneCut hk ring X)
    (hclean : ¬ exists witness : Fin n,
      CanonicalClean hk ring X witness)
    (hbullet : (X (tailCoord ring)).bullet = true) :
    1 + (List.ofFn (fun edge : Fin n =>
      directRank hk ring (Rank.cutSuccessor hk ring X edge))).sum <=
      n * directRank hk ring X := by
  apply childSum_le_of_one_drop
    (fun edge : Fin n =>
      directRank hk ring (Rank.cutSuccessor hk ring X edge))
    (barrierEdge ring)
  · intro edge
    by_cases he : edge = barrierEdge ring
    · subst edge
      have hdrop := refresh_barrier_directRank_drop
        hn3 R hclean hbullet
      omega
    · exact refresh_other_directRank_le
        hn3 R hclean hbullet edge he
  · exact refresh_barrier_directRank_drop hn3 R hclean hbullet

/-! ## Exhaustive raw Bellman inequality -/

theorem directRank_childSum
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    {X : Fin n -> State k} (R : RankOneCut hk ring X)
    (hclean : ¬ exists witness : Fin n,
      CanonicalClean hk ring X witness) :
    1 + (List.ofFn (fun edge : Fin n =>
      directRank hk ring (Rank.cutSuccessor hk ring X edge))).sum <=
      n * directRank hk ring X := by
  cases hbullet : (X (tailCoord ring)).bullet with
  | true =>
      exact refresh_directRank_childSum hn3 R hclean hbullet
  | false =>
      by_cases hleader : exists ell : Fin n, (X ell).leader = true
      · obtain ⟨ell, hell⟩ := hleader
        exact oneLeader_directRank_childSum
          hn3 hndvd R hclean hbullet ell hell
      · have hzero : forall i : Fin n, (X i).leader = false := by
          intro i
          cases hi : (X i).leader
          · rfl
          · exact False.elim (hleader ⟨i, hi⟩)
        exact zeroLeader_directRank_childSum
          hn3 hndvd R hzero hbullet

/-! ## Stopped literal process and finite-horizon duration -/

theorem terminalPotential_terminalStep_eq
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (state : TerminalState hk ring) (edge : Fin n) :
    terminalPotential (terminalStep hn3 hndvd state edge) =
      n * directRank hk ring
        (Rank.cutSuccessor hk ring state.configuration edge) := by
  by_cases hclean : exists ell : Fin n, CanonicalClean hk ring
      (Rank.cutSuccessor hk ring state.configuration edge) ell
  · simp [terminalStep, hclean, terminalPotential,
      directRank_eq_zero_of_clean hclean]
  · simp [terminalStep, hclean, terminalPotential]

/-- Scale-one Bellman certificate for every live canonical rank-one state.
The stopped process has only literal active children and actual clean success
children; there is no failure branch. -/
theorem terminalNatBellmanSuperSolution
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n) :
    NatBellmanSuperSolution (terminalStep (hk := hk) (ring := ring)
      hn3 hndvd) 1 terminalPotential := by
  refine ⟨rfl, rfl, ?_⟩
  intro state
  have hraw := directRank_childSum hn3 hndvd
    state.rankOne state.notClean
  have hmul := Nat.mul_le_mul_left n hraw
  have hsum :
      (List.ofFn (fun edge : Fin n =>
        terminalPotential (terminalStep hn3 hndvd state edge))).sum =
      n * (List.ofFn (fun edge : Fin n =>
        directRank hk ring
          (Rank.cutSuccessor hk ring state.configuration edge))).sum := by
    calc
      (List.ofFn (fun edge : Fin n =>
        terminalPotential (terminalStep hn3 hndvd state edge))).sum =
          (List.ofFn (fun edge : Fin n =>
            n * directRank hk ring
              (Rank.cutSuccessor hk ring state.configuration edge))).sum :=
        ofFn_sum_eq _ _ (terminalPotential_terminalStep_eq hn3 hndvd state)
      _ = n * (List.ofFn (fun edge : Fin n =>
            directRank hk ring
              (Rank.cutSuccessor hk ring state.configuration edge))).sum :=
        ofFn_sum_mul_left n _
  rw [hsum]
  simp only [Nat.one_mul, terminalPotential]
  simpa [Nat.mul_add, Nat.mul_assoc] using hmul

/-- Strong finite-horizon terminal cost bound with the nonnegative residual
retained. -/
theorem terminal_duration_add_residual_le
    {n k T : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (X : Fin n -> State k) (R : RankOneCut hk ring X) :
    truncatedActiveCostNumerator (terminalStep hn3 hndvd)
          (initialNode X R) T +
        treeWeight (terminalStep hn3 hndvd) terminalPotential
          (initialNode X R) T <=
      n ^ T * terminalPotential (initialNode X R) := by
  simpa using truncatedActiveCost_add_treeWeight_le_of_natSuperSolution
    (terminalStep (hk := hk) (ring := ring) hn3 hndvd) 1
    terminalPotential (terminalNatBellmanSuperSolution hn3 hndvd)
    (initialNode X R) T

/-- Uniform truncated expected-cost numerator.  The normalized expectation is
at most `4*n^2 + 2*n`, hence also below the published `8*n^2 + 9*n`. -/
theorem terminal_truncatedActiveCostNumerator_le_dirtyBudget
    {n k T : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (X : Fin n -> State k) (R : RankOneCut hk ring X) :
    truncatedActiveCostNumerator (terminalStep hn3 hndvd)
        (initialNode X R) T <= n ^ T * dirtyBudget n := by
  have hcost := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    (terminalStep (hk := hk) (ring := ring) hn3 hndvd) 1
    terminalPotential (terminalNatBellmanSuperSolution hn3 hndvd)
    (initialNode X R) T
  simp only [Nat.one_mul] at hcost
  exact Nat.le_trans hcost (Nat.mul_le_mul_left (n ^ T)
    (initialNode_potential_le_dirtyBudget hn3 X R))

theorem terminal_truncatedActiveCostNumerator_le_terminalBudget
    {n k T : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (X : Fin n -> State k) (R : RankOneCut hk ring X) :
    truncatedActiveCostNumerator (terminalStep hn3 hndvd)
        (initialNode X R) T <=
      n ^ T * ComplexityConstants.terminalBudget n := by
  exact Nat.le_trans
    (terminal_truncatedActiveCostNumerator_le_dirtyBudget
      hn3 hndvd X R)
    (Nat.mul_le_mul_left (n ^ T) (dirtyBudget_le_terminalBudget n))

end TerminalRankOne
end CenteredRenewal
end AAFJPK
