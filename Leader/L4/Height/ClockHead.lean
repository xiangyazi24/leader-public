import Leader.L4.Height.Headline
import Leader.L4.Height.LogicalStrong
import Leader.L4.Height.LegitCoset
import Leader.L4.Height.MomentGeom
import Leader.L4.Height.ChainBridge

/-!
# The paired clock layer and permanent single-anchor observations

Each physical letter selects a site and a bit. Clock repair concerns the
native records, whereas the logical clock uses coherent natural-valued lifts.
The coherent-relift overrun estimate and the virtual level comparison below
connect these descriptions. The warm trial bounds charge missed levels
explicitly. The two- and four-site counterexamples distinguish the service,
observation, and permanence assumptions needed for a quadratic hitting bound.
-/
namespace L4.Height

open Classical
open L4.Compiler.Native

noncomputable section

/-- Every paired physical letter publishes its site and offered bit. -/
def clockAct {m : Nat} : OverrunAct (2 * m) m :=
  fun _ e => some (physicalSite e, physicalBit e)

/-- The native clock driven by the paired physical alphabet. -/
def clockNext {m B M : Nat} (hm : 0 < m) :
    OverrunState m → Fin (2 * m) → OverrunState m :=
  overrunNext (B := B) (M := M) hm clockAct

/-- Lifted activation projects to the literal native recovery transition. -/
theorem clock_activate_cfg {m B M : Nat} (hm : 0 < m)
    (s : WordState m) (i : Fin m) (b : Bool) :
    (activate B M hm s i b).cfg =
      Recover.StageThree.activate B M hm s.cfg i b := by
  funext j
  rfl

/-- The concrete clock chain carries its most recently served site. -/
def clockChain {m B M : Nat} (hm : 0 < m) :
    Recover.Chain.ClockChain (OverrunState m) (2 * m) m B M hm where
  next := clockNext (B := B) (M := M) hm
  cfg := fun y => y.1.cfg
  act := clockAct
  lastAct := Prod.snd
  cfg_next := by
    intro y e
    exact clock_activate_cfg hm y.1 (physicalSite e) (physicalBit e)
  last_next := by
    intro y e
    rfl

private theorem clock_alphabet_nodup {α : Type} {n : Nat}
    (f : Fin n → α) (hf : Function.Injective f) :
    (List.ofFn f).Nodup := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.nodup_cons]
      constructor
      · intro h
        obtain ⟨i, hi⟩ := List.mem_ofFn.mp h
        have he := hf hi
        cases he
      · exact ih (fun i => f i.succ)
          (fun i j h => Fin.succ_inj.mp (hf h))

/-- Exactly two alphabet letters serve each site, independently of the state. -/
theorem clock_service_count {m B M : Nat} (hm : 0 < m)
    (x : OverrunState m) (i : Fin m) :
    countFin (fun e : Fin (2 * m) =>
      decide (((clockChain (B := B) (M := M) hm).act x e).map Prod.fst =
        some i)) = 2 := by
  let a : Fin (2 * m) := ⟨2 * i.val, by omega⟩
  let b : Fin (2 * m) := ⟨2 * i.val + 1, by omega⟩
  let p (e : Fin (2 * m)) : Bool := decide (physicalSite e = i)
  let es := List.ofFn (fun e : Fin (2 * m) => e)
  have hab : a ≠ b := by
    intro h
    have he := congrArg Fin.val h
    dsimp [a, b] at he
    omega
  have hn : es.Nodup :=
    clock_alphabet_nodup (fun e : Fin (2 * m) => e) (fun _ _ h => h)
  have hnab : [a, b].Nodup := by simp [hab]
  have hp (e : Fin (2 * m)) : p e = true ↔ e = a ∨ e = b := by
    simp only [p, decide_eq_true_eq]
    constructor
    · intro h
      have he := congrArg Fin.val h
      change e.val / 2 = i.val at he
      have hr := Nat.mod_lt e.val (by omega : 0 < 2)
      have hd := Nat.mod_add_div e.val 2
      by_cases hz : e.val % 2 = 0
      · left
        apply Fin.ext
        dsimp [a]
        omega
      · right
        apply Fin.ext
        dsimp [b]
        omega
    · intro h
      apply Fin.ext
      rcases h with h | h <;> subst e <;>
        change _ / 2 = i.val <;> dsimp [a, b] <;> omega
  have heq : (es.filter p).Perm [a, b] := by
    apply (List.perm_ext_iff_of_nodup (hn.filter p) hnab).2
    intro e
    simp only [List.mem_filter, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · intro h
      exact (hp e).1 h.2
    · intro h
      exact ⟨List.mem_ofFn.mpr ⟨e, rfl⟩, (hp e).2 h⟩
  simpa [countFin, clockChain, clockAct, es, p] using heq.length_eq

/-- Native custody is preserved by every concrete clock transition. -/
theorem clock_wellFormed_next {m B M : Nat} (hm : 0 < m)
    (hM : Recover.StageTwo.ClockParams M)
    (x : OverrunState m) (e : Fin (2 * m))
    (hx : Recover.StageTwo.WellFormed M x.1.cfg) :
    Recover.StageTwo.WellFormed M ((clockNext (B := B) (M := M) hm x e).1.cfg) := by
  change Recover.StageTwo.WellFormed M
    (activate B M hm x.1 (physicalSite e) (physicalBit e)).cfg
  rw [clock_activate_cfg]
  exact Recover.Chain.wellFormed_activate hM hm x.1.cfg hx
    (physicalSite e) (physicalBit e)

/-- Native custody persists on every finite scheduler word. -/
theorem clock_wellFormed_run {m B M : Nat} (hm : 0 < m)
    (hM : Recover.StageTwo.ClockParams M)
    (x : OverrunState m) (u : Thru.Word (2 * m))
    (hx : Recover.StageTwo.WellFormed M x.1.cfg) :
    Recover.StageTwo.WellFormed M
      (Thru.runWord (clockNext (B := B) (M := M) hm) x u).1.cfg := by
  induction u generalizing x with
  | nil => exact hx
  | cons e u ih =>
      exact ih (clockNext (B := B) (M := M) hm x e)
        (clock_wellFormed_next hm hM x e hx)

/-- Forgetting the publication marker gives the physical clock execution. -/
theorem clock_run_physical {m B M : Nat} (hm : 0 < m)
    (x : OverrunState m) (u : Thru.Word (2 * m)) :
    (Thru.runWord (clockNext (B := B) (M := M) hm) x u).1 =
      physicalRun B M hm x.1 u := by
  induction u generalizing x with
  | nil => rfl
  | cons e u ih => exact ih (clockNext (B := B) (M := M) hm x e)

end
end L4.Height
namespace L4.Height
/-- The constant and linear terms of a power expansion give a lower bound. -/
private theorem power_linear_lower (a b q : Nat) :
    (a + (q + 1) * b) * a ^ q ≤ (a + b) ^ (q + 1) := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hcoeff :
        (a + (q + 1 + 1) * b) * a ≤
          (a + (q + 1) * b) * (a + b) := by
      calc
        (a + (q + 1 + 1) * b) * a =
            (a + (q + 1) * b) * a + a * b := by
          simp only [Nat.add_mul, Nat.one_mul]
          ac_rfl
        _ ≤ (a + (q + 1) * b) * a +
              (a + (q + 1) * b) * b :=
          Nat.add_le_add_left
            (Nat.mul_le_mul_right b (Nat.le_add_right a ((q + 1) * b))) _
        _ = (a + (q + 1) * b) * (a + b) :=
          (Nat.mul_add _ _ _).symm
    calc
      (a + (q + 1 + 1) * b) * a ^ (q + 1) =
          ((a + (q + 1 + 1) * b) * a) * a ^ q := by
        rw [Nat.pow_succ]
        ac_rfl
      _ ≤ ((a + (q + 1) * b) * (a + b)) * a ^ q :=
        Nat.mul_le_mul_right (a ^ q) hcoeff
      _ = ((a + (q + 1) * b) * a ^ q) * (a + b) := by ac_rfl
      _ ≤ (a + b) ^ (q + 1) * (a + b) :=
        Nat.mul_le_mul_right (a + b) ih
      _ = (a + b) ^ (q + 1 + 1) := (Nat.pow_succ _ _).symm

/-- Two service letters per site suffice for the geometric block inequality
at every block length at least four times the number of sites. -/
theorem service_length_ratio {m L : Nat} (hm : 0 < m) (hL : 4 * m ≤ L) :
    4 * (2 * m - 2) ^ (L - 1) ≤ (2 * m) ^ (L - 1) := by
  let a := 2 * m - 2
  let q := L - 2
  have hsum : a + 2 = 2 * m := by dsimp [a]; omega
  have hexp : q + 1 = L - 1 := by dsimp [q]; omega
  have hcoeff : 4 * a ≤ a + (q + 1) * 2 := by dsimp [a, q]; omega
  calc
    4 * (2 * m - 2) ^ (L - 1) = (4 * a) * a ^ q := by
      change 4 * a ^ (L - 1) = (4 * a) * a ^ q
      rw [← hexp, Nat.pow_succ]
      ac_rfl
    _ ≤ (a + (q + 1) * 2) * a ^ q :=
      Nat.mul_le_mul_right (a ^ q) hcoeff
    _ ≤ (a + 2) ^ (q + 1) := power_linear_lower a 2 q
    _ = (2 * m) ^ (L - 1) := by rw [hsum, hexp]

/-- The concrete uniform scheduler supplies the service moment at any
length at least four times the number of sites. -/
theorem clock_served_moment {m B M L : Nat} (hm : 0 < m)
    (hL : 4 * m ≤ L) :
    ∀ i y, Thru.MomentAt (clockChain (B := B) (M := M) hm).next
      ((clockChain (B := B) (M := M) hm).served i) L y := by
  apply served_moment (clockChain (B := B) (M := M) hm)
    (by omega) (k := 2)
  · intro x i
    simpa only [clock_service_count] using (Nat.le_refl 2)
  · exact service_length_ratio hm hL

/-- An explicit valid service block length is four times the number of sites. -/
theorem clock_served_moment_explicit {m B M : Nat} (hm : 0 < m) :
    ∀ i y, Thru.MomentAt (clockChain (B := B) (M := M) hm).next
      ((clockChain (B := B) (M := M) hm).served i) (4 * m) y :=
  clock_served_moment hm (Nat.le_refl _)
end L4.Height
namespace L4.Height

open L4.Compiler.Native
open Classical

private def skewClock (d : Nat) : OverrunState 2 :=
  (⟨fun _ => ⟨128, false, {}, {}⟩, fun i => if i = 0 then 0 else d + 1⟩, none)

private theorem skewClock_lg (d : Nat) :
    Recover.Chain.LgSet (clockChain (B := 16) (M := 256) (by decide)) (skewClock d) := by
  refine ⟨fun _ => rfl, ?_, ?_⟩
  · intro i hr
    change false = true at hr
    cases hr
  · intro i
    change 128 < 256 ∧ (false = true → 128 < 256 / 2)
    decide

private theorem physical_lift_step_le {m : Nat} (B M : Nat) (hm : 0 < m)
    (s : WordState m) (e : Fin (2*m)) (i : Fin m) :
    (physicalNext B M hm s e).lift i ≤ s.lift i + 1 := by
  by_cases h : i = physicalSite e
  · subst i
    cases ha : clockAction M hm s (physicalSite e) <;>
      simp [physicalNext, activate, setAt, ha, advanceLift]
  · simp [physicalNext, activate, setAt, h]

private theorem physical_lift_le_length {m : Nat} (B M : Nat) (hm : 0 < m)
    (s : WordState m) (u : List (Fin (2*m))) (i : Fin m) :
    (physicalRun B M hm s u).lift i ≤ s.lift i + u.length := by
  induction u generalizing s with
  | nil => simp [physicalRun]
  | cons e u ih =>
    have hs := physical_lift_step_le B M hm s e i
    have ht := ih (physicalNext B M hm s e)
    simp only [physicalRun, List.length_cons]
    omega

/-- For every deadline a clean, quiet configuration admits stored lifts for
which every word misses every target above the initial maximum. -/
theorem stored_lift_deadline_counterexample (d : Nat) :
    ∃ x : OverrunState 2,
      Recover.Chain.LgSet (clockChain (B := 16) (M := 256) (by decide)) x ∧
      ∀ ell, x.1.lift 1 < ell →
      ¬ 4 * wordSum (fun u : List (Fin (2*2)) =>
        if (∃ i, (physicalRun 16 256 (by decide) x.1 u).lift i < ell)
          then 1 else 0) d ≤ 4 ^ d := by
  let x := skewClock d
  refine ⟨x, skewClock_lg _, ?_⟩
  intro ell hell
  have hlarge : d + 1 < ell := by simpa [x, skewClock] using hell
  have hone := wordSum_mono_on_length (fun _ : List (Fin (2*2)) => 1)
    (fun u => if (∃ i, (physicalRun 16 256 (by decide) x.1 u).lift i < ell)
      then 1 else 0) d (by
        intro u hu
        have h := physical_lift_le_length 16 256 (by decide) x.1 u 0
        have hzero : x.1.lift 0 = 0 := rfl
        rw [hzero, hu, Nat.zero_add] at h
        simp [show ∃ i, (physicalRun 16 256 (by decide) x.1 u).lift i < ell from
          ⟨0, by omega⟩])
  rw [wordSum_const_one] at hone
  have hp : 0 < 4 ^ d := Nat.pow_pos (by decide)
  change 4 ^ d ≤ _ at hone
  omega

end L4.Height
namespace L4.Height

open Classical
open L4.Compiler.Native

noncomputable section

/-- The height modulus at parameter two is the singleton modulus. -/
theorem unit_modulus_parameters :
    heightMod 2 = 1 ∧ modulus 2 = 256 ∧ ClockParams 256 ∧
      Recover.StageTwo.ClockParams 256 ∧
      32 ∣ 256 / 2 ∧ (2 : Nat) < 256 / 2 ∧
      (2 : Nat) / 2 < 256 / 2 ∧ (2 : Nat) * 2 ≤ 4 := by
  exact ⟨rfl, rfl, ⟨by decide, rfl⟩, ⟨by decide, rfl⟩,
    ⟨4, rfl⟩, by decide, by decide, by decide⟩

/-- A snapshot with zero height and zero proposed height. -/
def UnitSnapshot (v : Snapshot) : Prop := v.x = 0 ∧ v.proposal = 0

/-- Both snapshot banks carry zero height and zero proposed height. -/
def UnitRecord (v : NativeRecord) : Prop :=
  UnitSnapshot v.prior ∧ UnitSnapshot v.curr

/-- The singleton modulus preserves zero height and proposal in every phase. -/
theorem unit_phase_preserved (j : Nat) (l c r : Snapshot) (b : Bool)
    (hc : UnitSnapshot c) : UnitSnapshot (phaseUpdate 1 j l c r b) := by
  rcases hc with ⟨hx, hp⟩
  unfold UnitSnapshot phaseUpdate
  split <;> simp_all <;> omega

/-- Every native clock action preserves the zero-height invariant. -/
theorem unit_finish_preserved (l c r : NativeRecord) (a : ClockAction)
    (b : Bool) (hc : UnitRecord c) :
    UnitRecord (finishNative 1 l c r a b) := by
  cases a with
  | reset => simp [finishNative, UnitRecord, UnitSnapshot]
  | propagate t => simp [finishNative, UnitRecord, UnitSnapshot]
  | clear => simp [finishNative, UnitRecord, UnitSnapshot]
  | hold => exact hc
  | inc t =>
      exact ⟨hc.2, unit_phase_preserved _ _ _ _ _ hc.2⟩

/-- A literal activation preserves both zero-height snapshot banks. -/
theorem unit_activate_preserved {m M : Nat} (hm : 0 < m)
    (s : WordState m) (hs : ∀ i, UnitRecord (s.cfg i))
    (i : Fin m) (b : Bool) :
    ∀ j, UnitRecord ((activate 1 M hm s i b).cfg j) := by
  intro j
  by_cases he : j = i
  · subst j
    change UnitRecord
      (setAt s.cfg i
        (finishNative 1 (s.cfg (left hm i)) (s.cfg i)
          (s.cfg (right hm i)) (clockAction M hm s i) b) i)
    rw [setAt_self]
    exact unit_finish_preserved _ _ _ _ _ (hs i)
  · simpa [activate, setAt, he] using hs j

/-- Defaulting any first-level observation still yields zero height and proposal. -/
theorem unit_levelCurr_preserved {m M : Nat} (hm : 0 < m)
    (h : List (Activation m)) (s : WordState m)
    (hs : ∀ i, UnitRecord (s.cfg i)) (i : Fin m) (ell : Nat) :
    UnitSnapshot ((levelCurr 1 M hm h s i ell).getD ({} : Snapshot)) := by
  induction h generalizing s with
  | nil =>
      by_cases he : s.lift i = ell
      · simpa [levelCurr, he] using (hs i).2
      · simp [levelCurr, he, UnitSnapshot]
  | cons a h ih =>
      by_cases he : s.lift i = ell
      · simpa [levelCurr, he] using (hs i).2
      · simpa [levelCurr, he] using
          ih (activate 1 M hm s a.1 a.2)
            (unit_activate_preserved hm s hs a.1 a.2)

/-- The two-site initial state has correct equal clocks and empty snapshots. -/
def unitClockState : WordState 2 where
  cfg _ := ⟨128, false, {}, {}⟩
  lift _ := 0

/-- Both sites exist in the counterexample ring. -/
theorem unit_ring_positive : 0 < (2 : Nat) := by decide

/-- The initial native clock and its stored lift agree exactly. -/
theorem unit_clock_legit : Legit 256 unit_ring_positive unitClockState := by
  refine ⟨fun _ => rfl, fun _ => rfl, ?_⟩
  intro i j _
  change Near 0 0
  exact ⟨by omega, by omega⟩

/-- The same start is in the native quiet legitimate target. -/
theorem unit_clock_lgSet :
    Recover.Chain.LgSet
      (clockChain (B := 1) (M := 256) unit_ring_positive)
      (unitClockState, none) := by
  refine ⟨fun _ => rfl, ?_, ?_⟩
  · intro i
    simp [clockChain, unitClockState, Recover.StageThree.rootB,
      Recover.StageThree.upperGapB]
  · intro i
    change (128 : Nat) < 256 ∧ (false = true → (128 : Nat) < 256 / 2)
    decide

/-- Every finite physical execution preserves zero height in both banks. -/
theorem unit_physical_preserved {m M : Nat} (hm : 0 < m)
    (u : List (Fin (2 * m))) (s : WordState m)
    (hs : ∀ i, UnitRecord (s.cfg i)) :
    ∀ i, UnitRecord ((physicalRun 1 M hm s u).cfg i) := by
  induction u generalizing s with
  | nil => exact hs
  | cons e u ih =>
      exact ih (physicalNext 1 M hm s e)
        (unit_activate_preserved hm s hs (physicalSite e) (physicalBit e))

/-- The literal two-site execution never leaves zero height and proposal. -/
theorem unit_physical_zero (u : List (Fin (2 * 2))) (i : Fin 2) :
    UnitRecord ((physicalRun 1 256 unit_ring_positive unitClockState u).cfg i) :=
  unit_physical_preserved unit_ring_positive u unitClockState
    (fun _ => ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩) i

/-- Zero height occurs in every defaulted observed snapshot on every history. -/
theorem unit_observed_zero (u : List (Fin (2 * 2))) (ell : Nat) (i : Fin 2) :
    (observedSnapshot 1 256 unit_ring_positive unitClockState u ell i).x = 0 := by
  exact (unit_levelCurr_preserved unit_ring_positive
    (u.map physicalActivation) unitClockState
    (fun _ => ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩) i ell).1

/-- Each observed snapshot has two anchors, at every level and on every word. -/
theorem unit_observed_two_anchors (u : List (Fin (2 * 2))) (ell : Nat) :
    anchorCount unit_ring_positive
      (observedSnapshot 1 256 unit_ring_positive unitClockState u ell) = 2 := by
  simp [anchorCount, IsAnchor, unit_observed_zero]

/-- The non-single-anchor event has full mass at every scheduler deadline. -/
theorem unit_failure_full_mass (ell d : Nat) :
    Thru.wordSum (fun u : Thru.Word (2 * 2) =>
      if anchorCount unit_ring_positive
        (observedSnapshot 1 256 unit_ring_positive unitClockState u ell) ≠ 1
      then 1 else 0) d = 4 ^ d := by
  calc
    _ = Thru.wordSum (fun _ : Thru.Word (2 * 2) => 1) d := by
      apply Thru.wordSum_congr
      intro u
      simp only [unit_observed_two_anchors]
      decide
    _ = 4 ^ d := Thru.wordSum_const_one d

/-- Consequently the claimed quarter bound fails for every deadline. -/
theorem unit_failure_not_quarter (ell d : Nat) :
    ¬ (4 * Thru.wordSum (fun u : Thru.Word (2 * 2) =>
      if anchorCount unit_ring_positive
        (observedSnapshot 1 256 unit_ring_positive unitClockState u ell) ≠ 1
      then 1 else 0) d ≤ 4 ^ d) := by
  rw [unit_failure_full_mass]
  have hp : 0 < 4 ^ d := Nat.pow_pos (by decide)
  omega

/-- No physical word reaches a level carrying a single-anchor observation. -/
theorem unit_no_reached_single_anchor (u : Thru.Word (2 * 2)) :
    ¬ ∃ ell,
      (∀ i, ell ≤ (physicalRun 1 256 unit_ring_positive unitClockState u).lift i) ∧
      anchorCount unit_ring_positive
        (observedSnapshot 1 256 unit_ring_positive unitClockState u ell) = 1 := by
  rintro ⟨ell, _, hsingle⟩
  rw [unit_observed_two_anchors] at hsingle
  contradiction

end
end L4.Height
namespace L4.Height

open Classical
open L4.Compiler.Native

noncomputable section

/-- Actual paired letters produce the same activation history from every state. -/
private theorem clock_history_fixed {m B M : Nat} (hm : 0 < m)
    (x : OverrunState m) (u : Thru.Word (2 * m)) :
    overrunHistory (B := B) (M := M) hm clockAct x u =
      u.map (fun e => (physicalSite e, physicalBit e)) := by
  induction u generalizing x with
  | nil => rfl
  | cons e u ih =>
    simpa only [overrunHistory, clockAct, List.map_cons] using
      congrArg (List.cons (physicalSite e, physicalBit e))
        (ih (activate B M hm x.1 (physicalSite e) (physicalBit e),
          some (physicalSite e)))

/-- A coherent raw relift and its canonical representative have identical
lifted trajectories under the actual uniform scheduler. -/
theorem clock_run_canon_lift {m B M : Nat} (hm : 0 < m)
    (hM : ClockParams M) (s : WordState m) (hs : LegitCoset M hm s)
    (last : Option (Fin m)) (u : Thru.Word (2 * m)) :
    (Thru.runWord (clockNext (B := B) (M := M) hm) (s, last) u).1.lift =
      (Thru.runWord (clockNext (B := B) (M := M) hm)
        (canon M s, last) u).1.lift := by
  change (Thru.runWord (overrunNext (B := B) (M := M) hm clockAct)
    (s, last) u).1.lift =
      (Thru.runWord (overrunNext (B := B) (M := M) hm clockAct)
        (canon M s, last) u).1.lift
  rw [overrunHistory_run, overrunHistory_run,
    clock_history_fixed, clock_history_fixed]
  exact coset_syncRun_lift hM _ s (canon M s) hs (canon_legit hs) rfl

private theorem clock_activation_lift_mono {m B M : Nat} (hm : 0 < m)
    (s : WordState m) (i : Fin m) (b : Bool) (j : Fin m) :
    s.lift j ≤ (activate B M hm s i b).lift j := by
  by_cases he : j = i
  · subst j
    cases h : clockAction M hm s i <;> simp [activate, h, advanceLift]
  · simp [activate, he]

private theorem clock_run_lift_mono {m B M : Nat} (hm : 0 < m)
    (x : OverrunState m) (u : Thru.Word (2 * m)) (j : Fin m) :
    x.1.lift j ≤ (Thru.runWord (clockNext (B := B) (M := M) hm) x u).1.lift j := by
  induction u generalizing x with
  | nil => exact Nat.le_refl _
  | cons e u ih =>
    exact Nat.le_trans
      (clock_activation_lift_mono hm x.1 (physicalSite e) (physicalBit e) j)
      (ih (clockNext hm x e))

private theorem clock_run_append {m B M : Nat} (hm : 0 < m)
    (x : OverrunState m) (u v : Thru.Word (2 * m)) :
    Thru.runWord (clockNext (B := B) (M := M) hm) x (u ++ v) =
      Thru.runWord (clockNext (B := B) (M := M) hm)
        (Thru.runWord (clockNext (B := B) (M := M) hm) x u) v := by
  induction u generalizing x with
  | nil => rfl
  | cons e u ih => exact ih (clockNext hm x e)

private theorem clock_prefix_lift_le {m B M : Nat} (hm : 0 < m)
    (x : OverrunState m) (u : Thru.Word (2 * m)) (t : Nat) (j : Fin m) :
    (overrunStateAt (B := B) (M := M) hm clockAct x u t).1.lift j ≤
      (Thru.runWord (clockNext (B := B) (M := M) hm) x u).1.lift j := by
  have hh := clock_run_lift_mono (B := B) (M := M) hm
    (Thru.runWord (clockNext (B := B) (M := M) hm) x (u.take t)) (u.drop t) j
  rw [← clock_run_append, List.take_append_drop] at hh
  exact hh

private theorem clock_search_hit (p : Nat → Bool) (k : Nat)
    (h : overrunLeastTrue p k < k) : p (overrunLeastTrue p k) = true := by
  cases k with
  | zero => omega
  | succ k =>
    simp only [overrunLeastTrue] at h ⊢
    split at h <;> rename_i hp
    · simp [hp]
    · omega

/-- A target missed at the endpoint makes its capped clock equal to the word length. -/
private theorem clock_endpoint_miss_time {m B M : Nat} (hm : 0 < m)
    (x : OverrunState m) (base depth : Nat)
    (hb : ∀ j, base ≤ x.1.lift j) (u : Thru.Word (2 * m)) (i : Fin m)
    (hmiss : (Thru.runWord (clockNext (B := B) (M := M) hm) x u).1.lift i <
      base + depth) :
    finiteLevelTime (B := B) (M := M) hm clockAct x base u i depth = u.length := by
  have hd : depth ≠ 0 := by
    have hh := clock_run_lift_mono (B := B) (M := M) hm x u i
    have hi := hb i
    omega
  apply Nat.le_antisymm (finiteLevelTime_le_length hm clockAct x base u i depth)
  apply Nat.le_of_not_lt
  intro ht
  let p : Nat → Bool := fun k => decide
    (base + depth ≤
      (overrunStateAt (B := B) (M := M) hm clockAct x u k).1.lift i)
  have he : finiteLevelTime (B := B) (M := M) hm clockAct x base u i depth =
      overrunLeastTrue p u.length := by simp only [finiteLevelTime, hd, ↓reduceIte, p]
  rw [he] at ht
  have hh := of_decide_eq_true (clock_search_hit p u.length ht)
  have hm' := clock_prefix_lift_le (B := B) (M := M) hm x u
    (overrunLeastTrue p u.length) i
  change base + depth ≤ _ at hh
  omega

private theorem clock_site_le_maximum {n m : Nat}
    (T : Thru.Word n → Fin m → Nat → Nat)
    (depth : Nat) (u : Thru.Word n) (i : Fin m) :
    T u i depth ≤ clockMaximum T depth u := by
  have hmem : T u i depth ∈ (List.finRange m).map (fun j => T u j depth) :=
    List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
  unfold clockMaximum
  generalize (List.finRange m).map (fun j => T u j depth) = xs at hmem ⊢
  induction xs with
  | nil => simp at hmem
  | cons a xs ih =>
    simp only [List.mem_cons] at hmem
    simp only [Depth.foldMax, List.foldr_cons]
    rcases hmem with he | he
    · subst a
      exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih he) (Nat.le_max_right _ _)

private theorem clock_wordSum_mono_length {n : Nat}
    (f g : Thru.Word n → Nat) (d : Nat)
    (h : ∀ u, u.length = d → f u ≤ g u) :
    Thru.wordSum f d ≤ Thru.wordSum g d := by
  let f' := fun u => if u.length = d then f u else 0
  have he : Thru.wordSum f d = Thru.wordSum f' d := by
    apply Thru.wordSum_congr_length
    intro u hu
    simp only [f', hu, ↓reduceIte]
  rw [he]
  apply Thru.wordSum_mono
  intro u
  by_cases hu : u.length = d
  · simpa only [f', hu, ↓reduceIte] using h u hu
  · simp only [f', hu, ↓reduceIte]
    exact Nat.zero_le _

/-- The actual raw endpoint misses a chosen lifted target with probability
at most one quarter. The clock analysis uses the canonical representative,
while the event refers to the original raw relift. -/
theorem clock_coset_overrun_quarter {m B M L depth base : Nat}
    (hm : 0 < m) (hM : ClockParams M) (hL : 4 * m ≤ L)
    (s : WordState m) (hs : LegitCoset M hm s)
    (last : Option (Fin m)) (hb : ∀ j, base ≤ s.lift j)
    (hdepth : depth ≤ 2 ^ 25 * m) :
    4 * Thru.wordSum
      (fun u => if ∃ i,
        (Thru.runWord (clockNext (B := B) (M := M) hm) (s, last) u).1.lift i <
          base + depth then 1 else 0)
      (2 ^ 30 * L * m) ≤ (2 * m) ^ (2 ^ 30 * L * m) := by
  let y : OverrunState m := (canon M s, last)
  let d := 2 ^ 30 * L * m
  let T := finiteLevelTime (B := B) (M := M) hm clockAct y base
  have hmom : ∀ i z, Thru.MomentAt
      (overrunNext (B := B) (M := M) hm clockAct) (overrunServed i) L z :=
    clock_served_moment hm hL
  have hbound := overrun_chain hm clockAct y base hM (canon_legit hs)
    hb (by omega : 1 ≤ L) hmom hdepth
  apply Nat.le_trans (Nat.mul_le_mul_left 4 ?_) hbound
  apply clock_wordSum_mono_length
  intro u hu
  by_cases hmiss : ∃ i,
      (Thru.runWord (clockNext (B := B) (M := M) hm) (s, last) u).1.lift i <
        base + depth
  · have hmissCopy := hmiss
    obtain ⟨i, hi⟩ := hmissCopy
    have he := congrFun (clock_run_canon_lift (B := B) hm hM s hs last u) i
    have hiy : (Thru.runWord (clockNext (B := B) (M := M) hm) y u).1.lift i <
        base + depth := by
      dsimp only [y]
      rw [← he]
      exact hi
    have ht := clock_endpoint_miss_time hm y base depth hb u i hiy
    have hmax := clock_site_le_maximum T depth u i
    have htail : d ≤ clockMaximum T depth u := by
      change finiteLevelTime (B := B) (M := M) hm clockAct y base u i depth ≤ _ at hmax
      rw [ht, hu] at hmax
      exact hmax
    dsimp only [d,T] at htail
    simp only [hmiss, htail, ↓reduceIte, Nat.le_refl]
  · simp only [hmiss, ↓reduceIte]
    exact Nat.zero_le _

private theorem clock_list_minimum (a : Nat) (xs : List Nat) :
    ∃ v, (v = a ∨ v ∈ xs) ∧ v ≤ a ∧ ∀ b, b ∈ xs → v ≤ b := by
  induction xs generalizing a with
  | nil => exact ⟨a, Or.inl rfl, Nat.le_refl _, by simp⟩
  | cons b xs ih =>
    obtain ⟨v, hv, hvb, hvs⟩ := ih b
    by_cases ha : a ≤ v
    · refine ⟨a, Or.inl rfl, Nat.le_refl _, ?_⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact Nat.le_trans ha hvb
      · exact Nat.le_trans ha (hvs c hc)
    · refine ⟨v, Or.inr ?_, by omega, ?_⟩
      · rcases hv with hv | hv
        · exact List.mem_cons.mpr (Or.inl hv)
        · exact List.mem_cons.mpr (Or.inr hv)
      · intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hvb
        · exact hvs c hc

/-- Every finite nonempty collection of natural lifts has an attained minimum. -/
private theorem clock_minimum_exists {m : Nat} (hm : 0 < m)
    (lift : Fin m → Nat) : ∃ base, (∃ i, lift i = base) ∧ ∀ j, base ≤ lift j := by
  obtain ⟨base, hmem, _, hfloor⟩ :=
    clock_list_minimum (lift ⟨0, hm⟩) (List.ofFn lift)
  refine ⟨base, ?_, ?_⟩
  · rcases hmem with he | he
    · exact ⟨⟨0, hm⟩, he.symm⟩
    · obtain ⟨i, hi⟩ := List.mem_ofFn.mp he
      exact ⟨i, hi⟩
  · intro j
    exact hfloor _ (List.mem_ofFn.mpr ⟨j, rfl⟩)

/-- Recovery supplies one coherent relift and its attained minimum. Every
target within the stated depth budget has the raw endpoint quarter bound. -/
theorem clock_lgSet_overrun_quarter {m B M L : Nat}
    (hm : 0 < m) (hM : ClockParams M) (hmP : m < M / 2)
    (hL : 4 * m ≤ L) (x : OverrunState m)
    (hx : Recover.Chain.LgSet (clockChain (B := B) (M := M) hm) x) :
    ∃ (lift : Fin m → Nat) (base : Nat),
      (∃ i, lift i = base) ∧ (∀ j, base ≤ lift j) ∧
      LegitCoset M hm ⟨x.1.cfg, lift⟩ ∧
      ∀ depth, depth ≤ 2 ^ 25 * m →
        4 * Thru.wordSum
          (fun u => if ∃ i,
            (Thru.runWord (clockNext (B := B) (M := M) hm)
              (⟨x.1.cfg, lift⟩, x.2) u).1.lift i < base + depth then 1 else 0)
          (2 ^ 30 * L * m) ≤ (2 * m) ^ (2 ^ 30 * L * m) := by
  obtain ⟨lift, _, hc⟩ := lgSet_coset (clockChain (B := B) (M := M) hm)
    x hx hmP hM 0
  obtain ⟨base, hmin, hfloor⟩ := clock_minimum_exists hm lift
  refine ⟨lift, base, hmin, hfloor, hc, ?_⟩
  intro depth hd
  exact clock_coset_overrun_quarter hm hM hL ⟨x.1.cfg, lift⟩ hc x.2 hfloor hd

end
end L4.Height
namespace L4.Height

open Classical
open L4.Compiler.Native

noncomputable section

/-- Unit slopes along a nonwrapping right segment bound both endpoint differences. -/
private theorem clock_segment_bound {m : Nat} (hm : 0 < m)
    (lift : Fin m → Nat)
    (hnear : ∀ {i j}, Adjacent hm i j → Near (lift i) (lift j))
    (a : Nat) (ha : a < m) :
    ∀ d (had : a + d < m),
      lift ⟨a + d, had⟩ ≤ lift ⟨a, ha⟩ + d ∧
      lift ⟨a, ha⟩ ≤ lift ⟨a + d, had⟩ + d := by
  intro d
  induction d with
  | zero => intro had; simp
  | succ d ih =>
    intro had
    have hd : a + d < m := by omega
    have hh := ih hd
    let i : Fin m := ⟨a + d, hd⟩
    let j : Fin m := ⟨a + (d + 1), had⟩
    have he : j = right hm i := by
      apply Fin.ext
      change a + (d + 1) = (a + d + 1) % m
      rw [Nat.mod_eq_of_lt (by omega : a + d + 1 < m)]
      omega
    have hn := hnear (i := i) (j := j) (Or.inr he)
    change lift i ≤ lift j + 1 ∧ lift j ≤ lift i + 1 at hn
    change lift j ≤ lift ⟨a, ha⟩ + (d + 1) ∧
      lift ⟨a, ha⟩ ≤ lift j + (d + 1)
    change lift i ≤ lift ⟨a, ha⟩ + d ∧ lift ⟨a, ha⟩ ≤ lift i + d at hh
    omega

/-- Coherent unit slopes on a ring give spread at most its number of sites. -/
theorem clock_lift_spread {m : Nat} (hm : 0 < m)
    (lift : Fin m → Nat)
    (hnear : ∀ {i j}, Adjacent hm i j → Near (lift i) (lift j))
    (i j : Fin m) : lift j ≤ lift i + m := by
  by_cases hij : i.val ≤ j.val
  · have hd : i.val + (j.val - i.val) < m := by omega
    have h := (clock_segment_bound hm lift hnear i.val i.isLt
      (j.val - i.val) hd).1
    have he : (⟨i.val + (j.val - i.val), hd⟩ : Fin m) = j := by
      apply Fin.ext
      change i.val + (j.val - i.val) = j.val
      omega
    rw [he] at h
    change lift j ≤ lift i + (j.val - i.val) at h
    have hj := j.isLt
    omega
  · have hd : j.val + (i.val - j.val) < m := by omega
    have h := (clock_segment_bound hm lift hnear j.val j.isLt
      (i.val - j.val) hd).2
    have he : (⟨j.val + (i.val - j.val), hd⟩ : Fin m) = i := by
      apply Fin.ext
      change j.val + (i.val - j.val) = i.val
      omega
    rw [he] at h
    change lift j ≤ lift i + (i.val - j.val) at h
    have hi := i.isLt
    omega

/-- An attained minimum turns the slope diameter bound into a common upper bound. -/
theorem clock_lift_le_floor {m : Nat} (hm : 0 < m)
    (lift : Fin m → Nat)
    (hnear : ∀ {i j}, Adjacent hm i j → Near (lift i) (lift j))
    (base : Nat) (hmin : ∃ i, lift i = base) : ∀ j, lift j ≤ base + m := by
  obtain ⟨i, hi⟩ := hmin
  intro j
  simpa only [hi] using clock_lift_spread hm lift hnear i j

/-- A phase-zero frontier above the whole initial lift profile, with two
hundred additional levels of warmup, remains within the depth budget. -/
theorem clock_aligned_frontier {m : Nat} (hm : 0 < m) (base : Nat) :
    let ellzero := 32 * ((base + m + 200) / 32 + 1)
    ellzero % 32 = 0 ∧ base + m + 200 < ellzero ∧
      ellzero + 32 * (2 ^ 19 * m) - base ≤ 2 ^ 25 * m := by
  let a := base + m + 200
  have hrem : a % 32 < 32 := Nat.mod_lt a (by decide)
  have hdiv := Nat.mod_add_div a 32
  have hlo : a < 32 * (a / 32 + 1) := by omega
  have hhi : 32 * (a / 32 + 1) ≤ a + 32 := by omega
  change (32 * (a / 32 + 1)) % 32 = 0 ∧ a < 32 * (a / 32 + 1) ∧ _
  refine ⟨by simp, hlo, ?_⟩
  have hc : 32 * (2 ^ 19 * m) = 16777216 * m := by
    change 32 * (524288 * m) = 16777216 * m
    rw [← Nat.mul_assoc]
  change 32 * (a / 32 + 1) + 32 * (2 ^ 19 * m) - base ≤ 33554432 * m
  rw [hc]
  dsimp [a] at hhi
  omega

/-- Recovery admits a coherent relift and an aligned target above its entire
initial profile, including a fixed warmup margin and the logical round budget.
The target is reached by the physical deadline outside a quarter-mass event. -/
theorem clock_lgSet_aligned_overrun {m B M L : Nat}
    (hm : 0 < m) (hM : ClockParams M) (hmP : m < M / 2)
    (hL : 4 * m ≤ L) (x : OverrunState m)
    (hx : Recover.Chain.LgSet (clockChain (B := B) (M := M) hm) x) :
    ∃ (lift : Fin m → Nat) (base ellzero : Nat),
      (∃ i, lift i = base) ∧ (∀ j, base ≤ lift j) ∧
      LegitCoset M hm ⟨x.1.cfg, lift⟩ ∧ ellzero % 32 = 0 ∧
      (∀ i, lift i + 200 < ellzero) ∧
      ellzero + 32 * (2 ^ 19 * m) - base ≤ 2 ^ 25 * m ∧
      4 * Thru.wordSum
        (fun u => if ∃ i,
          (Thru.runWord (clockNext (B := B) (M := M) hm)
            (⟨x.1.cfg, lift⟩, x.2) u).1.lift i < ellzero + 32 * (2 ^ 19 * m)
          then 1 else 0)
        (2 ^ 30 * L * m) ≤ (2 * m) ^ (2 ^ 30 * L * m) := by
  obtain ⟨lift, base, hmin, hfloor, hc, hquarter⟩ :=
    clock_lgSet_overrun_quarter hm hM hmP hL x hx
  let ellzero := 32 * ((base + m + 200) / 32 + 1)
  obtain ⟨hzero, habove, hbudget⟩ := clock_aligned_frontier hm base
  have hspread := clock_lift_le_floor hm lift hc.near base hmin
  refine ⟨lift, base, ellzero, hmin, hfloor, hc, hzero, ?_, hbudget, ?_⟩
  · intro i
    have hi := hspread i
    omega
  · have hbase : base ≤ ellzero + 32 * (2 ^ 19 * m) := by omega
    have he : base + (ellzero + 32 * (2 ^ 19 * m) - base) =
        ellzero + 32 * (2 ^ 19 * m) := by omega
    have hq := hquarter (ellzero + 32 * (2 ^ 19 * m) - base) hbudget
    simpa only [he] using hq

end
end L4.Height
namespace L4.Height.ClockHead

open L4.Height
open Classical
open L4.Compiler.Native

noncomputable def reachedBad {m : Nat}
    (B M base Q : Nat) (hm : 0 < m) (s : WordState m)
    (u : List (Fin (2 * m))) : Prop :=
  (∀ i, base + 32 * Q ≤ (physicalRun B M hm s u).lift i) ∧
    anchorCount hm (observedSnapshot B M hm s u (base + 32 * Q)) ≠ 1

theorem warm_reached_bad_quarter {m B : Nat}
    (hm : 0 < m) (hmb : m < B)
    (M base : Nat) (hM : ClockParams M)
    (hdiv : 32 ∣ M / 2) (hzero : base % 32 = 0)
    (start : Fin m → Snapshot) (s : WordState m)
    (hs : Bounded B start) (hleg : Legit M hm s)
    (hstart : StartConsistent B M base hm falseChoices start s)
    (t : Nat) :
    4 * wordSum
      (fun u => if reachedBad B M base (2 ^ 19 * m) hm s u then 1 else 0)
      t ≤ (2 * m) ^ t := by
  classical
  have hQ : 0 < 2 ^ 19 * m := Nat.mul_pos (by decide) hm
  apply logical_physical_quarter hm hmb start hs M base s t
    (reachedBad B M base (2 ^ 19 * m) hm s)
  intro u _hu hE
  exact physical_event B M base (2 ^ 19 * m) hm hM hdiv hzero hQ
    start s hleg hstart u hE

end L4.Height.ClockHead
namespace L4.Height.ClockHead

open L4.Height
open L4.Compiler.Native

/-- Representation is required only for snapshots at or above the virtual
base. Below-base snapshots may still be arbitrary. -/
def AboveRep {m : Nat} (B M base : Nat) (hm : 0 < m)
    (choices : Nat → Fin m → Bool) (start : Fin m → Snapshot)
    (s : WordState m) : Prop :=
  (∀ i, base ≤ s.lift i → (s.cfg i).curr =
    syncLevels B M base hm choices start (s.lift i - base) i) ∧
  (∀ i, base < s.lift i → (s.cfg i).prior =
    syncLevels B M base hm choices start (s.lift i - base - 1) i)

private theorem activate_lift_step {m B M : Nat} (hm : 0 < m)
    (s : WordState m) (e : Activation m) (i : Fin m) :
    (activate B M hm s e.1 e.2).lift i = s.lift i ∨
      (activate B M hm s e.1 e.2).lift i = s.lift i + 1 := by
  by_cases hi : i = e.1
  · subst i
    cases ha : clockAction M hm s e.1 <;>
      simp [activate, ha, advanceLift]
  · left
    simp [activate, hi]

private theorem activate_lift_mono {m B M : Nat} (hm : 0 < m)
    (s : WordState m) (e : Activation m) (i : Fin m) :
    s.lift i ≤ (activate B M hm s e.1 e.2).lift i := by
  rcases activate_lift_step (B := B) (M := M) hm s e i with h | h <;> omega

/-- The history argument is matched before levelCurr checks the present
lift, so this small lemma must split its possibly unknown list. -/
private theorem levelCurr_at_current {m : Nat} (B M : Nat) (hm : 0 < m)
    (h : List (Activation m)) (s : WordState m) (i : Fin m) (ell : Nat)
    (he : s.lift i = ell) :
    levelCurr B M hm h s i ell = some (s.cfg i).curr := by
  cases h <;> simp [levelCurr, he]

/-- A legitimate activation that does not raise this site's lift cannot
change its current snapshot. -/
private theorem activate_curr_same_level {m B M : Nat}
    (hm : 0 < m) (hM : ClockParams M)
    (s : WordState m) (hs : Legit M hm s) (e : Activation m)
    (i : Fin m)
    (he : (activate B M hm s e.1 e.2).lift i = s.lift i) :
    ((activate B M hm s e.1 e.2).cfg i).curr = (s.cfg i).curr := by
  by_cases hi : i = e.1
  · subst i
    rcases action_inc_or_hold hM hm s hs e.1 with h | h
    · simp [activate, h, advanceLift] at he
    · rw [activate_of_hold hm s e.1 e.2 h]
  · simp [activate, hi]

private theorem levelCurr_none_below {m B M : Nat}
    (hm : 0 < m) (h : List (Activation m)) (s : WordState m)
    (i : Fin m) (ell : Nat) (hbelow : ell < s.lift i) :
    levelCurr B M hm h s i ell = none := by
  induction h generalizing s with
  | nil => simp [levelCurr, show s.lift i ≠ ell by omega]
  | cons e h ih =>
      have hmono := activate_lift_mono (B := B) (M := M) hm s e i
      have hnext : ell < (activate B M hm s e.1 e.2).lift i := by omega
      simpa [levelCurr, show s.lift i ≠ ell by omega] using
        ih (activate B M hm s e.1 e.2) hnext

private theorem above_neighborView {m B M base : Nat}
    (hM : ClockParams M) (hm : 0 < m)
    (choices : Nat → Fin m → Bool) (start : Fin m → Snapshot)
    (s : WordState m) (hleg : Legit M hm s)
    (hrep : AboveRep B M base hm choices start s)
    (i j : Fin m) (n : Nat)
    (hilevel : s.lift i = base + n)
    (hfront : s.lift j = s.lift i ∨ s.lift j = s.lift i + 1) :
    neighborView (s.cfg i).tick (s.cfg j) =
      syncLevels B M base hm choices start n j := by
  rcases hfront with hsame | hahead
  · have hticksame : (s.cfg j).tick = (s.cfg i).tick := by
      rw [hleg.2.1 j, hleg.2.1 i, hsame]
    have hj : base ≤ s.lift j := by omega
    have hoff : s.lift j - base = n := by omega
    simp [neighborView, hticksame, hrep.1 j hj, hoff]
  · have htickahead : (s.cfg j).tick = successor M (s.cfg i).tick := by
      rw [hleg.2.1 j, hleg.2.1 i, hahead, clockOf_succ hM]
    have hwindow : M / 2 ≤ (s.cfg i).tick ∧ (s.cfg i).tick < M := by
      rw [hleg.2.1 i]
      exact clockOf_window hM
    have hne : (s.cfg j).tick ≠ (s.cfg i).tick := by
      rw [htickahead]
      exact successor_ne_self hM hwindow
    have hj : base < s.lift j := by omega
    have hoff : s.lift j - base - 1 = n := by omega
    simp [neighborView, hne, hrep.2 j hj, hoff]

/-- The only extra data needed when crossing the base is the actual
snapshot published at that base. -/
theorem aboveRep_activate {m B M base : Nat}
    (hM : ClockParams M) (hm : 0 < m)
    (choices : Nat → Fin m → Bool) (start : Fin m → Snapshot)
    (s : WordState m) (hleg : Legit M hm s)
    (hrep : AboveRep B M base hm choices start s)
    (i : Fin m) (delta : Bool)
    (hpin : ∀ j, (activate B M hm s i delta).lift j = base →
      ((activate B M hm s i delta).cfg j).curr = start j)
    (hchoice :
      match clockAction M hm s i with
      | .inc _ => clockOf M (s.lift i) % 32 ≠ 1 ∨
          delta = choices (s.lift i) i
      | _ => True) :
    AboveRep B M base hm choices start (activate B M hm s i delta) := by
  have hnormal := nativeClock_normal hM hm s hleg i
  cases hval : canAdvanceBool hm s.lift i with
  | false =>
      have hact : clockAction M hm s i = ClockAction.hold := by
        simpa [hval] using hnormal
      rw [activate_of_hold hm s i delta hact]
      exact hrep
  | true =>
      have hcan := (canAdvanceBool_eq_true hm s.lift i).1 hval
      have hact : clockAction M hm s i =
          ClockAction.inc (clockOf M (s.lift i + 1)) := by
        simpa [hval] using hnormal
      have hchoiceInc : clockOf M (s.lift i) % 32 ≠ 1 ∨
          delta = choices (s.lift i) i := by
        simpa [hact] using hchoice
      let n := s.lift i - base
      have hnewlift : (activate B M hm s i delta).lift i = s.lift i + 1 := by
        simp [activate, hact, advanceLift]
      have hnewcurr : base ≤ s.lift i →
          ((activate B M hm s i delta).cfg i).curr =
            syncLevels B M base hm choices start (n + 1) i := by
        intro hbase
        have hilevel : s.lift i = base + n := by dsimp [n]; omega
        have hcenter : (s.cfg i).curr =
            syncLevels B M base hm choices start n i := hrep.1 i hbase
        have hleft := above_neighborView hM hm choices start s hleg hrep
          i (left hm i) n hilevel hcan.1
        have hright := above_neighborView hM hm choices start s hleg hrep
          i (right hm i) n hilevel hcan.2
        have hdelta :
            phaseUpdate B ((s.cfg i).tick % 32)
              (neighborView (s.cfg i).tick (s.cfg (left hm i))) (s.cfg i).curr
              (neighborView (s.cfg i).tick (s.cfg (right hm i))) delta =
            phaseUpdate B ((s.cfg i).tick % 32)
              (neighborView (s.cfg i).tick (s.cfg (left hm i))) (s.cfg i).curr
              (neighborView (s.cfg i).tick (s.cfg (right hm i)))
              (choices (s.lift i) i) := by
          rcases hchoiceInc with hp | hd
          · apply phaseUpdate_delta_irrelevant
            rw [hleg.2.1 i]
            exact hp
          · rw [hd]
        calc
          ((activate B M hm s i delta).cfg i).curr =
              phaseUpdate B ((s.cfg i).tick % 32)
                (neighborView (s.cfg i).tick (s.cfg (left hm i))) (s.cfg i).curr
                (neighborView (s.cfg i).tick (s.cfg (right hm i))) delta := by
                  simp [activate, hact, finishNative]
          _ = phaseUpdate B ((s.cfg i).tick % 32)
                (neighborView (s.cfg i).tick (s.cfg (left hm i))) (s.cfg i).curr
                (neighborView (s.cfg i).tick (s.cfg (right hm i)))
                (choices (s.lift i) i) := hdelta
          _ = syncLevels B M base hm choices start (n + 1) i := by
              rw [hleft, hcenter, hright, hleg.2.1 i, hilevel]
              simp [syncLevels, phaseStep]
      refine ⟨?_, ?_⟩
      · intro j hj
        by_cases hji : j = i
        · subst j
          by_cases hb : base ≤ s.lift i
          · rw [hnewlift]
            have hoff : s.lift i + 1 - base = n + 1 := by dsimp [n]; omega
            rw [hoff]
            exact hnewcurr hb
          · have he : (activate B M hm s i delta).lift i = base := by
              rw [hnewlift] at hj ⊢
              omega
            rw [he, Nat.sub_self]
            exact hpin i he
        · simp [activate, hji] at hj ⊢
          exact hrep.1 j hj
      · intro j hj
        by_cases hji : j = i
        · subst j
          rw [hnewlift] at hj ⊢
          have hb : base ≤ s.lift i := by omega
          have hoff : s.lift i + 1 - base - 1 = n := by dsimp [n]; omega
          rw [hoff]
          have hc : ((activate B M hm s i delta).cfg i).prior =
              (s.cfg i).curr := by simp [activate, hact, finishNative]
          exact hc.trans (hrep.1 i hb)
        · simp [activate, hji] at hj ⊢
          exact hrep.2 j hj

/-- Compare a history to a virtual slice. Initial heights may have arbitrary
skew. A base observation is pinned to start, and no lower-bound condition
on all current lifts is needed. -/
theorem levelCurr_eq_sync_above {m B M base : Nat}
    (hM : ClockParams M) (hm : 0 < m)
    (choices : Nat → Fin m → Bool) (start : Fin m → Snapshot)
    (h : List (Activation m)) (s : WordState m)
    (hleg : Legit M hm s)
    (hrep : AboveRep B M base hm choices start s)
    (hhonor : Honors B M hm choices s h)
    (hslice : ∀ i value,
      levelCurr B M hm h s i base = some value → value = start i)
    (i : Fin m) (n : Nat) (value : Snapshot)
    (hvalue : levelCurr B M hm h s i (base + n) = some value) :
    value = syncLevels B M base hm choices start n i := by
  induction h generalizing s with
  | nil =>
      by_cases heq : s.lift i = base + n
      · have hv : (s.cfg i).curr = value := by
          simpa [levelCurr, heq] using hvalue
        have hb : base ≤ s.lift i := by omega
        have hoff : s.lift i - base = n := by omega
        simpa [hoff, hv] using hrep.1 i hb
      · simp [levelCurr, heq] at hvalue
  | cons e h ih =>
      by_cases heq : s.lift i = base + n
      · have hv : (s.cfg i).curr = value := by
          simpa [levelCurr, heq] using hvalue
        have hb : base ≤ s.lift i := by omega
        have hoff : s.lift i - base = n := by omega
        simpa [hoff, hv] using hrep.1 i hb
      · let next := activate B M hm s e.1 e.2
        have hpin : ∀ j, next.lift j = base → (next.cfg j).curr = start j := by
          intro j hj
          by_cases hold : s.lift j = base
          · have he : next.lift j = s.lift j := hj.trans hold.symm
            have hc := activate_curr_same_level hm hM s hleg e j he
            have hstart := hrep.1 j (show base ≤ s.lift j by omega)
            have hoff : s.lift j - base = 0 := by omega
            simpa [next, hoff, syncLevels] using hc.trans hstart
          · apply hslice j (next.cfg j).curr
            have hn := levelCurr_at_current B M hm h next j base hj
            simpa only [levelCurr, if_neg hold] using hn
        have htailSlice : ∀ j v,
            levelCurr B M hm h next j base = some v → v = start j := by
          intro j v hv
          by_cases hold : s.lift j = base
          · have hmono := activate_lift_mono (B := B) (M := M) hm s e j
            have hlow : base ≤ next.lift j := by dsimp [next]; omega
            by_cases hn : next.lift j = base
            · have hc : (next.cfg j).curr = v := by
                rw [levelCurr_at_current B M hm h next j base hn] at hv
                exact Option.some.inj hv
              exact hc.symm.trans (hpin j hn)
            · have hgt : base < next.lift j := by omega
              rw [levelCurr_none_below hm h next j base hgt] at hv
              cases hv
          · apply hslice j v
            simpa [levelCurr, hold, next] using hv
        change
          (match clockAction M hm s e.1 with
           | .inc _ => clockOf M (s.lift e.1) % 32 ≠ 1 ∨
               e.2 = choices (s.lift e.1) e.1
           | _ => True) ∧ Honors B M hm choices next h at hhonor
        have hnextRep := aboveRep_activate hM hm choices start s hleg hrep
          e.1 e.2 hpin hhonor.1
        have hnextValue : levelCurr B M hm h next i (base + n) = some value := by
          simpa [levelCurr, heq, next] using hvalue
        exact ih next (legit_activate hM hm s hleg e.1 e.2)
          hnextRep hhonor.2 htailSlice hnextValue

/-- Taking the actual observed base slice removes the special simultaneous
warm-start premise completely from the deterministic comparison. -/
theorem virtual_slice_comparison {m B M base : Nat}
    (hM : ClockParams M) (hm : 0 < m)
    (choices : Nat → Fin m → Bool)
    (h : List (Activation m)) (s : WordState m)
    (hleg : Legit M hm s) (hbelow : ∀ i, s.lift i < base)
    (hhonor : Honors B M hm choices s h)
    (i : Fin m) (n : Nat) (value : Snapshot)
    (hvalue : levelCurr B M hm h s i (base + n) = some value) :
    value = syncLevels B M base hm choices
      (fun j => (levelCurr B M hm h s j base).getD ({} : Snapshot)) n i := by
  let start : Fin m → Snapshot :=
    fun j => (levelCurr B M hm h s j base).getD ({} : Snapshot)
  have hrep : AboveRep B M base hm choices start s := by
    constructor
    · intro j hj
      have := hbelow j
      omega
    · intro j hj
      have := hbelow j
      omega
  apply levelCurr_eq_sync_above hM hm choices start h s hleg hrep hhonor
  · intro j v hv
    simp [start, hv]
  · exact hvalue

private theorem roundBits_agree {m : Nat}
    (f g : Nat → Fin m → Bool) (base : Nat) :
    ∀ Q, (∀ k, k < Q → f (base + 32 * k + 1) = g (base + 32 * k + 1)) →
      roundBits f base Q = roundBits g base Q := by
  intro Q
  induction Q with
  | zero => intro _; rfl
  | succ Q ih =>
      intro h
      have hp : ∀ k, k < Q → f (base + 32 * k + 1) =
          g (base + 32 * k + 1) := fun k hk => h k (by omega)
      change roundBits f base Q ++ [f (base + 32 * Q + 1)] =
        roundBits g base Q ++ [g (base + 32 * Q + 1)]
      rw [ih hp, h Q (by omega)]

/-- The virtual slice comparison in the exact logical runRounds form used
by physical_event. Its start slice depends on u: counting that varying
slice still needs the separate fiber argument. -/
theorem virtual_physical_observation {m B M base : Nat}
    (hM : ClockParams M) (hm : 0 < m)
    (hdiv : 32 ∣ M / 2) (hzero : base % 32 = 0)
    (Q : Nat) (s : WordState m) (u : List (Fin (2 * m)))
    (hleg : Legit M hm s) (hbelow : ∀ i, s.lift i < base)
    (i : Fin m) (value : Snapshot)
    (hvalue : levelCurr B M hm (u.map physicalActivation) s i
      (base + 32 * Q) = some value) :
    value = runRounds B hm
      (roundBits (physicalChoices B M base Q hm s u) base Q)
      (observedSnapshot B M hm s u base) i := by
  let choices := strongChoices B M base Q hm s u
  have hv := virtual_slice_comparison hM hm choices
    (u.map physicalActivation) s hleg hbelow
    (honors_strongChoices B M base Q hm s u) i (32 * Q) value hvalue
  have hphase : ∀ n, clockOf M (base + n) % 32 = n % 32 :=
    fun _ => clockOf_mod_phase hdiv hzero
  have hsync := syncLevels_runRounds (B := B) (M := M) (ellzero := base)
    (k := Q) hm choices (observedSnapshot B M hm s u base) hphase
  have hround : roundBits choices base Q =
      roundBits (physicalChoices B M base Q hm s u) base Q := by
    apply roundBits_agree
    intro k hk
    funext j
    let r : Fin Q := ⟨k, hk⟩
    exact (strongChoices_target B M base Q hm s u r j).trans
      (physicalChoices_target B M base Q hm s u r j).symm
  change value = syncLevels B M base hm choices
    (observedSnapshot B M hm s u base) (32 * Q) i at hv
  rw [hsync, hround] at hv
  exact hv

end L4.Height.ClockHead
namespace L4.Height

open Classical
open L4.Compiler.Native

noncomputable section

/-- Change only the stored lift, by a fixed independently chosen offset per site. -/
def liftOffset {m : Nat} (offset : Fin m → Nat) (s : WordState m) : WordState m where
  cfg := s.cfg
  lift i := s.lift i + offset i

/-- Stored lift offsets do not alter the literal native clock action. -/
theorem liftOffset_activate {m B M : Nat} (hm : 0 < m)
    (offset : Fin m → Nat) (s : WordState m) (i : Fin m) (b : Bool) :
    activate B M hm (liftOffset offset s) i b =
      liftOffset offset (activate B M hm s i b) := by
  apply wordState_ext
  · rfl
  · funext j
    by_cases he : j = i
    · subst j
      simp only [activate, setAt_self, liftOffset]
      change advanceLift (clockAction M hm s i) (s.lift i + offset i) =
        advanceLift (clockAction M hm s i) (s.lift i) + offset i
      cases ha : clockAction M hm s i <;>
        simp [advanceLift, ha, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    · simp [activate, liftOffset, setAt, he]

/-- Every physical history commutes with arbitrary fixed sitewise lift offsets. -/
theorem physicalRun_liftOffset {m B M : Nat} (hm : 0 < m)
    (offset : Fin m → Nat) (s : WordState m) (u : List (Fin (2 * m))) :
    physicalRun B M hm (liftOffset offset s) u =
      liftOffset offset (physicalRun B M hm s u) := by
  induction u generalizing s with
  | nil => rfl
  | cons e u ih =>
      change physicalRun B M hm
        (activate B M hm (liftOffset offset s) (physicalSite e) (physicalBit e)) u =
        liftOffset offset (physicalRun B M hm
          (activate B M hm s (physicalSite e) (physicalBit e)) u)
      rw [liftOffset_activate]
      exact ih _

/-- The native endpoint is identical under every physical scheduler word. -/
theorem physicalRun_liftOffset_cfg {m B M : Nat} (hm : 0 < m)
    (offset : Fin m → Nat) (s : WordState m) (u : List (Fin (2 * m))) :
    (physicalRun B M hm (liftOffset offset s) u).cfg =
      (physicalRun B M hm s u).cfg := by
  rw [physicalRun_liftOffset]
  rfl

/-- Offset the lifted component while preserving the last-publication marker. -/
def clockOffset {m : Nat} (offset : Fin m → Nat) (s : OverrunState m) :
    OverrunState m := (liftOffset offset s.1, s.2)

/-- The complete clock-chain step commutes with fixed sitewise offsets. -/
theorem clockOffset_next {m B M : Nat} (hm : 0 < m)
    (offset : Fin m → Nat) (s : OverrunState m) (e : Fin (2 * m)) :
    clockNext (B := B) (M := M) hm (clockOffset offset s) e =
      clockOffset offset (clockNext (B := B) (M := M) hm s e) := by
  change (activate B M hm (liftOffset offset s.1)
      (physicalSite e) (physicalBit e), some (physicalSite e)) =
    (liftOffset offset (activate B M hm s.1
      (physicalSite e) (physicalBit e)), some (physicalSite e))
  rw [liftOffset_activate]

/-- Every scheduler word preserves exactly the same native execution and marker. -/
theorem clockOffset_run {m B M : Nat} (hm : 0 < m)
    (offset : Fin m → Nat) (s : OverrunState m) (u : Thru.Word (2 * m)) :
    Thru.runWord (clockNext (B := B) (M := M) hm) (clockOffset offset s) u =
      clockOffset offset (Thru.runWord (clockNext (B := B) (M := M) hm) s u) := by
  induction u generalizing s with
  | nil => rfl
  | cons e u ih =>
      change Thru.runWord (clockNext (B := B) (M := M) hm)
        (clockNext (B := B) (M := M) hm (clockOffset offset s) e) u =
        clockOffset offset (Thru.runWord (clockNext (B := B) (M := M) hm)
          (clockNext (B := B) (M := M) hm s e) u)
      rw [clockOffset_next]
      exact ih _

private theorem offset_pair_positive : 0 < (2 : Nat) := by decide

/-- Flat native clock with its coherent zero lift. -/
def offsetFlatClock : WordState 2 where
  cfg _ := ⟨128, false, {}, {}⟩
  lift _ := 0

/-- A permanent eight-level discrepancy on the second site. -/
def offsetPair : Fin 2 → Nat := fun i => 8 * i.val

/-- The underlying flat clock is legitimately lifted. -/
theorem offsetFlatClock_legit : Legit 256 offset_pair_positive offsetFlatClock := by
  refine ⟨fun _ => rfl, fun _ => rfl, ?_⟩
  intro i j _
  change Near 0 0
  exact ⟨by omega, by omega⟩

private theorem offset_physical_legit {m B M : Nat} (hm : 0 < m)
    (hM : ClockParams M) (s : WordState m) (hs : Legit M hm s)
    (u : List (Fin (2 * m))) : Legit M hm (physicalRun B M hm s u) := by
  induction u generalizing s with
  | nil => exact hs
  | cons e u ih =>
      exact ih (physicalNext B M hm s e)
        (legit_activate hM hm s hs (physicalSite e) (physicalBit e))

/-- The offset state starts in the native legitimate target at height modulus sixteen. -/
theorem offsetClock_lgSet :
    Recover.Chain.LgSet
      (clockChain (B := 16) (M := 256) offset_pair_positive)
      (liftOffset offsetPair offsetFlatClock, none) := by
  refine ⟨fun _ => rfl, ?_, ?_⟩
  · intro i hr
    change false = true at hr
    cases hr
  · intro i
    change 128 < 256 ∧ (false = true → 128 < 256 / 2)
    decide

/-- The two stored counters remain separated by more than one on every history. -/
theorem offsetClock_never_near (u : List (Fin (2 * 2))) :
    ¬ Near
      ((physicalRun 16 256 offset_pair_positive
        (liftOffset offsetPair offsetFlatClock) u).lift 0)
      ((physicalRun 16 256 offset_pair_positive
        (liftOffset offsetPair offsetFlatClock) u).lift 1) := by
  have hleg := offset_physical_legit (B := 16) offset_pair_positive
    (show ClockParams 256 from ⟨by decide, by decide⟩)
    offsetFlatClock offsetFlatClock_legit u
  have hadj : Adjacent offset_pair_positive (0 : Fin 2) (1 : Fin 2) :=
    Or.inr rfl
  have hnear := hleg.2.2 hadj
  rw [physicalRun_liftOffset]
  change ¬ Near
    ((physicalRun 16 256 offset_pair_positive offsetFlatClock u).lift 0 + 0)
    ((physicalRun 16 256 offset_pair_positive offsetFlatClock u).lift 1 + 8)
  unfold Near at hnear ⊢
  omega

/-- No finite physical history ever repairs the stored lift into a legitimate lift. -/
theorem offsetClock_never_legit (u : List (Fin (2 * 2))) :
    ¬ Legit 256 offset_pair_positive
      (physicalRun 16 256 offset_pair_positive
        (liftOffset offsetPair offsetFlatClock) u) := by
  intro h
  exact offsetClock_never_near u
    (h.2.2 (i := (0 : Fin 2)) (j := (1 : Fin 2)) (Or.inr rfl))

/-- No history reaches any common warm frontier, for any choice table or start vector. -/
theorem offsetClock_never_consistent (u : List (Fin (2 * 2)))
    (ell : Nat) (choices : Nat → Fin 2 → Bool) (start : Fin 2 → Snapshot) :
    ¬ StartConsistent 16 256 ell offset_pair_positive choices start
      (physicalRun 16 256 offset_pair_positive
        (liftOffset offsetPair offsetFlatClock) u) := by
  intro h
  apply offsetClock_never_near u
  have ha := h (0 : Fin 2)
  have hb := h (1 : Fin 2)
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    rcases ha with ⟨ha, _⟩ <;> rcases hb with ⟨hb, _⟩ <;>
    unfold Near <;> omega

/-- Stored lift failure coexists with exact equality of all native word endpoints. -/
theorem offsetClock_native_projection (u : List (Fin (2 * 2))) :
    (physicalRun 16 256 offset_pair_positive
      (liftOffset offsetPair offsetFlatClock) u).cfg =
    (physicalRun 16 256 offset_pair_positive offsetFlatClock u).cfg :=
  physicalRun_liftOffset_cfg offset_pair_positive offsetPair offsetFlatClock u

end
end L4.Height
namespace L4.Height

open L4.Compiler.Native

/-- Identifying the physical packing size with the paired alphabet forces
the decoded height modulus to be one whenever the native width is used. -/
theorem paired_packing_heightMod {m r : Nat} (hm : 0 < m) (hw : m*r ≤ 2*m) :
    r ≤ 2 ∧ heightMod r = 1 := by
  rw [Nat.mul_comm 2 m] at hw
  have hr := Nat.le_of_mul_le_mul_left hw hm
  exact ⟨hr, by simp [heightMod, Nat.sub_eq_zero_of_le hr]⟩

/-- At the headline service scale, a positive width and the packing bound
supply the concrete moment's length requirement. -/
theorem clock_service_scale {m r bL ringN L : Nat} (hr : 0 < r)
    (hw : m*r ≤ ringN) (hL : L = 2^(5*bL+34)*ringN*r) : 4*m ≤ L := by
  have hmr : m ≤ m*r := by simpa using Nat.mul_le_mul_left m hr
  have hc : 4 ≤ 2^(5*bL+34) := by
    rw [Nat.pow_add]
    have hp : 0 < 2^(5*bL) := Nat.pow_pos (by decide)
    change 4 ≤ 2^(5*bL)*17179869184
    omega
  have hn := Nat.mul_le_mul hc (Nat.le_trans hmr hw)
  rw [hL]
  exact Nat.le_trans hn (by simpa using Nat.mul_le_mul_left (2^(5*bL+34)*ringN) hr)

/-- All well-formed starts reach native clock legitimacy with the repair
budget once the physical service scale is substituted. -/
theorem clock_layer_repair {m B M L : Nat} (hm : 0 < m)
    (hM : ClockParams M) (hd : m/2 < M/2) (hL : 4*m ≤ L) (x : OverrunState m)
    (hx : Recover.StageTwo.WellFormed M x.1.cfg) :
    IIDExpectedHittingTimeAtMost (clockNext (B := B) (M := M) hm)
      (Recover.Chain.LgSet (clockChain (B := B) (M := M) hm)) x (17*L*m) := by
  apply clock_repair (clockChain (B := B) (M := M) hm) _ hd (by omega) hm
    (clock_served_moment hm hL) x hx
  exact ⟨by have := hM.1; omega, hM.2⟩

end L4.Height
namespace L4.Height.ClockHead

open L4.Compiler.Native

/-- The native action does not consult the auxiliary lift or the last mark.
Replacing either at a repair cut preserves the whole native execution. -/
theorem clock_run_records {m B M : Nat} (hm : 0 < m)
    (x y : OverrunState m) (u : List (Fin (2*m))) (he : x.1.cfg = y.1.cfg) :
    (runWord (clockNext (B := B) (M := M) hm) x u).1.cfg =
      (runWord (clockNext (B := B) (M := M) hm) y u).1.cfg := by
  induction u generalizing x y with
  | nil => exact he
  | cons e u ih =>
    apply ih
    change (activate B M hm x.1 (physicalSite e) (physicalBit e)).cfg =
      (activate B M hm y.1 (physicalSite e) (physicalBit e)).cfg
    rw [clock_activate_cfg, clock_activate_cfg, he]

/-- A coherent raw relift has the same first observations as its canonical
representative at every level, including levels missed by the word. -/
theorem clock_canon_observed {m B M : Nat} (hm : 0 < m)
    (hM : ClockParams M) (hp : 32 ∣ M/2) (s : WordState m) (hc : LegitCoset M hm s)
    (u : List (Fin (2*m))) (ell : Nat) :
    observedSnapshot B M hm (canon M s) u ell = observedSnapshot B M hm s u ell := by
  funext i
  unfold observedSnapshot
  rw [canon_levelCurr hM _ s hc (updatesAgree_of_dvd hM hp _ s hc)]

/-- In the actual coset records, every target observation evolves from the
word's actual base slice by the rounds revealed in the canonical execution. -/
theorem clock_coset_virtual_observation {m B M base : Nat}
    (hm : 0 < m) (hM : ClockParams M)
    (hp : 32 ∣ M/2) (hz : base%32 = 0) (q : Nat)
    (s : WordState m) (hc : LegitCoset M hm s) (hbelow : ∀ i, s.lift i < base)
    (u : List (Fin (2*m))) (i : Fin m) (v : Snapshot)
    (ho : levelCurr B M hm (u.map physicalActivation) s i (base+32*q) = some v) :
    v = runRounds B hm (roundBits (physicalChoices B M base q hm (canon M s) u) base q)
      (observedSnapshot B M hm s u base) i := by
  rw [← clock_canon_observed hm hM hp s hc]
  apply virtual_physical_observation hM hm hp hz q (canon M s) u (canon_legit hc) hbelow
  rw [canon_levelCurr hM _ s hc (updatesAgree_of_dvd hM hp _ s hc)]
  exact ho

end L4.Height.ClockHead

namespace L4.Height.ClockHead

open L4.Compiler.Native

/-- A strictly higher virtual base can never satisfy the simultaneous
warm-start predicate on the unchanged clock, even after canonicalization. -/
theorem no_initial_warm_frontier {m : Nat} (B M base : Nat) (hm : 0 < m)
    (s : WordState m) (k : Fin m) (hk : s.lift k < base)
    (c : Nat → Fin m → Bool) (start : Fin m → Snapshot) :
    ¬ StartConsistent B M base hm c start s := by
  intro h
  rcases h k with h | h <;> have h' := h.1 <;> omega

theorem flat_higher_frontier_counterexample (c : Nat → Fin 2 → Bool)
    (start : Fin 2 → Snapshot) :
    Legit 256 unit_ring_positive unitClockState ∧
      ¬ StartConsistent 16 256 32 unit_ring_positive c start unitClockState :=
  ⟨unit_clock_legit, no_initial_warm_frontier 16 256 32 unit_ring_positive
    unitClockState 0 (by decide) c start⟩

end L4.Height.ClockHead

namespace L4.Height.ClockHead

/-- One lift at a native recovery cut represents all future words. The native
records of the relifted chain are exactly those of the original chain, and
phase alignment gives equality of the complete canonical records. -/
theorem clock_trial_projection {m B M : Nat} (hm : 0 < m) (hM : ClockParams M)
    (hmP : m < M/2) (hp : 32 ∣ M/2) (x : OverrunState m)
    (hx : Recover.Chain.LgSet (clockChain (B := B) (M := M) hm) x) :
    ∃ lift : Fin m → Nat,
      let s : WordState m := ⟨x.1.cfg, lift⟩
      LegitCoset M hm s ∧ Legit M hm (canon M s) ∧
      ∀ u : List (Fin (2*m)),
        (runWord (clockNext (B := B) (M := M) hm) x u).1.cfg =
          (runWord (clockNext (B := B) (M := M) hm) (s,x.2) u).1.cfg ∧
        canon M (syncRun B M hm (u.map physicalActivation) s) =
          syncRun B M hm (u.map physicalActivation) (canon M s) := by
  obtain ⟨lift, _, hc, hl, _, halls⟩ := lgSet_canon_legit
    (clockChain (B := B) (M := M) hm) x hx hmP hM 0
  exact ⟨lift, hc, hl, fun u =>
    ⟨clock_run_records hm x (⟨x.1.cfg,lift⟩,x.2) u rfl, halls hp _⟩⟩

end L4.Height.ClockHead
namespace L4.Height.ClockHead

open Classical
open L4.Height
open L4.Height.Couple
open L4.Compiler.Native

noncomputable section

private theorem ofFn_nodup_of_injective {α : Type} :
    (n : Nat) → (f : Fin n → α) →
      Function.Injective f → (List.ofFn f).Nodup
  | 0, _, _ => by simp [List.ofFn_zero]
  | n + 1, f, hf => by
      rw [List.ofFn_succ]
      apply (List.nodup_cons).2
      constructor
      · intro hmem
        obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
        have hzero : (0 : Fin (n + 1)) = i.succ := hf hi.symm
        exact (Fin.succ_ne_zero i) hzero.symm
      · apply ofFn_nodup_of_injective n
          (fun i : Fin n => f i.succ)
        intro i j hij
        exact Fin.succ_inj.mp (hf hij)

private theorem map_nodup_of_injective {α β : Type}
    (f : α → β) (hf : Function.Injective f) :
    ∀ xs : List α, xs.Nodup → (xs.map f).Nodup := by
  intro xs hxs
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hcons := List.nodup_cons.mp hxs
      simp only [List.map_cons]
      apply List.nodup_cons.mpr
      constructor
      · intro hmem
        obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hmem
        have hyx : y = x := hf hfy
        subst y
        exact hcons.1 hy
      · exact ih hcons.2

/-- Core-only `flatMap` nodup criterion, specialized later to word blocks. -/
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

/-- Canonical duplicate-free enumeration of all words of length `q`. -/
private def allWords (n : Nat) : Nat → List (List (Fin n))
  | 0 => [[]]
  | q + 1 =>
      (List.ofFn (fun e : Fin n => e)).flatMap
        (fun e => (allWords n q).map (fun u => e :: u))

private theorem mem_allWords_iff {n : Nat} :
    ∀ (q : Nat) (u : List (Fin n)),
      u ∈ allWords n q ↔ u.length = q := by
  intro q
  induction q with
  | zero =>
      intro u
      simp [allWords]
  | succ q ih =>
      intro u
      constructor
      · intro hu
        rw [allWords] at hu
        obtain ⟨e, he, hem⟩ := List.mem_flatMap.mp hu
        obtain ⟨v, hv, hev⟩ := List.mem_map.mp hem
        rw [← hev]
        simp only [List.length_cons]
        exact congrArg Nat.succ ((ih v).1 hv)
      · intro hu
        cases u with
        | nil =>
            simp at hu
        | cons e v =>
            have hvlen : v.length = q := by
              simp only [List.length_cons] at hu
              omega
            rw [allWords]
            apply List.mem_flatMap.mpr
            refine ⟨e, List.mem_ofFn.mpr ⟨e, rfl⟩, ?_⟩
            apply List.mem_map.mpr
            exact ⟨v, (ih v).2 hvlen, rfl⟩

private theorem allWords_nodup (n : Nat) :
    ∀ q : Nat, (allWords n q).Nodup := by
  intro q
  induction q with
  | zero =>
      simp [allWords]
  | succ q ih =>
      rw [allWords]
      apply nodup_flatMap_of_nodup
        (List.ofFn (fun e : Fin n => e))
        (fun e => (allWords n q).map (fun u => e :: u))
      · exact ofFn_nodup_of_injective n
          (fun e : Fin n => e) (fun _ _ h => h)
      · intro e he
        exact map_nodup_of_injective
          (fun u : List (Fin n) => e :: u)
          (by
            intro u v huv
            exact (List.cons.inj huv).2)
          (allWords n q) ih
      · intro e he e' he' hne w hw w' hw' hww'
        obtain ⟨u, hu, hwu⟩ := List.mem_map.mp hw
        obtain ⟨v, hv, hwv⟩ := List.mem_map.mp hw'
        have hlist : e :: u = e' :: v :=
          hwu.trans (hww'.trans hwv.symm)
        have hhead : e = e' := (List.cons.inj hlist).1
        exact hne hhead

private theorem sum_flatMap_map {α β : Type}
    (xs : List α) (ys : α → List β) (f : β → Nat) :
    ((xs.flatMap ys).map f).sum =
      (xs.map (fun x => ((ys x).map f).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons, ih]

private theorem wordSum_eq_allWords_sum {n : Nat} :
    ∀ (q : Nat) (f : List (Fin n) → Nat),
      wordSum f q = ((allWords n q).map f).sum := by
  intro q
  induction q with
  | zero =>
      intro f
      simp [wordSum, allWords]
  | succ q ih =>
      intro f
      calc
        wordSum f (q + 1) =
            (List.ofFn (fun e : Fin n =>
              wordSum (fun v => f (e :: v)) q)).sum := rfl
        _ = (List.ofFn (fun e : Fin n =>
              (((allWords n q).map (fun v => e :: v)).map f).sum)).sum := by
              apply sum_ofFn_eq
              intro e
              simpa [List.map_map, Function.comp_def] using
                ih (fun v => f (e :: v))
        _ = (((List.ofFn (fun e : Fin n => e)).flatMap
              (fun e => (allWords n q).map (fun v => e :: v))).map f).sum := by
              symm
              rw [sum_flatMap_map]
              simp only [List.map_ofFn, Function.comp_def]
        _ = ((allWords n (q + 1)).map f).sum := rfl

/-- The words obtained by encoding all flattened vectors. -/
private def vectorWords (Q m : Nat) : List (List (Fin (2 ^ m))) :=
  (allVectors (Q * m)).map (vecWord Q m)

private theorem vectorWords_nodup (Q m : Nat) :
    (vectorWords Q m).Nodup := by
  unfold vectorWords
  exact map_nodup_of_injective (vecWord Q m)
    (vecWord_injective Q m) (allVectors (Q * m))
    (allVectors_nodup (Q * m))

private theorem mem_vectorWords_iff (Q m : Nat)
    (u : List (Fin (2 ^ m))) :
    u ∈ vectorWords Q m ↔ u.length = Q := by
  constructor
  · intro hu
    unfold vectorWords at hu
    obtain ⟨a, ha, hau⟩ := List.mem_map.mp hu
    rw [← hau]
    exact vecWord_length Q m a
  · intro hu
    obtain ⟨a, ha, _huniq⟩ := vec_word_bij Q m u hu
    unfold vectorWords
    apply List.mem_map.mpr
    exact ⟨a, mem_allVectors a, ha⟩

private theorem vectorWords_perm_allWords (Q m : Nat) :
    (vectorWords Q m).Perm (allWords (2 ^ m) Q) := by
  apply (List.perm_ext_iff_of_nodup
    (vectorWords_nodup Q m) (allWords_nodup (2 ^ m) Q)).2
  intro u
  exact (mem_vectorWords_iff Q m u).trans
    (mem_allWords_iff (n := 2 ^ m) Q u).symm

private theorem vector_sum_eq_wordSum (Q m : Nat)
    (f : List (Fin (2 ^ m)) → Nat) :
    ((allVectors (Q * m)).map (fun a => f (vecWord Q m a))).sum =
      wordSum f Q := by
  have hp := (vectorWords_perm_allWords Q m).map f
  have hs := List.Perm.sum_nat hp
  calc
    ((allVectors (Q * m)).map (fun a => f (vecWord Q m a))).sum =
        ((vectorWords Q m).map f).sum := by
          simp [vectorWords, List.map_map, Function.comp_def]
    _ = ((allWords (2 ^ m) Q).map f).sum := hs
    _ = wordSum f Q :=
      (wordSum_eq_allWords_sum (n := 2 ^ m) Q f).symm

private theorem filter_length_eq_indicator_sum {α : Type}
    (P : α → Prop) [DecidablePred P] :
    ∀ xs : List α,
      (xs.filter P).length =
        (xs.map (fun x => if P x then 1 else 0)).sum := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      by_cases hx : P x
      · simp [hx, ih, Nat.add_comm]
      · simp [hx, ih]

private theorem badVectorCount_eq_wordSum {m : Nat}
    (B : Nat) (hm : 0 < m) (s : Fin m → Snapshot) (Q : Nat) :
    ((allVectors (Q * m)).filter
      (fun a => anchorCount hm
        (runRounds B hm (vecRounds Q m a) s) ≠ 1)).length =
      wordSum
        (fun u => if anchorCount hm
          (runWord (heightChain B hm) s u) = 1 then 0 else 1) Q := by
  calc
    ((allVectors (Q * m)).filter
      (fun a => anchorCount hm
        (runRounds B hm (vecRounds Q m a) s) ≠ 1)).length =
        ((allVectors (Q * m)).map
          (fun a => if anchorCount hm
            (runRounds B hm (vecRounds Q m a) s) ≠ 1
            then 1 else 0)).sum :=
      filter_length_eq_indicator_sum
        (fun a => anchorCount hm
          (runRounds B hm (vecRounds Q m a) s) ≠ 1)
        (allVectors (Q * m))
    _ = ((allVectors (Q * m)).map
          (fun a => if anchorCount hm
            (runWord (heightChain B hm) s (vecWord Q m a)) = 1
            then 0 else 1)).sum := by
      apply list_sum_congr
      intro a ha
      rw [runWord_vecWord (m := m) B hm s Q a]
      by_cases hone :
          anchorCount hm
            (runRounds B hm (vecRounds Q m a) s) = 1
      · simp [hone]
      · simp [hone]
    _ = wordSum
          (fun u => if anchorCount hm
            (runWord (heightChain B hm) s u) = 1 then 0 else 1) Q :=
      vector_sum_eq_wordSum Q m
        (fun u => if anchorCount hm
          (runWord (heightChain B hm) s u) = 1 then 0 else 1)

noncomputable def logicalEventSum {β : Type} {n : Nat}
    (P : β → List (Fin n) → Prop) :
    List β → List (Fin n) → Nat
  | [], _ => 0
  | a :: as, u => (if P a u then 1 else 0) + logicalEventSum P as u

private theorem logicalWordSumEventSum {β : Type} {n : Nat}
    (P : β → List (Fin n) → Prop) (as : List β) (t : Nat) :
    wordSum (logicalEventSum P as) t =
      (as.map (fun a =>
        wordSum (fun u => if P a u then 1 else 0) t)).sum := by
  classical
  induction as with
  | nil => simp [logicalEventSum, wordSum_zero]
  | cons a as ih =>
      simp only [logicalEventSum, List.map_cons, List.sum_cons]
      rw [wordSum_add_fun, ih]

private theorem logicalOneLeEventSum {β : Type} {n : Nat}
    (P : β → List (Fin n) → Prop)
    {a : β} {as : List β} {u : List (Fin n)}
    (ha : a ∈ as) (hp : P a u) :
    1 ≤ logicalEventSum P as u := by
  classical
  induction as with
  | nil => simp at ha
  | cons b bs ih =>
      simp only [List.mem_cons] at ha
      rcases ha with hba | ha
      · subst b
        simp [logicalEventSum, hp]
      · have htail := ih ha
        by_cases hb : P b u
        · simp [logicalEventSum, hb]
        · simpa [logicalEventSum, hb] using htail

private theorem logicalWordSumMono {n : Nat}
    (f g : List (Fin n) → Nat) :
    ∀ t, (∀ u, u.length = t → f u ≤ g u) →
      wordSum f t ≤ wordSum g t := by
  intro t
  induction t generalizing f g with
  | zero =>
      intro h
      exact h [] rfl
  | succ t ih =>
      intro h
      simp only [wordSum]
      apply sum_ofFn_le
      intro e
      apply ih
      intro u hu
      apply h
      simp [hu]

private theorem logicalListScaledSumLe {β : Type}
    (p T : Nat) (f : β → Nat) :
    ∀ as : List β,
      (∀ a, a ∈ as → p * f a ≤ T) →
      p * (as.map f).sum ≤ as.length * T := by
  intro as
  induction as with
  | nil =>
      intro h
      simp
  | cons a as ih =>
      intro h
      have ha := h a (by simp)
      have htail : ∀ b, b ∈ as → p * f b ≤ T := by
        intro b hb
        exact h b (by simp [hb])
      have hi := ih htail
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        Nat.mul_add, Nat.succ_mul]
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (Nat.add_le_add ha hi)

/-- Exact Markov scaling retains the fifteen-sixty-fourths logical bound. -/
theorem logical_failure_sharp {m B : Nat} (hm : 0 < m) (hmb : m < B)
    (s : Fin m → Snapshot) (hs : Bounded B s) :
    64 * wordSum
      (fun u => if anchorCount hm (runWord (heightChain B hm) s u) = 1
        then 0 else 1) (2 ^ 19 * m) ≤
      15 * (2 ^ m) ^ (2 ^ 19 * m) := by
  let Q := 2 ^ 19 * m
  let bad := wordSum
    (fun u => if anchorCount hm (runWord (heightChain B hm) s u) = 1
      then 0 else 1) Q
  let total := (2 ^ m) ^ Q
  have heq : wordSum
      (fun u => @ite Nat
        (anchorCount hm (stoppedRun (heightChain B hm)
          (fun y => anchorCount hm y = 1) s u) = 1)
        (Classical.propDecidable _) 0 1) Q = bad := by
    apply wordSum_congr
    intro u
    have hi := stoppedRun_single_anchor_iff_runWord_single_anchor B hm hmb s hs u
    by_cases he : anchorCount hm (runWord (heightChain B hm) s u) = 1
    · have hstop := hi.mpr he
      simp [he, hstop]
    · have hstop : ¬ anchorCount hm
          (stoppedRun (heightChain B hm) (fun y => anchorCount hm y = 1) s u) = 1 :=
        fun h => he (hi.mp h)
      simp [he, hstop]
  have hmark := markov_survivors (heightChain B hm)
    (fun y => anchorCount hm y = 1) s (122880 * m) Q
    (anchor_contraction B hm hmb s hs)
  rw [heq] at hmark
  have hmark' : Q * bad ≤ (122880 * m) * total := hmark
  have hc : 64 * (122880 * m) = 15 * Q := by
    dsimp [Q]
    simp only [← Nat.mul_assoc]
  change 64 * bad ≤ 15 * total
  apply Nat.le_of_mul_le_mul_right _
    (show 0 < Q from Nat.mul_pos (by decide) hm)
  calc
    (64 * bad) * Q = 64 * (Q * bad) := by ac_rfl
    _ ≤ 64 * ((122880 * m) * total) := Nat.mul_le_mul_left 64 hmark'
    _ = (64 * (122880 * m)) * total := (Nat.mul_assoc _ _ _).symm
    _ = (15 * total) * Q := by rw [hc]; ac_rfl

/-- The same exact fraction holds for the complete list of logical bit vectors. -/
theorem logical_vectors_sharp {m B : Nat} (hm : 0 < m) (hmb : m < B)
    (s : Fin m → Snapshot) (hs : Bounded B s) :
    64 * ((allVectors ((2 ^ 19 * m) * m)).filter
      (fun a => anchorCount hm
        (runRounds B hm (vecRounds (2 ^ 19 * m) m a) s) ≠ 1)).length ≤
      15 * 2 ^ ((2 ^ 19 * m) * m) := by
  rw [badVectorCount_eq_wordSum]
  have hp : (2 ^ m) ^ (2 ^ 19 * m) = 2 ^ ((2 ^ 19 * m) * m) := by
    rw [← Nat.pow_mul, Nat.mul_comm m (2 ^ 19 * m)]
  rw [← hp]
  exact logical_failure_sharp hm hmb s hs

/-- Adaptive revealed fibers transfer any rational finite counting bound. -/
theorem adaptive_fraction_transfer
    {α : Type} {n K : Nat}
    (S : PairedSource α (Fin K) n) (x : α) (t p q : Nat)
    (E : List (Fin n) → Prop) (F : (Fin K → Bool) → Prop)
    (bad : List (Fin K → Bool))
    (hbad : ∀ a, a ∈ bad ↔ F a)
    (hfraction : p * bad.length ≤ q * 2 ^ K)
    (hlogical : ∀ u, u.length = t → E u →
      (∀ k, firstReveal S k x u ≠ none) ∧ F (readVector S x u)) :
    p * wordSum (fun u => if E u then 1 else 0) t ≤ q * n ^ t := by
  let P : (Fin K → Bool) → List (Fin n) → Prop :=
    fun a u => FirstPrescribed S a x (List.finRange K) u
  let eventMass := wordSum (fun u => if E u then 1 else 0) t
  let fiberMass := fun a => wordSum (fun u => if P a u then 1 else 0) t
  have hpoint : ∀ u, u.length = t →
      (if E u then 1 else 0) ≤ logicalEventSum P bad u := by
    intro u hu
    by_cases he : E u
    · have hd := hlogical u hu he
      have hm : readVector S x u ∈ bad := (hbad _).2 hd.2
      have hpres : P (readVector S x u) u := by
        intro k _
        have hne := hd.1 k
        cases hfirst : firstReveal S k x u with
        | none => exact False.elim (hne hfirst)
        | some v => simpa [readVector, hfirst]
      simpa [he] using logicalOneLeEventSum P hm hpres
    · simp [he]
  have hmass : eventMass ≤ (bad.map fiberMass).sum := by
    calc
      eventMass ≤ wordSum (logicalEventSum P bad) t :=
        logicalWordSumMono _ _ t hpoint
      _ = (bad.map fiberMass).sum := logicalWordSumEventSum P bad t
  have hfiber : ∀ a, a ∈ bad → 2 ^ K * fiberMass a ≤ n ^ t := by
    intro a _
    exact (show 2 ^ K * wordSum
      (fun u => if FirstPrescribed S a x (List.finRange K) u then 1 else 0) t ≤ n ^ t by
        simpa only [List.length_finRange] using
          adaptive_prescribed S a x (List.finRange K) (List.nodup_finRange K) t)
  have hsum := logicalListScaledSumLe (2 ^ K) (n ^ t) fiberMass bad hfiber
  have hpull : 2 ^ K * eventMass ≤ bad.length * n ^ t :=
    Nat.le_trans (Nat.mul_le_mul_left (2 ^ K) hmass) hsum
  change p * eventMass ≤ q * n ^ t
  apply Nat.le_of_mul_le_mul_right _ (Nat.two_pow_pos K)
  calc
    (p * eventMass) * 2 ^ K = p * (2 ^ K * eventMass) := by ac_rfl
    _ ≤ p * (bad.length * n ^ t) := Nat.mul_le_mul_left p hpull
    _ = (p * bad.length) * n ^ t := (Nat.mul_assoc _ _ _).symm
    _ ≤ (q * 2 ^ K) * n ^ t := Nat.mul_le_mul_right (n ^ t) hfraction
    _ = (q * n ^ t) * 2 ^ K := by ac_rfl

/-- A fixed warm clock start has reached-and-bad mass at most fifteen sixty-fourths. -/
theorem warm_reached_bad_sharp {m B : Nat}
    (hm : 0 < m) (hmb : m < B)
    (M base : Nat) (hM : ClockParams M)
    (hdiv : 32 ∣ M / 2) (hzero : base % 32 = 0)
    (start : Fin m → Snapshot) (s : WordState m)
    (hs : Bounded B start) (hleg : Legit M hm s)
    (hstart : StartConsistent B M base hm falseChoices start s)
    (t : Nat) :
    64 * wordSum
      (fun u => if reachedBad B M base (2 ^ 19 * m) hm s u then 1 else 0)
      t ≤ 15 * (2 * m) ^ t := by
  let Q := 2 ^ 19 * m
  let S := physSource B M base Q hm
  let F : (Fin (Q * m) → Bool) → Prop :=
    fun a => anchorCount hm (runRounds B hm (vecRounds Q m a) start) ≠ 1
  let bad := (allVectors (Q * m)).filter (fun a => decide (F a))
  have hbad : ∀ a, a ∈ bad ↔ F a := by
    intro a
    simp [bad, mem_allVectors]
  have hfraction : 64 * bad.length ≤ 15 * 2 ^ (Q * m) := by
    simpa [bad, F, Q] using logical_vectors_sharp hm hmb start hs
  apply adaptive_fraction_transfer S s t 64 15
    (reachedBad B M base Q hm s) F bad hbad hfraction
  intro u _ hu
  exact physical_event B M base Q hm hM hdiv hzero
    (Nat.mul_pos (by decide) hm) start s hleg hstart u hu

end
end L4.Height.ClockHead

namespace L4.Height

open Classical

/-- At the longer trial deadline a concrete service block of length four
times the ring size leaves at most one sixty-fourth of the words unreached. -/
theorem clock_miss_small {m B M L base depth : Nat} (hm : 0 < m)
    (hM : ClockParams M) (hL : 64*m ≤ L) (s : WordState m)
    (hl : Legit M hm s) (hb : ∀ i, base ≤ s.lift i)
    (hd : depth ≤ 2^25*m) :
    let d := 2^30*L*m
    64 * wordSum (fun u => if ∃ i, (physicalRun B M hm s u).lift i < base+depth
      then 1 else 0) d ≤ (2*m)^d := by
  let x : OverrunState m := (s, none)
  let T := finiteLevelTime (B := B) (M := M) hm clockAct x base
  let d := 2^30*L*m
  let n := 2*m
  let miss := fun u : Thru.Word (2*m) =>
    if ∃ i, (physicalRun B M hm s u).lift i < base+depth then 1 else 0
  let mass := wordSum miss d
  let K := (4*m)*(2^28*m)
  have hpoint : d*mass ≤ wordSum (fun u => min (clockMaximum T depth u) d) d := by
    change d * wordSum miss d ≤ _
    rw [← wordSum_mul_left]
    apply wordSum_mono_on_length
    intro u hu
    by_cases hm' : ∃ i, (physicalRun B M hm s u).lift i < base+depth
    · obtain ⟨i, hi⟩ := hm'
      have hi' : (Thru.runWord (clockNext (B := B) (M := M) hm) x u).1.lift i < base+depth := by
        rw [clock_run_physical]; exact hi
      have hh := clock_endpoint_miss_time hm x base depth hb u i hi'
      have hmax := clock_site_le_maximum T depth u i
      change finiteLevelTime (B := B) (M := M) hm clockAct x base u i depth ≤ _ at hmax
      rw [hh, hu] at hmax
      simp [miss, show ∃ i, (physicalRun B M hm s u).lift i < base+depth from ⟨i,hi⟩,
        Nat.min_eq_right hmax]
    · simp [miss, hm']
  rw [repair_wordSum_eq_thru] at hpoint
  have hmean := clock_depth_mean (L := 4*m) (B := B) hm clockAct x base hM hl hb
    (by omega) (clock_served_moment_explicit (B := B) (M := M) hm) depth d
  have hbgt := clock_budget_gen m depth hm hd
  have hbound : d * mass ≤ K * n^d :=
    Nat.le_trans (Nat.le_trans hpoint hmean) (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hbgt))
  have hcost : 64*K ≤ d := by
    change 64*((4*m)*(2^28*m)) ≤ (2^30*L)*m
    calc
      64*((4*m)*(2^28*m)) = ((4*2^28)*(64*m))*m := by ac_rfl
      _ ≤ (2^30*L)*m := Nat.mul_le_mul_right m (Nat.mul_le_mul_left _ hL)
  have hpos : 0 < d := Nat.mul_pos (Nat.mul_pos (by decide) (by omega)) hm
  exact Nat.le_of_mul_le_mul_left (by
    show d*(64*mass) ≤ d*n^d
    calc
      d*(64*mass) = 64*(d*mass) := by ac_rfl
      _ ≤ 64*(K*n^d) := Nat.mul_le_mul_left _ hbound
      _ = (64*K)*n^d := (Nat.mul_assoc _ _ _).symm
      _ ≤ d*n^d := Nat.mul_le_mul_right _ hcost) hpos

end L4.Height
namespace L4.Height.ClockHead

open Classical
open L4.Compiler.Native

/-- The inclusive logical failure from a bounded consistent start includes
every miss. A sixty-fourth of the budget is reserved for those words. -/
theorem warm_inclusive_quarter {m B M base L : Nat}
    (hm : 0 < m) (hmb : m < B) (hM : ClockParams M)
    (hp : 32 ∣ M/2) (hz : base%32 = 0) (hL : 64*m ≤ L)
    (s : WordState m) (hl : Legit M hm s)
    (start : Fin m → Snapshot) (hb : Bounded B start)
    (hw : StartConsistent B M base hm falseChoices start s) :
    let target := base + 32*(2^19*m)
    let d := 2^30*L*m
    4*wordSum (fun u =>
      if anchorCount hm (observedSnapshot B M hm s u target) ≠ 1 ∨
        ¬ ∀ i, target ≤ (physicalRun B M hm s u).lift i then 1 else 0) d ≤ (2*m)^d := by
  let q := 2^19*m
  let target := base + 32*q
  let d := 2^30*L*m
  let f := fun u => if reachedBad B M base q hm s u then 1 else 0
  let g := fun u : Thru.Word (2*m) =>
    if ∃ i, (physicalRun B M hm s u).lift i < target then 1 else 0
  let incl := fun u => if anchorCount hm (observedSnapshot B M hm s u target) ≠ 1 ∨
      ¬ ∀ i, target ≤ (physicalRun B M hm s u).lift i then 1 else 0
  have hbse (i : Fin m) : base ≤ s.lift i := by
    rcases hw i with h | h <;> have hh := h.1 <;> omega
  have hgd : 32*q ≤ 2^25*m := by change 32*(524288*m) ≤ 33554432*m; omega
  have hf : 64*wordSum f d ≤ 15*(2*m)^d :=
    warm_reached_bad_sharp hm hmb M base hM hp hz start s hb hl hw d
  have hg : 64*wordSum g d ≤ (2*m)^d := clock_miss_small hm hM hL s hl hbse hgd
  have hu : wordSum incl d ≤ wordSum f d + wordSum g d := by
    rw [← wordSum_add_fun]
    apply wordSum_mono
    intro u
    by_cases hr : ∀ i, target ≤ (physicalRun B M hm s u).lift i
    · have hnm : ¬ ∃ i, (physicalRun B M hm s u).lift i < target :=
        fun ⟨i,h⟩ => Nat.not_lt_of_ge (hr i) h
      by_cases hd : anchorCount hm (observedSnapshot B M hm s u target) ≠ 1
      · have hf' : reachedBad B M base q hm s u := ⟨hr,hd⟩
        simp [incl, f, g, hd, hr, hf', hnm]
      · have hf' : ¬ reachedBad B M base q hm s u := fun h => hd h.2
        simp [incl, f, g, hd, hr, hf', hnm]
    · have hm' : ∃ i, (physicalRun B M hm s u).lift i < target := by
        apply Classical.byContradiction
        intro h
        exact hr (fun i => Nat.le_of_not_lt (fun hi => h ⟨i,hi⟩))
      simp [incl, f, g, hr, hm']
  change 4*wordSum incl d ≤ (2*m)^d
  omega

end L4.Height.ClockHead
namespace L4.Height.ClockHead

open L4.Height
open L4.Compiler.Native

/-- A retained target observation with the precise boundedness premise
needed by the logical anchor-permanence theorem. -/
def boundedObservedCertificate {m : Nat} (B M target : Nat) (hm : 0 < m)
    (s : WordState m) (u : List (Fin (2 * m))) : Prop :=
  ∃ snap : Fin m → Snapshot,
    (∀ i, levelCurr B M hm (u.map physicalActivation) s i target =
      some (snap i)) ∧ Bounded B snap ∧ anchorCount hm snap = 1

theorem boundedObservedCertificate_append {m : Nat}
    (B M target : Nat) (hm : 0 < m) (s : WordState m)
    (u v : List (Fin (2 * m)))
    (hc : boundedObservedCertificate B M target hm s u) :
    boundedObservedCertificate B M target hm s (u ++ v) := by
  obtain ⟨snap, ho, hb, hone⟩ := hc
  refine ⟨snap, ?_, hb, hone⟩
  intro i
  rw [List.map_append]
  exact levelCurr_stable B M hm _ _ s i target (snap i) (ho i)

private theorem virtual_physical_append {m B M : Nat} (hm : 0 < m)
    (s : WordState m) (u v : List (Fin (2 * m))) :
    physicalRun B M hm s (u ++ v) =
      physicalRun B M hm (physicalRun B M hm s u) v := by
  induction u generalizing s with
  | nil => rfl
  | cons e u ih => exact ih (physicalNext B M hm s e)

private theorem virtual_observation_exists {m B M : Nat} (hm : 0 < m)
    (u : List (Fin (2 * m))) (s : WordState m) (i : Fin m) (target : Nat)
    (hstart : s.lift i ≤ target)
    (hreach : target ≤ (physicalRun B M hm s u).lift i) :
    ∃ value, levelCurr B M hm (u.map physicalActivation) s i target =
      some value := by
  induction u generalizing s with
  | nil =>
      have he : s.lift i = target := by
        change target ≤ s.lift i at hreach
        omega
      exact ⟨(s.cfg i).curr, by simp [levelCurr, he]⟩
  | cons e u ih =>
      by_cases he : s.lift i = target
      · exact ⟨(s.cfg i).curr, by simp [levelCurr, he]⟩
      · have hstep : (physicalNext B M hm s e).lift i = s.lift i ∨
            (physicalNext B M hm s e).lift i = s.lift i + 1 := by
          by_cases hi : i = physicalSite e
          · subst i
            cases ha : clockAction M hm s (physicalSite e) <;>
              simp [physicalNext, activate, ha, advanceLift]
          · left
            simp [physicalNext, activate, hi]
        have hnext : (physicalNext B M hm s e).lift i ≤ target := by
          rcases hstep with hs | hs <;> omega
        obtain ⟨value, hv⟩ := ih (physicalNext B M hm s e) hnext hreach
        refine ⟨value, ?_⟩
        simpa [levelCurr, he, physicalActivation, physicalNext] using hv

/-- Reach removes the default branch of observedSnapshot. -/
theorem virtual_bounded_certificate_of_reach {m B M target : Nat} (hm : 0 < m)
    (s : WordState m) (u : List (Fin (2 * m)))
    (hstart : ∀ i, s.lift i ≤ target)
    (hreach : ∀ i, target ≤ (physicalRun B M hm s u).lift i)
    (hb : Bounded B (observedSnapshot B M hm s u target))
    (hone : anchorCount hm (observedSnapshot B M hm s u target) = 1) :
    boundedObservedCertificate B M target hm s u := by
  refine ⟨observedSnapshot B M hm s u target, ?_, hb, hone⟩
  intro i
  obtain ⟨value, hv⟩ := virtual_observation_exists hm u s i target (hstart i) (hreach i)
  simpa [observedSnapshot, hv] using hv

/-- A fixed target snapshot supplies the unique anchor on every later
aligned slice observed along any continuation. No bound is imposed on the
initial snapshots or on any earlier virtual frontier. -/
theorem virtual_observed_anchor_permanent {m B M target : Nat}
    (hm : 0 < m) (hmb : m < B)
    (hM : ClockParams M) (hp : 32 ∣ M / 2) (hz : target % 32 = 0)
    (s : WordState m) (hl : LegitCoset M hm s)
    (hbelow : ∀ i, s.lift i < target)
    (u : List (Fin (2 * m)))
    (hc : boundedObservedCertificate B M target hm s u) :
    ∃ a : Fin m, ∀ (v : List (Fin (2 * m))) (t : Nat)
      (obs : Fin m → Snapshot),
      (∀ i, levelCurr B M hm ((u ++ v).map physicalActivation) s i
        (target + 32 * t) = some (obs i)) →
      ∀ j, IsAnchor hm obs j ↔ j = a := by
  obtain ⟨snap, ho, hb, hone⟩ := hc
  obtain ⟨a, ha⟩ := anchor_exists hm snap
  refine ⟨a, ?_⟩
  intro v t obs hobs
  let w := u ++ v
  let c := strongChoices B M target 0 hm (canon M s) w
  let h := w.map physicalActivation
  have hup : UpdatesAgree B M hm s h := updatesAgree_of_dvd hM hp h s hl
  have hbase : ∀ i, levelCurr B M hm h (canon M s) i target = some (snap i) := by
    intro i
    rw [canon_levelCurr hM h s hl hup i target]
    change levelCurr B M hm ((u ++ v).map physicalActivation) s i target = _
    rw [List.map_append]
    exact levelCurr_stable B M hm _ _ s i target (snap i) (ho i)
  have hvirtualStart :
      (fun i => (levelCurr B M hm h (canon M s) i target).getD
        ({} : Snapshot)) = snap := by
    funext i
    rw [hbase i]
    rfl
  have hfuture : obs = runRounds B hm (roundBits c target t) snap := by
    funext i
    have hobsCanon : levelCurr B M hm h (canon M s) i
        (target + 32 * t) = some (obs i) := by
      rw [canon_levelCurr hM h s hl hup i (target + 32 * t)]
      exact hobs i
    have hv := virtual_slice_comparison hM hm c h (canon M s)
      (canon_legit hl) hbelow
      (honors_strongChoices B M target 0 hm (canon M s) w)
      i (32 * t) (obs i) hobsCanon
    rw [hvirtualStart] at hv
    have hsync := syncLevels_runRounds (B := B) (M := M) (ellzero := target)
      (k := t) hm c snap (fun _ => clockOf_mod_phase hp hz)
    exact hv.trans (congrFun hsync i)
  rw [hfuture]
  exact single_anchor_runRounds B hm hmb _ snap a hb
    (only_anchor_of_count_one hm snap a hone ha)

/-- A predicate of the native configuration, witnessed by a coherent raw
history and a bounded, single-anchor observation. The present stored lift
does not enter this predicate. -/
def virtualNativeR {m : Nat} (B M : Nat) (hm : 0 < m)
    (cfg : Fin m → NativeRecord) : Prop :=
  ∃ (s : WordState m) (u : List (Fin (2 * m))) (target : Nat),
    LegitCoset M hm s ∧ (∀ i, s.lift i < target) ∧ target % 32 = 0 ∧
    boundedObservedCertificate B M target hm s u ∧
    (physicalRun B M hm s u).cfg = cfg

/-- The native predicate is closed under every literal native activation. -/
theorem virtualNativeR_activate {m B M : Nat} (hm : 0 < m)
    (cfg : Fin m → NativeRecord) (i : Fin m) (b : Bool)
    (hx : virtualNativeR B M hm cfg) :
    virtualNativeR B M hm (Recover.StageThree.activate B M hm cfg i b) := by
  obtain ⟨s, u, target, hl, hbelow, hz, hc, he⟩ := hx
  let e : Fin (2 * m) := ⟨2 * i.val + b.toNat, by
    cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega⟩
  have hes : physicalSite e = i := by
    apply Fin.ext
    cases b with
    | false => change (2 * i.val + 0) / 2 = i.val; omega
    | true => change (2 * i.val + 1) / 2 = i.val; omega
  have heb : physicalBit e = b := by
    cases b <;> simp [physicalBit, e, Nat.add_mod, Nat.mul_mod]
  refine ⟨s, u ++ [e], target, hl, hbelow, hz,
    boundedObservedCertificate_append B M target hm s u [e] hc, ?_⟩
  rw [virtual_physical_append]
  change (activate B M hm (physicalRun B M hm s u)
    (physicalSite e) (physicalBit e)).cfg = _
  rw [hes, heb, clock_activate_cfg, he]

/-- Any coherent raw trial with a reached bounded singleton slice gives a
member of the closed native endpoint set, with no simultaneous warm cut. -/
theorem virtualNativeR_cover {m B M target : Nat} (hm : 0 < m)
    (s : WordState m) (hl : LegitCoset M hm s)
    (hbelow : ∀ i, s.lift i < target) (hz : target % 32 = 0)
    (u : List (Fin (2 * m)))
    (hc : boundedObservedCertificate B M target hm s u) :
    virtualNativeR B M hm (physicalRun B M hm s u).cfg := by
  exact ⟨s, u, target, hl, hbelow, hz, hc, rfl⟩

theorem virtualNativeR_cover_reached {m B M target : Nat} (hm : 0 < m)
    (s : WordState m) (hl : LegitCoset M hm s)
    (hbelow : ∀ i, s.lift i < target) (hz : target % 32 = 0)
    (u : List (Fin (2 * m)))
    (hreach : ∀ i, target ≤ (physicalRun B M hm s u).lift i)
    (hb : Bounded B (observedSnapshot B M hm s u target))
    (hone : anchorCount hm (observedSnapshot B M hm s u target) = 1) :
    virtualNativeR B M hm (physicalRun B M hm s u).cfg := by
  apply virtualNativeR_cover hm s hl hbelow hz u
  exact virtual_bounded_certificate_of_reach hm s u
    (fun i => Nat.le_of_lt (hbelow i)) hreach hb hone

def virtualClockR {m : Nat} (B M : Nat) (hm : 0 < m)
    (x : OverrunState m) : Prop := virtualNativeR B M hm x.1.cfg

theorem virtualClockR_closed {m B M : Nat} (hm : 0 < m)
    (x : OverrunState m) (e : Fin (2 * m))
    (hx : virtualClockR B M hm x) :
    virtualClockR B M hm (clockNext (B := B) (M := M) hm x e) := by
  change virtualNativeR B M hm
    (activate B M hm x.1 (physicalSite e) (physicalBit e)).cfg
  rw [clock_activate_cfg]
  exact virtualNativeR_activate hm x.1.cfg (physicalSite e) (physicalBit e) hx

/-- Every native-R witness carries a permanent unique-anchor identity on
all later aligned observations of its coherent extension. -/
theorem virtualNativeR_permanent {m B M : Nat}
    (hm : 0 < m) (hmb : m < B) (hM : ClockParams M) (hp : 32 ∣ M / 2)
    (cfg : Fin m → NativeRecord) (hx : virtualNativeR B M hm cfg) :
    ∃ (s : WordState m) (u : List (Fin (2 * m))) (target : Nat) (a : Fin m),
      (physicalRun B M hm s u).cfg = cfg ∧
      ∀ (v : List (Fin (2 * m))) (t : Nat) (obs : Fin m → Snapshot),
        (∀ i, levelCurr B M hm ((u ++ v).map physicalActivation) s i
          (target + 32 * t) = some (obs i)) →
        ∀ j, IsAnchor hm obs j ↔ j = a := by
  obtain ⟨s, u, target, hl, hbelow, hz, hc, he⟩ := hx
  obtain ⟨a, ha⟩ := virtual_observed_anchor_permanent hm hmb hM hp hz
    s hl hbelow u hc
  exact ⟨s, u, target, a, he, ha⟩

/-- Boundedness cannot be dropped from single-anchor permanence, even when
m < B and the clock itself starts flat and coherent. -/
def unboundedFourSnap (i : Fin 4) : Snapshot := {x := 14 + i.val}

def unboundedFourClock : WordState 4 where
  cfg i :=
    { tick := 32
      err := false
      prior := unboundedFourSnap i
      curr := unboundedFourSnap i }
  lift _ := 0

theorem unbounded_single_anchor_counterexample :
    Legit 64 (by decide) unboundedFourClock ∧
    4 < 16 ∧
    anchorCount (by decide) unboundedFourSnap = 1 ∧
    (∀ i : Fin 4, (unboundedFourSnap i).role = false) ∧
    (∀ i : Fin 4,
      (logicalRound 16 (by decide) (fun _ => false) unboundedFourSnap i).x =
        if i.val = 0 then 0 else if i.val = 1 then 15 else
          if i.val = 2 then 16 else 1) ∧
    anchorCount (by decide)
      (logicalRound 16 (by decide) (fun _ => false) unboundedFourSnap) = 2 ∧
    ¬ Bounded 16 unboundedFourSnap := by
  refine ⟨?_, by decide, by decide, fun _ => rfl, by decide, by decide, ?_⟩
  · refine ⟨fun _ => rfl, fun _ => rfl, ?_⟩
    intro i j _
    change Near 0 0
    exact ⟨by decide, by decide⟩
  · intro hb
    have h := hb (2 : Fin 4)
    change 16 < 16 at h
    omega

end L4.Height.ClockHead
namespace L4.Height.ClockHead

open L4.Compiler.Native
open Classical

private theorem word_clock_physical {m B M : Nat} (hm : 0 < m)
    (x : OverrunState m) (u : List (Fin (2*m))) :
    (runWord (clockNext (B := B) (M := M) hm) x u).1 = physicalRun B M hm x.1 u := by
  induction u generalizing x with
  | nil => rfl
  | cons e u ih => exact ih (clockNext (B := B) (M := M) hm x e)

/-- The residual counting event for a repaired native trial. Missing the
target is charged separately to its clock. -/
def uncertifiedSlice {m : Nat} (B M target : Nat) (hm : 0 < m)
    (s : WordState m) (u : List (Fin (2*m))) : Prop :=
  (∀ i, target ≤ (physicalRun B M hm s u).lift i) ∧
    ¬ (Bounded B (observedSnapshot B M hm s u target) ∧
      anchorCount hm (observedSnapshot B M hm s u target) = 1)

/-- Conditional post-custody bound on native records. The only additional
probabilistic premise is the count of reached but uncertified slices for one
coherent trial per legitimate restart. Clock service, overrun, endpoint
cover, closure and repair are derived on this concrete scheduler. -/
theorem clock_layer_headline_of_slice {m B M bL ringN r L : Nat}
    (hm : 0 < m) (hM : ClockParams M) (hd : m/2 < M/2)
    (hr : 0 < r) (hs : L = 2^(5*bL+34)*ringN*r) (hw : m*r ≤ ringN)
    (hSlice : ∀ x : OverrunState m,
      Recover.Chain.LgSet (clockChain (B := B) (M := M) hm) x →
      ¬ virtualClockR B M hm x →
      ∃ (lift : Fin m → Nat) (floor base : Nat),
        let s : WordState m := ⟨x.1.cfg, lift⟩
        let target := base + 32*(2^19*m)
        LegitCoset M hm s ∧ (∀ i, floor ≤ lift i) ∧
        (∀ i, lift i < base) ∧ base%32 = 0 ∧ target-floor ≤ 2^25*m ∧
        4*wordSum (fun u => if uncertifiedSlice B M target hm s u then 1 else 0)
          (2^30*L*m) ≤ (2*m)^(2^30*L*m))
    (x : OverrunState m) (hx : Recover.StageTwo.WellFormed M x.1.cfg) :
    IIDExpectedHittingTimeAtMost (clockNext (B := B) (M := M) hm)
      (virtualClockR B M hm) x (2^(5*bL+66)*ringN^2) := by
  let C := clockChain (B := B) (M := M) hm
  let R := virtualClockR B M hm
  let d := 2^30*L*m
  let n := 2*m
  let Event := List (Fin (2*m)) → Prop
  let mass := fun f : Event => wordSum (fun u => if f u then 1 else 0) d
  have hL := clock_service_scale hr hw hs
  have hsel (y : OverrunState m) : ∃ fs : Event × Event,
      (Recover.Chain.LgSet C y → ¬ R y → 4*mass fs.1 ≤ n^d ∧ 4*mass fs.2 ≤ n^d) ∧
      (Recover.Chain.LgSet C y → ∀ u : List (Fin (2*m)), u.length = d →
        ¬ fs.1 u → ¬ fs.2 u → R (runWord C.next y u)) := by
    by_cases hleg : Recover.Chain.LgSet C y
    · by_cases hdone : R y
      · refine ⟨(fun _ => False, fun _ => False), fun _ hn => (hn hdone).elim, ?_⟩
        intro _ u _ _ _
        exact runWord_of_closed C.next R (virtualClockR_closed hm) y u hdone
      · obtain ⟨lift, floor, base, hc, hf, hbelow, hz, hd', hlog⟩ := hSlice y hleg hdone
        let s : WordState m := ⟨y.1.cfg, lift⟩
        let target := base + 32*(2^19*m)
        let z : OverrunState m := (s, y.2)
        let miss : Event := fun u => ∃ i, (physicalRun B M hm s u).lift i < target
        have hft : floor ≤ target := by
          have h := hf ⟨0,hm⟩
          have h' := hbelow ⟨0,hm⟩
          dsimp [target]; omega
        have ht : floor+(target-floor) = target := by omega
        have hover := clock_coset_overrun_quarter (B := B) hm hM hL s hc y.2 hf hd'
        refine ⟨(uncertifiedSlice B M target hm s, miss), ?_, ?_⟩
        · intro _ _
          refine ⟨hlog, ?_⟩
          dsimp only [mass, Prod.snd]
          rw [repair_wordSum_eq_thru]
          apply Nat.le_trans (Nat.mul_le_mul_left 4 ?_) hover
          apply Thru.wordSum_mono
          intro u
          rw [clock_run_physical]
          have he : floor + (target-floor) = target := ht
          dsimp only [Prod.fst]
          rw [he]
          by_cases hmiss : ∃ i, (physicalRun B M hm s u).lift i < target <;>
            simp [miss, hmiss]
        · intro _ u _ hgood hhit
          have hreach (i : Fin m) : target ≤ (physicalRun B M hm s u).lift i :=
            Nat.le_of_not_lt (fun hi => hhit ⟨i,hi⟩)
          have hcert : Bounded B (observedSnapshot B M hm s u target) ∧
              anchorCount hm (observedSnapshot B M hm s u target) = 1 :=
            Classical.byContradiction fun hn => hgood ⟨hreach, hn⟩
          have habove (i : Fin m) : s.lift i < target :=
            Nat.lt_of_lt_of_le (hbelow i) (Nat.le_add_right _ _)
          have hphase : target%32 = 0 := by simp [target, Nat.add_mod, hz]
          have hnative := virtualNativeR_cover_reached hm s hc habove hphase u
            hreach hcert.1 hcert.2
          change virtualNativeR B M hm (runWord (clockNext (B := B) (M := M) hm) y u).1.cfg
          rw [clock_run_records hm y z u rfl, word_clock_physical]
          exact hnative
    · exact ⟨(fun _ => False, fun _ => False), fun hh => (hleg hh).elim,
        fun hh => (hleg hh).elim⟩
  exact post_custody_chain_capfree C R L bL ringN r
    (fun y => (hsel y).choose.1) (fun y => (hsel y).choose.2)
    ⟨by have := hM.1; omega, hM.2⟩ hd (by omega) hm
    (clock_served_moment hm hL) hs hw (virtualClockR_closed hm)
    (fun y hy hn => ((hsel y).choose_spec.1 hy hn).1)
    (fun y hy hn => ((hsel y).choose_spec.1 hy hn).2)
    (fun y => (hsel y).choose_spec.2) x hx

/-- A bounded slice of a two-site clock at height modulus one necessarily
has two anchors. Hence the native certificate is empty at these parameters. -/
theorem unit_virtual_target_empty (x : OverrunState 2) :
    ¬ virtualClockR 1 256 unit_ring_positive x := by
  rintro ⟨s,u,ell,_,_,_,⟨snap, _, hb, hone⟩,_⟩
  have hzero (i : Fin 2) : (snap i).x = 0 := by have := hb i; omega
  have htwo : anchorCount unit_ring_positive snap = 2 := by simp [anchorCount, IsAnchor, hzero]
  omega

/-- At a well-formed, legitimate start satisfying the clock and width
relations, even the native target has infinite expected hitting time. -/
theorem clock_layer_headline_counterexample (bound : Nat) :
    Recover.StageTwo.WellFormed 256 unitClockState.cfg ∧
      ¬ IIDExpectedHittingTimeAtMost (clockNext (B := 1) (M := 256) unit_ring_positive)
        (virtualClockR 1 256 unit_ring_positive) (unitClockState, none) bound := by
  refine ⟨unit_clock_lgSet.2.2, ?_⟩
  intro h
  have hm := markov_survivors _ _ _ bound (bound+1) h
  simp only [unit_virtual_target_empty, if_false, wordSum_const_one] at hm
  exact (Nat.not_succ_le_self bound) (Nat.le_of_mul_le_mul_right hm (Nat.pow_pos (by decide)))

end L4.Height.ClockHead

namespace L4.Height.ClockHead

/-- All values in the proposed quadratic coefficient can be instantiated.
The service block at these values exceeds even the longer trial scale. -/
theorem paired_headline_fails_at_scale (Kone bL : Nat) :
    let L := 2^(5*bL+34)*4*2
    4*2 ≤ L ∧
    (∀ i y, Thru.MomentAt (clockChain (B := 1) (M := 256) unit_ring_positive).next
      ((clockChain (B := 1) (M := 256) unit_ring_positive).served i) L y) ∧
    Recover.StageTwo.WellFormed 256 unitClockState.cfg ∧
    ¬ IIDExpectedHittingTimeAtMost (clockNext (B := 1) (M := 256) unit_ring_positive)
      (virtualClockR 1 256 unit_ring_positive) (unitClockState, none)
      ((Kone+2^(5*bL+66))*4^2) := by
  have hL := clock_service_scale (m := 2) (r := 2) (ringN := 4) (bL := bL)
    (by decide) (by decide) rfl
  exact ⟨hL, clock_served_moment unit_ring_positive hL,
    clock_layer_headline_counterexample _⟩

end L4.Height.ClockHead

namespace L4.Height.ClockHead

open Classical

/-- The failure convention counting either a bad observation or a missed
level assigns full mass to the two-site counterexample. -/
theorem unit_inclusive_full_mass (target d : Nat) :
    wordSum (fun u : List (Fin (2*2)) =>
      if anchorCount unit_ring_positive (observedSnapshot 1 256 unit_ring_positive
        unitClockState u target) ≠ 1 ∨
        ¬ ∀ i, target ≤ (physicalRun 1 256 unit_ring_positive unitClockState u).lift i
      then 1 else 0) d = 4^d := by
  calc
    _ = wordSum (fun _ : List (Fin (2*2)) => 1) d := by
      apply wordSum_congr
      intro u
      simp [unit_observed_two_anchors]
    _ = _ := wordSum_const_one d

/-- The obstruction applies to every closed state predicate whose membership
certifies an actual reached singleton observation on the path. -/
theorem no_headline_for_observed_singleton (R : OverrunState 2 → Prop)
    (hc : ∀ y e, R y → R (clockNext (B := 1) (M := 256) unit_ring_positive y e))
    (hs : ∀ u, R (runWord (clockNext (B := 1) (M := 256) unit_ring_positive)
      (unitClockState, none) u) → ∃ ell,
        (∀ i, ell ≤ (physicalRun 1 256 unit_ring_positive unitClockState u).lift i) ∧
        anchorCount unit_ring_positive
          (observedSnapshot 1 256 unit_ring_positive unitClockState u ell) = 1)
    (bound : Nat) :
    ¬ IIDExpectedHittingTimeAtMost (clockNext (B := 1) (M := 256) unit_ring_positive)
      R (unitClockState, none) bound := by
  intro h
  have hm := markov_survivors _ _ _ bound (bound+1) h
  have hmiss (u : List (Fin (2*2))) :
      ¬ R (stoppedRun (clockNext (B := 1) (M := 256) unit_ring_positive)
        R (unitClockState, none) u) := fun hr =>
    unit_no_reached_single_anchor u (hs u ((stoppedRun_mem_iff_runWord_mem _ _ hc _ u).mp hr))
  simp only [hmiss, if_false, wordSum_const_one] at hm
  exact (Nat.not_succ_le_self bound) (Nat.le_of_mul_le_mul_right hm (Nat.pow_pos (by decide)))

end L4.Height.ClockHead
namespace L4.Height.ClockHead

open L4.Compiler.Native
open Classical

private theorem rounds_bounded {m B : Nat} (hm : 0 < m) (hB : 0 < B)
    (bs : List (Fin m → Bool)) (s : Fin m → Snapshot) (hs : Bounded B s) :
    Bounded B (runRounds B hm bs s) := by
  induction bs generalizing s with
  | nil => exact hs
  | cons b bs ih => exact ih _ (bounded_round B hm hB b s hs)

/-- A bounded consistent warm start yields the native permanent certificate
with probability at least three quarters at the physical deadline. -/
theorem warm_native_trial {m B M base L : Nat} (hm : 0 < m) (hmb : m < B)
    (hM : ClockParams M) (hp : 32 ∣ M/2) (hz : base%32 = 0) (hL : 64*m ≤ L)
    (raw : WordState m) (hc : LegitCoset M hm raw) (last : Option (Fin m))
    (start : Fin m → Snapshot) (hb : Bounded B start)
    (hw : StartConsistent B M base hm falseChoices start (canon M raw)) :
    let d := 2^30*L*m
    4*wordSum (fun u => if virtualClockR B M hm
      (runWord (clockNext (B := B) (M := M) hm) (raw,last) u) then 0 else 1) d ≤ (2*m)^d := by
  let q := 2^19*m
  let target := base+32*q
  let s := canon M raw
  have hq : 0 < q := Nat.mul_pos (by decide) hm
  have hbound := warm_inclusive_quarter hm hmb hM hp hz hL s (canon_legit hc) start hb hw
  apply Nat.le_trans (Nat.mul_le_mul_left 4 ?_) hbound
  apply wordSum_mono
  intro u
  by_cases hf : anchorCount hm (observedSnapshot B M hm s u target) ≠ 1 ∨
      ¬ ∀ i, target ≤ (physicalRun B M hm s u).lift i
  · calc
      _ ≤ 1 := by split <;> decide
      _ ≤ _ := by
        split
        · exact Nat.le_refl 1
        · rename_i hgood
          exact (hgood hf).elim
  · have hr : ∀ i, target ≤ (physicalRun B M hm s u).lift i :=
      Classical.byContradiction (fun hn => hf (Or.inr hn))
    have ha : anchorCount hm (observedSnapshot B M hm s u target) = 1 :=
      Classical.byContradiction (fun hn => hf (Or.inl hn))
    have hs := (physical_snapshot_reach B M base q hm hM hp hz hq start s u
      (canon_legit hc) hw hr).1
    have hobs : observedSnapshot B M hm s u target =
        runRounds B hm (roundBits (physicalChoices B M base q hm s u) base q) start := by
      funext i
      simp [observedSnapshot, target, hs i]
    have hbounded : Bounded B (observedSnapshot B M hm s u target) := by
      rw [hobs]
      exact rounds_bounded hm (by omega) _ start hb
    have he := clock_run_canon_lift (B := B) hm hM raw hc last u
    simp only [clock_run_physical] at he
    have hr' (i : Fin m) : target ≤ (physicalRun B M hm raw u).lift i := by
      rw [he]; exact hr i
    have heo := clock_canon_observed (B := B) hm hM hp raw hc u target
    change observedSnapshot B M hm s u target = _ at heo
    rw [heo] at hbounded ha
    have hbelow (i : Fin m) : raw.lift i < target := by
      rcases hw i with h | h
      · have hh : raw.lift i = base := h.1
        dsimp [target]; omega
      · have hh : raw.lift i = base+1 := h.1
        dsimp [target]; omega
    have hphase : target%32=0 := by simp [target,Nat.add_mod,hz]
    have hy := virtualNativeR_cover_reached hm raw hc hbelow hphase u hr' hbounded ha
    have hR : virtualClockR B M hm (runWord (clockNext (B := B) (M := M) hm) (raw,last) u) := by
      unfold virtualClockR
      rw [word_clock_physical]
      exact hy
    simp [hR]

end L4.Height.ClockHead
namespace L4.Height

open Classical
open L4.Compiler.Native

/-- A one-anchor staircase outside the height modulus. The anchor countdown
is its only varying field during all-false rounds. -/
def delaySnapshot (z : Nat) (i : Fin 4) : Snapshot :=
  { x := 15 + 16 * i.val, d := 4 - i.val,
    z := if i.val = 0 then z else 0,
    anchor := decide (i.val = 0), approve := decide (i.val = 0) }

@[simp] private theorem delay_last_value : (3 : Fin 4).val = 3 := rfl

private theorem delay_site_cases (i : Fin 4) :
    i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ ∨
      i = ⟨2, by decide⟩ ∨ i = ⟨3, by decide⟩ := by
  have hi := i.isLt
  have hv : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
  rcases hv with h | h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))

/-- The false-bit round either reloads forty or decrements the sole countdown. -/
theorem delay_false_step (z : Nat) (hz : z ≤ 40) :
    logicalRound 16 (by decide) (fun _ : Fin 4 => false) (delaySnapshot z) =
      delaySnapshot (if z = 0 then 40 else z - 1) := by
  funext i
  have hmin : min 40 (z - 1) = z - 1 := Nat.min_eq_right (by omega)
  rcases delay_site_cases i with rfl | rfl | rfl | rfl <;>
    simp [delaySnapshot, logicalRound, phaseStep, phaseUpdate, left, right, hmin]

/-- False rounds can be delayed arbitrarily long while staying in the
same staircase family. -/
theorem delay_false_family (z q : Nat) (hz : z ≤ 40) :
    ∃ z', z' ≤ 40 ∧
      runRounds 16 (by decide) (List.replicate q (fun _ : Fin 4 => false))
        (delaySnapshot z) = delaySnapshot z' := by
  induction q generalizing z with
  | zero => exact ⟨z, hz, rfl⟩
  | succ q ih =>
    let next := if z = 0 then 40 else z - 1
    have hn : next ≤ 40 := by dsimp [next]; split <;> omega
    obtain ⟨z', hz', he⟩ := ih next hn
    refine ⟨z', hz', ?_⟩
    simpa only [List.replicate_succ, runRounds, delay_false_step z hz] using he

/-- Waiting for the remaining countdown returns exactly to the zero-countdown state. -/
theorem delay_false_drain (z : Nat) (hz : z ≤ 40) :
    runRounds 16 (by decide) (List.replicate z (fun _ : Fin 4 => false))
      (delaySnapshot z) = delaySnapshot 0 := by
  induction z with
  | zero => rfl
  | succ z ih =>
    have hh := delay_false_step (z + 1) hz
    simp only [if_neg (by omega : z + 1 ≠ 0), Nat.add_sub_cancel] at hh
    simp only [List.replicate_succ, runRounds, hh]
    exact ih (by omega)

/-- After firing, role true propagates one site to the right each round.
At the fourth round the last site writes fifteen; the intervening heights
have not changed. This formula describes the propagation mechanism. -/
def delayFired (rounds : Nat) (i : Fin 4) : Snapshot :=
  { x := if rounds = 4 ∧ i.val = 3 then 15 else 15 + 16 * i.val,
    d := 4 - i.val,
    z := if i.val = 0 then 41 - rounds else 0,
    anchor := decide (i.val = 0), home := decide (i.val = 0),
    role := decide (i.val < rounds),
    proposal := if i.val < rounds then (if i.val = 3 then 15 else 14) else 0,
    approve := decide (i.val = 0 ∨ (rounds = 4 ∧ i.val = 3)) }

/-- The first true-bit round fires the anchor. -/
theorem delay_true_first :
    logicalRound 16 (by decide) (fun _ : Fin 4 => true) (delaySnapshot 0) =
      delayFired 1 := by
  funext i
  rcases delay_site_cases i with rfl | rfl | rfl | rfl <;>
    simp [delaySnapshot, delayFired, logicalRound, phaseStep, phaseUpdate, left, right]

/-- A fired role crosses one more edge per synchronous round. -/
theorem delay_true_step (rounds : Nat) (hlo : 1 ≤ rounds) (hhi : rounds ≤ 3) :
    logicalRound 16 (by decide) (fun _ : Fin 4 => true) (delayFired rounds) =
      delayFired (rounds + 1) := by
  have hr : rounds = 1 ∨ rounds = 2 ∨ rounds = 3 := by omega
  rcases hr with rfl | rfl | rfl <;>
    funext i <;>
    rcases delay_site_cases i with rfl | rfl | rfl | rfl <;>
    simp [delayFired, logicalRound, phaseStep, phaseUpdate, left, right]

/-- Four true rounds create a second anchor at site three. -/
theorem delay_true_escape :
    anchorCount (by decide)
      (runRounds 16 (by decide) (List.replicate 4 (fun _ : Fin 4 => true))
        (delaySnapshot 0)) = 2 := by
  simp only [List.replicate_succ, List.replicate_zero, runRounds]
  rw [delay_true_first, delay_true_step 1 (by decide) (by decide),
    delay_true_step 2 (by decide) (by decide), delay_true_step 3 (by decide) (by decide)]
  rfl

/-- The staircase's height order has exactly one anchor, independently of its countdown. -/
theorem delay_anchor_count (z : Nat) : anchorCount (by decide) (delaySnapshot z) = 1 := by
  rfl

/-- Arbitrarily many false rounds retain exactly one anchor, but that very
execution has a finite continuation creating two anchors. Thus a reached
singleton does not by itself certify permanent singleton behavior outside
the bounded-height domain. -/
theorem delay_singleton_not_closed (q : Nat) :
    anchorCount (by decide)
      (runRounds 16 (by decide) (List.replicate q (fun _ : Fin 4 => false))
        (delaySnapshot 0)) = 1 ∧
    ∃ tail : List (Fin 4 → Bool),
      anchorCount (by decide)
        (runRounds 16 (by decide)
          (List.replicate q (fun _ : Fin 4 => false) ++ tail)
          (delaySnapshot 0)) = 2 := by
  obtain ⟨z, hz, he⟩ := delay_false_family 0 q (by decide)
  constructor
  · rw [he]
    exact delay_anchor_count z
  · refine ⟨List.replicate z (fun _ : Fin 4 => false) ++
      List.replicate 4 (fun _ : Fin 4 => true), ?_⟩
    rw [runRounds_append, he, runRounds_append, delay_false_drain z hz]
    exact delay_true_escape

end L4.Height
namespace L4.Height.PhysicalDelay
open L4.Height
open L4.Compiler.Native

def siteLetter {m : Nat} (i : Fin m) (b : Bool) : Fin (2*m) :=
  ⟨2*i.val+b.toNat, by cases b <;> simp <;> omega⟩

@[simp] theorem siteLetter_site {m : Nat} (i : Fin m) (b : Bool) :
    physicalSite (siteLetter i b) = i := by
  apply Fin.ext
  cases b with
  | false => change (2*i.val+0)/2=i.val; omega
  | true => change (2*i.val+1)/2=i.val; omega

@[simp] theorem siteLetter_bit {m : Nat} (i : Fin m) (b : Bool) :
    physicalBit (siteLetter i b) = b := by
  cases b <;> simp [siteLetter, physicalBit, Nat.add_mod, Nat.mul_mod]

def sweep {m : Nat} (bits : Fin m → Bool) : List (Activation m) :=
  (List.finRange m).map (fun i => (i,bits i))

def sweeps {m : Nat} (bits : Fin m → Bool) : Nat → List (Activation m)
  | 0 => []
  | n+1 => sweep bits ++ sweeps bits n

private theorem run_append {m B M : Nat} (hm : 0<m)
    (h k : List (Activation m)) (s : WordState m) :
    syncRun B M hm (h++k) s = syncRun B M hm k (syncRun B M hm h s) := by
  induction h generalizing s with
  | nil => rfl
  | cons e h ih => exact ih (activate B M hm s e.1 e.2)

private theorem sweep_aux {m B M : Nat} (hm : 0<m) (hM : ClockParams M)
    (bits : Fin m → Bool) (ell : Nat) (todo : List (Fin m))
    (hn : todo.Nodup) (s : WordState m) (hs : Legit M hm s)
    (hshape : ∀ j, s.lift j = if j∈todo then ell else ell+1) :
    Legit M hm (syncRun B M hm (todo.map (fun j => (j,bits j))) s) ∧
      ∀ j, (syncRun B M hm (todo.map (fun j => (j,bits j))) s).lift j = ell+1 := by
  induction todo generalizing s with
  | nil => exact ⟨hs, fun j => by simpa [syncRun] using hshape j⟩
  | cons i todo ih =>
      have hnot : i∉todo := (List.nodup_cons.mp hn).1
      have htail : todo.Nodup := (List.nodup_cons.mp hn).2
      have hi : s.lift i=ell := by simpa using hshape i
      have hvals (j : Fin m) : s.lift j=ell ∨ s.lift j=ell+1 := by
        by_cases hj : j∈i::todo
        · exact Or.inl (by simpa [hj] using hshape j)
        · exact Or.inr (by simpa [hj] using hshape j)
      have hcan : CanAdvance hm s.lift i := by
        constructor
        · simpa [hi] using hvals (left hm i)
        · simpa [hi] using hvals (right hm i)
      have ha : clockAction M hm s i = .inc (clockOf M (s.lift i+1)) := by
        rw [nativeClock_normal hM hm s hs i,
          (canAdvanceBool_eq_true hm s.lift i).2 hcan]
        simp
      have hnext : ∀ j, (activate B M hm s i (bits i)).lift j =
          if j∈todo then ell else ell+1 := by
        intro j
        by_cases hji : j=i
        · subst j
          simp [activate,ha,advanceLift,hi,hnot]
        · simp [activate,hji]
          simpa [List.mem_cons,hji] using hshape j
      exact ih htail (activate B M hm s i (bits i))
        (legit_activate hM hm s hs i (bits i)) hnext

theorem sweep_advances {m B M : Nat} (hm : 0<m) (hM : ClockParams M)
    (bits : Fin m → Bool) (s : WordState m) (hs : Legit M hm s)
    (ell : Nat) (hflat : ∀ j, s.lift j=ell) :
    Legit M hm (syncRun B M hm (sweep bits) s) ∧
      ∀ j, (syncRun B M hm (sweep bits) s).lift j=ell+1 := by
  apply sweep_aux hm hM bits ell (List.finRange m) (List.nodup_finRange m) s hs
  intro j
  simpa using hflat j

theorem sweeps_advance {m B M : Nat} (hm : 0<m) (hM : ClockParams M)
    (bits : Fin m → Bool) (n : Nat) (s : WordState m) (hs : Legit M hm s)
    (ell : Nat) (hflat : ∀ j, s.lift j=ell) :
    Legit M hm (syncRun B M hm (sweeps bits n) s) ∧
      ∀ j, (syncRun B M hm (sweeps bits n) s).lift j=ell+n := by
  induction n generalizing s ell with
  | zero => exact ⟨hs, by simpa [sweeps,syncRun] using hflat⟩
  | succ n ih =>
      obtain ⟨hl,hf⟩ := sweep_advances hm hM bits s hs ell hflat
      have ht := ih (syncRun B M hm (sweep bits) s) hl (ell+1) hf
      simpa [sweeps,run_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht

private theorem honors_fixed {m B M : Nat} (hm : 0<m)
    (bits : Fin m → Bool) (h : List (Activation m))
    (hb : ∀ e∈h, e.2=bits e.1) (s : WordState m) :
    Honors B M hm (fun _ => bits) s h := by
  induction h generalizing s with
  | nil => trivial
  | cons e h ih =>
      have he : e.2=bits e.1 := hb e (by simp)
      change (match clockAction M hm s e.1 with
        | .inc _ => clockOf M (s.lift e.1)%32≠1 ∨ e.2=bits e.1
        | _ => True) ∧ Honors B M hm (fun _ => bits) (activate B M hm s e.1 e.2) h
      constructor
      · cases clockAction M hm s e.1 <;> simp [he]
      · apply ih
        intro a ha
        exact hb a (by simp [ha])

private theorem sweeps_bits {m : Nat} (bits : Fin m → Bool) (n : Nat) :
    ∀ e∈sweeps bits n, e.2=bits e.1 := by
  induction n with
  | zero => simp [sweeps]
  | succ n ih =>
      intro e he
      change e∈sweep bits ++ sweeps bits n at he
      rcases List.mem_append.mp he with he|he
      · obtain ⟨i,_,hi⟩ := List.mem_map.mp he
        cases hi
        rfl
      · exact ih e he

def roundWord {m : Nat} (bits : Fin m → Bool) : List (Fin (2*m)) :=
  (sweeps bits 32).map (fun e => siteLetter e.1 e.2)

def roundWords {m : Nat} : List (Fin m → Bool) → List (Fin (2*m))
  | [] => []
  | bits::bs => roundWord bits ++ roundWords bs

private theorem physical_encoded {m B M : Nat} (hm : 0<m)
    (h : List (Activation m)) (s : WordState m) :
    physicalRun B M hm s (h.map (fun e => siteLetter e.1 e.2)) = syncRun B M hm h s := by
  induction h generalizing s with
  | nil => rfl
  | cons e h ih =>
      simpa [physicalRun,physicalNext,syncRun] using ih (activate B M hm s e.1 e.2)

theorem physical_append {m B M : Nat} (hm : 0<m)
    (u v : List (Fin (2*m))) (s : WordState m) :
    physicalRun B M hm s (u++v) = physicalRun B M hm (physicalRun B M hm s u) v := by
  induction u generalizing s with
  | nil => rfl
  | cons e u ih => exact ih (physicalNext B M hm s e)

theorem roundWord_run {m B M : Nat} (hm : 0<m) (hM : ClockParams M)
    (hp : 32∣M/2) (ell : Nat) (hz : ell%32=0)
    (bits : Fin m → Bool) (s : WordState m) (hs : Legit M hm s)
    (hflat : ∀ i, s.lift i=ell) :
    let t := physicalRun B M hm s (roundWord bits)
    Legit M hm t ∧ (∀ i, t.lift i=ell+32) ∧
      (∀ i, (t.cfg i).curr=logicalRound B hm bits (fun j => (s.cfg j).curr) i) := by
  let start := fun j => (s.cfg j).curr
  let h := sweeps bits 32
  have ht := sweeps_advance (B:=B) hm hM bits 32 s hs ell hflat
  have hh : Honors B M hm (fun _ => bits) s h := honors_fixed hm bits h (sweeps_bits bits 32) s
  have hw : StartConsistent B M ell hm (fun _ => bits) start s := by
    intro i
    exact Or.inl ⟨hflat i,rfl⟩
  have hr := syncRun_represents hM hm (fun _ => bits) start h s hs
    (startConsistent_represents hm (fun _ => bits) start s hw) hh
  have he : physicalRun B M hm s (roundWord bits)=syncRun B M hm h s := physical_encoded hm h s
  change Legit M hm (physicalRun B M hm s (roundWord bits)) ∧ _
  rw [he]
  refine ⟨ht.1,ht.2,?_⟩
  intro i
  have hc := hr.2.1 i
  rw [ht.2 i] at hc
  have hoff : ell+32-ell=32 := by omega
  rw [hoff] at hc
  have hsync := syncLevels_runRounds (B:=B) (M:=M) (ellzero:=ell) (k:=1)
    hm (fun _ => bits) start (fun _ => clockOf_mod_phase hp hz)
  rw [hsync] at hc
  simpa [roundBits,runRounds] using hc

theorem roundWords_run {m B M : Nat} (hm : 0<m) (hM : ClockParams M)
    (hp : 32∣M/2) (bs : List (Fin m → Bool))
    (ell : Nat) (hz : ell%32=0) (s : WordState m)
    (hs : Legit M hm s) (hflat : ∀ i, s.lift i=ell) :
    let t := physicalRun B M hm s (roundWords bs)
    Legit M hm t ∧ (∀ i, t.lift i=ell+32*bs.length) ∧
      (∀ i, (t.cfg i).curr=runRounds B hm bs (fun j => (s.cfg j).curr) i) := by
  induction bs generalizing s ell with
  | nil => exact ⟨hs,by simpa [roundWords,physicalRun] using hflat,fun _ => rfl⟩
  | cons bits bs ih =>
      let next := physicalRun B M hm s (roundWord bits)
      obtain ⟨hl,hf,hc⟩ := roundWord_run hm hM hp ell hz bits s hs hflat
      have hz' : (ell+32)%32=0 := by simp [Nat.add_mod,hz]
      have ht := ih (ell+32) hz' next hl hf
      have hcurr : (fun j => (next.cfg j).curr)=logicalRound B hm bits (fun j => (s.cfg j).curr) := funext hc
      simp only [roundWords,physical_append]
      refine ⟨ht.1,?_,?_⟩
      · intro i
        simpa [List.length_cons,Nat.mul_add,Nat.mul_one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht.2.1 i
      · intro i
        simpa only [hcurr,runRounds_cons] using ht.2.2 i

theorem roundWords_length {m : Nat} (bs : List (Fin m → Bool)) :
    (roundWords bs).length=32*m*bs.length := by
  have hs (bits : Fin m → Bool) (n : Nat) : (sweeps bits n).length=n*m := by
    induction n with
    | zero => simp [sweeps]
    | succ n ih => simp [sweeps,sweep,ih,Nat.succ_mul,Nat.add_comm]
  induction bs with
  | nil => simp [roundWords]
  | cons b bs ih => simp [roundWords,roundWord,hs,ih,Nat.mul_add,Nat.add_comm]

def flatClock (M : Nat) {m : Nat} (start : Fin m → Snapshot) : WordState m where
  cfg i := {tick:=clockOf M 0,err:=false,prior:={},curr:=start i}
  lift _ := 0

theorem flatClock_legit {m : Nat} (M : Nat) (hm : 0<m)
    (start : Fin m → Snapshot) : Legit M hm (flatClock M start) := by
  refine ⟨fun _ => rfl,fun _ => rfl,?_⟩
  intro i j _
  change Near 0 0
  exact ⟨by decide,by decide⟩

theorem four_roundWords_run (start : Fin 4 → Snapshot) (bs : List (Fin 4 → Bool)) :
    let t := physicalRun 16 256 (by decide) (flatClock 256 start) (roundWords bs)
    (∀ i, t.lift i=32*bs.length) ∧
      (∀ i, (t.cfg i).curr=runRounds 16 (by decide) bs start i) ∧
      (roundWords bs).length=128*bs.length := by
  have hM : ClockParams 256 := ⟨by decide,by decide⟩
  have ht := roundWords_run (B:=16) (by decide) hM (by decide) bs 0 (by decide)
    (flatClock 256 start) (flatClock_legit 256 (by decide) start) (fun _ => rfl)
  refine ⟨?_,ht.2.2,roundWords_length bs⟩
  simpa using ht.2.1

theorem roundWords_append {m : Nat} (bs cs : List (Fin m → Bool)) :
    roundWords (bs++cs)=roundWords bs ++ roundWords cs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [roundWords,ih,List.append_assoc]

private theorem step_mono {m B M : Nat} (hm : 0<m)
    (s : WordState m) (e : Activation m) (i : Fin m) :
    s.lift i ≤ (activate B M hm s e.1 e.2).lift i := by
  by_cases hi : i=e.1
  · subst i
    cases ha : clockAction M hm s e.1 <;> simp [activate,ha,advanceLift]
  · simp [activate,hi]

private theorem history_mono {m B M : Nat} (hm : 0<m)
    (h : List (Activation m)) (s : WordState m) (i : Fin m) :
    s.lift i ≤ (syncRun B M hm h s).lift i := by
  induction h generalizing s with
  | nil => exact Nat.le_refl _
  | cons e h ih =>
      exact Nat.le_trans (step_mono (B:=B) (M:=M) hm s e i)
        (ih (activate B M hm s e.1 e.2))

private theorem level_now {m B M : Nat} (hm : 0<m)
    (h : List (Activation m)) (s : WordState m) (i : Fin m) (ell : Nat)
    (he : s.lift i=ell) : levelCurr B M hm h s i ell=some (s.cfg i).curr := by
  cases h <;> simp [levelCurr,he]

private theorem curr_same_level {m B M : Nat} (hm : 0<m) (hM : ClockParams M)
    (s : WordState m) (hs : Legit M hm s) (e : Activation m) (i : Fin m)
    (he : (activate B M hm s e.1 e.2).lift i=s.lift i) :
    ((activate B M hm s e.1 e.2).cfg i).curr=(s.cfg i).curr := by
  by_cases hi : i=e.1
  · subst i
    rcases action_inc_or_hold hM hm s hs e.1 with ha|ha
    · simp [activate,ha,advanceLift] at he
    · rw [activate_of_hold hm s e.1 e.2 ha]
  · simp [activate,hi]

private theorem history_endpoint_observation {m B M : Nat}
    (hm : 0<m) (hM : ClockParams M) (h : List (Activation m))
    (s : WordState m) (hs : Legit M hm s) (i : Fin m) (ell : Nat)
    (hf : (syncRun B M hm h s).lift i=ell) :
    levelCurr B M hm h s i ell=some ((syncRun B M hm h s).cfg i).curr := by
  induction h generalizing s with
  | nil =>
      change s.lift i=ell at hf
      simp [levelCurr,syncRun,hf]
  | cons e h ih =>
      let next := activate B M hm s e.1 e.2
      have hnle : next.lift i ≤ ell :=
        Nat.le_trans (history_mono (B:=B) (M:=M) hm h next i) (Nat.le_of_eq hf)
      have ht := ih next (legit_activate hM hm s hs e.1 e.2) hf
      by_cases he : s.lift i=ell
      · have hmono := step_mono (B:=B) (M:=M) hm s e i
        have hne : next.lift i=ell := by change s.lift i ≤ next.lift i at hmono; omega
        have hc := curr_same_level hm hM s hs e i (hne.trans he.symm)
        rw [level_now (B:=B) (M:=M) hm h next i ell hne] at ht
        have hv := Option.some.inj ht
        simp only [levelCurr,if_pos he]
        exact congrArg some (hc.symm.trans hv)
      · simpa only [levelCurr,if_neg he,syncRun,next] using ht

private theorem physical_as_sync {m B M : Nat} (hm : 0<m)
    (s : WordState m) (u : List (Fin (2*m))) :
    physicalRun B M hm s u=syncRun B M hm (u.map physicalActivation) s := by
  induction u generalizing s with
  | nil => rfl
  | cons e u ih => exact ih (physicalNext B M hm s e)

theorem physical_endpoint_observation {m B M : Nat}
    (hm : 0<m) (hM : ClockParams M) (s : WordState m) (hs : Legit M hm s)
    (u : List (Fin (2*m))) (i : Fin m) (ell : Nat)
    (hf : (physicalRun B M hm s u).lift i=ell) :
    levelCurr B M hm (u.map physicalActivation) s i ell=
      some ((physicalRun B M hm s u).cfg i).curr := by
  rw [physical_as_sync] at hf ⊢
  exact history_endpoint_observation hm hM _ s hs i ell hf

theorem four_prefix_observation (start : Fin 4 → Snapshot)
    (bs cs : List (Fin 4 → Bool)) (i : Fin 4) :
    levelCurr 16 256 (by decide) ((roundWords (bs++cs)).map physicalActivation)
      (flatClock 256 start) i (32*bs.length)=some (runRounds 16 (by decide) bs start i) := by
  have ht := four_roundWords_run start bs
  have ho := physical_endpoint_observation (B:=16) (by decide)
    (show ClockParams 256 from ⟨by decide,by decide⟩) (flatClock 256 start)
    (flatClock_legit 256 (by decide) start) (roundWords bs) i (32*bs.length) (ht.1 i)
  rw [ht.2.1 i] at ho
  rw [roundWords_append,List.map_append]
  exact levelCurr_stable 16 256 (by decide) _ _ _ i _ _ ho

end L4.Height.PhysicalDelay



namespace L4.Height.PhysicalDelay
open L4.Height
open L4.Compiler.Native

private theorem replicate_concat {α : Type} (n k : Nat) (x : α) :
    List.replicate (n+k) x=List.replicate n x++List.replicate k x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.succ_add]
      calc
        _ = x :: List.replicate (n+k) x := by apply List.replicate_succ
        _ = x :: (List.replicate n x ++ List.replicate k x) :=
          congrArg (List.cons x) ih
        _ = _ := by rw [List.replicate_succ, List.cons_append]

theorem false_word_observation (a r : Nat) (har : a≤r) (i : Fin 4) :
    levelCurr 16 256 (by decide)
      ((roundWords (List.replicate r (fun _ : Fin 4 => false))).map physicalActivation)
      (flatClock 256 (delaySnapshot 0)) i (32*a)=
        some (runRounds 16 (by decide)
          (List.replicate a (fun _ : Fin 4 => false)) (delaySnapshot 0) i) := by
  have hrepl : List.replicate r (fun _ : Fin 4 => false)=
      List.replicate a (fun _ : Fin 4 => false)++
      List.replicate (r-a) (fun _ : Fin 4 => false) := by
    rw [←replicate_concat]
    congr 1
    omega
  have ho := four_prefix_observation (delaySnapshot 0)
    (List.replicate a (fun _ : Fin 4 => false))
    (List.replicate (r-a) (fun _ : Fin 4 => false)) i
  rw [←hrepl] at ho
  simpa using ho

/-- A physical trial can preserve a singleton observation at any chosen
aligned target until an arbitrary later full-round deadline, yet a finite
continuation reaches an aligned slice with two anchors. -/
theorem physical_delayed_singleton (a r : Nat) (ha : 0<a) (har : a≤r) :
    ∃ (u v : List (Fin 8)) (future : Nat),
      u.length=128*r ∧
      (∀ i : Fin 4, 32*a ≤
        (physicalRun 16 256 (by decide) (flatClock 256 (delaySnapshot 0)) u).lift i) ∧
      anchorCount (by decide)
        (observedSnapshot 16 256 (by decide) (flatClock 256 (delaySnapshot 0)) u (32*a))=1 ∧
      32*a<future ∧ future%32=0 ∧
      (∀ i : Fin 4,
        (physicalRun 16 256 (by decide) (flatClock 256 (delaySnapshot 0)) (u++v)).lift i=future) ∧
      anchorCount (by decide)
        (observedSnapshot 16 256 (by decide) (flatClock 256 (delaySnapshot 0)) (u++v) future)=2 := by
  let fs (n : Nat) := List.replicate n (fun _ : Fin 4 => false)
  let s := flatClock 256 (delaySnapshot 0)
  let u := roundWords (fs r)
  obtain ⟨hdeadline,tail,hbad⟩ := delay_singleton_not_closed r
  let v := roundWords tail
  let future := 32*(r+tail.length)
  have hr := four_roundWords_run (delaySnapshot 0) (fs r)
  have hlast := four_roundWords_run (delaySnapshot 0) (fs r++tail)
  have hobs : observedSnapshot 16 256 (by decide) s u (32*a)=
      runRounds 16 (by decide) (fs a) (delaySnapshot 0) := by
    funext i
    have ho := false_word_observation a r har i
    change levelCurr 16 256 (by decide) (u.map physicalActivation) s i (32*a)=_ at ho
    simp [observedSnapshot,ho,fs]
  have hne : tail≠[] := by
    intro he
    rw [he,List.append_nil] at hbad
    omega
  have htailPos : 0<tail.length := by
    cases tail with
    | nil => exact (hne rfl).elim
    | cons b bs => exact Nat.zero_lt_succ _
  have hfuture : ∀ i : Fin 4,
      (physicalRun 16 256 (by decide) s (u++v)).lift i=future := by
    intro i
    change (physicalRun 16 256 (by decide) s
      (roundWords (fs r)++roundWords tail)).lift i=future
    rw [←roundWords_append]
    simpa [future,fs] using hlast.1 i
  have hfutureCurr : (fun i =>
      ((physicalRun 16 256 (by decide) s (u++v)).cfg i).curr)=
        runRounds 16 (by decide) (fs r++tail) (delaySnapshot 0) := by
    funext i
    change ((physicalRun 16 256 (by decide) s
      (roundWords (fs r)++roundWords tail)).cfg i).curr=_
    rw [←roundWords_append]
    exact hlast.2.1 i
  have hfutureObs : observedSnapshot 16 256 (by decide) s (u++v) future=
      (fun i => ((physicalRun 16 256 (by decide) s (u++v)).cfg i).curr) := by
    funext i
    have ho := physical_endpoint_observation (B:=16) (by decide)
      (show ClockParams 256 from ⟨by decide,by decide⟩) s
      (flatClock_legit 256 (by decide) (delaySnapshot 0)) (u++v) i future (hfuture i)
    change (levelCurr 16 256 (by decide) ((u++v).map physicalActivation)
      s i future).getD ({} : Snapshot)=_
    rw [ho]
    rfl
  refine ⟨u,v,future,?_,?_,?_,?_,?_,hfuture,?_⟩
  · simpa [u,fs] using hr.2.2
  · intro i
    have hi : (physicalRun 16 256 (by decide) s u).lift i=32*r := by
      simpa [s,u,fs] using hr.1 i
    rw [hi]
    exact Nat.mul_le_mul_left 32 har
  · rw [hobs]
    exact (delay_singleton_not_closed a).1
  · dsimp [future]
    omega
  · simp [future,Nat.mul_mod]
  · rw [hfutureObs,hfutureCurr]
    exact hbad

end L4.Height.PhysicalDelay

namespace L4.Height.PhysicalDelay
open L4.Height
open L4.Compiler.Native

theorem delay_initial_coset :
    LegitCoset 256 (by decide) (flatClock 256 (delaySnapshot 0)) := by
  refine ⟨fun _ => rfl,?_,?_,?_,?_⟩
  · intro i
    simp [flatClock,clockOf]
  · intro i j _
    change Near 0 0
    exact ⟨by decide,by decide⟩
  · intro i
    change 128<256
    decide
  · intro i hi
    change false=true at hi
    cases hi

/-- The delayed escape begins inside the concrete native LgSet, with the
same four-site physical alphabet used by the deadline witness. -/
theorem delay_initial_lgSet :
    Recover.Chain.LgSet (clockChain (B:=16) (M:=256) (by decide))
      (flatClock 256 (delaySnapshot 0),none) := by
  refine ⟨delay_initial_coset.clean,delay_initial_coset.quiet,?_⟩
  intro i
  change (128 : Nat)<256 ∧ (false=true → (128 : Nat)<256/2)
  decide

/-- Q=2^19*m, base=32>initial maximum, exact deadline d=2^30*L*m.
The later slice refutes permanence even though the target is reached and
its actual observed snapshot is a singleton at that exact deadline. -/
theorem requested_deadline_delayed_singleton (L : Nat) (hL : 1≤L) :
    ∃ (u v : List (Fin 8)) (future : Nat),
      u.length=2^30*L*4 ∧
      (∀ i : Fin 4, 32+32*(2^19*4) ≤
        (physicalRun 16 256 (by decide) (flatClock 256 (delaySnapshot 0)) u).lift i) ∧
      anchorCount (by decide)
        (observedSnapshot 16 256 (by decide) (flatClock 256 (delaySnapshot 0)) u
          (32+32*(2^19*4)))=1 ∧
      32+32*(2^19*4)<future ∧ future%32=0 ∧
      (∀ i : Fin 4,
        (physicalRun 16 256 (by decide) (flatClock 256 (delaySnapshot 0)) (u++v)).lift i=future) ∧
      anchorCount (by decide)
        (observedSnapshot 16 256 (by decide) (flatClock 256 (delaySnapshot 0)) (u++v) future)=2 := by
  have hmin : 2^25≤2^25*L := by simpa using Nat.mul_le_mul_left (2^25) hL
  have har : 1+2^19*4≤2^25*L := by omega
  have h := physical_delayed_singleton (1+2^19*4) (2^25*L) (by omega) har
  have hlen : 128*(2^25*L)=2^30*L*4 := by omega
  have htarget : 32*(1+2^19*4)=32+32*(2^19*4) := by omega
  simpa only [hlen,htarget] using h

end L4.Height.PhysicalDelay
#print axioms L4.Height.clock_served_moment_explicit
#print axioms L4.Height.clock_lgSet_aligned_overrun
#print axioms L4.Height.ClockHead.clock_coset_virtual_observation
#print axioms L4.Height.ClockHead.warm_inclusive_quarter
#print axioms L4.Height.ClockHead.virtualNativeR_permanent
#print axioms L4.Height.ClockHead.clock_layer_headline_of_slice
#print axioms L4.Height.ClockHead.clock_layer_headline_counterexample
#print axioms L4.Height.ClockHead.warm_native_trial
#print axioms L4.Height.PhysicalDelay.requested_deadline_delayed_singleton

