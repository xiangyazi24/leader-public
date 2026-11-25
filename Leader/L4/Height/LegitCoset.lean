import Leader.L4.Height.ChainRepair
import Leader.L4.Height.OverrunChain
import Leader.L4.Height.SyncAlt

/-! Recovery and the lifted clock meet at a coset modulo the half-period.
Quietness retains the native edge information needed by the front guard. -/
namespace L4.Height

open L4.Compiler.Native
open Recover

variable {m : Nat}

/-- A lift of an error-free quiet configuration with its physical tick range. -/
structure LegitCoset {m : Nat} (M : Nat) (hm : 0 < m) (s : WordState m) : Prop where
  clean : ∀ i, (s.cfg i).err = false
  residue : ∀ i, (s.cfg i).tick % (M / 2) = s.lift i % (M / 2)
  near : ∀ {i j}, Adjacent hm i j → Near (s.lift i) (s.lift j)
  range : ∀ i, (s.cfg i).tick < M
  quiet : StageThree.Quiet M hm s.cfg

private theorem successor_edge_of_legitimate {M : Nat} {a b : NativeRecord}
    (ha : a.tick < M) (hb : b.tick < M) (h : StageThree.LegitimateEdge M a b) :
    b.tick = a.tick ∨ b.tick = successor M a.tick ∨ a.tick = successor M b.tick := by
  rcases h with h | h | h | ⟨ha', hb'⟩ | ⟨hb', ha'⟩
  · exact Or.inl h.symm
  · have ht : a.tick ≠ M - 1 := by omega
    exact Or.inr (Or.inl (by simpa [successor, ht] using h.symm))
  · have ht : b.tick ≠ M - 1 := by omega
    exact Or.inr (Or.inr (by simpa [successor, ht] using h.symm))
  · exact Or.inr (Or.inl (by simp [successor, ha', hb']))
  · exact Or.inr (Or.inr (by simp [successor, hb', ha']))

/-- Every quiet, correct edge, in either orientation, is a native clock edge. -/
theorem coset_edge {M : Nat} (hm : 0 < m)
    (c : Fin m → NativeRecord) (herr : ∀ i, (c i).err = false)
    (hq : StageThree.Quiet M hm c) (hrange : ∀ i, (c i).tick < M)
    {i j : Fin m} (hij : Adjacent hm i j) :
    (c j).tick = (c i).tick ∨ (c j).tick = successor M (c i).tick ∨
      (c i).tick = successor M (c j).tick := by
  have edges := StageThree.legitimate_of_correct_quiet hm c herr hq
  rcases hij with rfl | rfl
  · have h := edges (left hm i)
    rw [sync_right_left] at h
    rcases successor_edge_of_legitimate (hrange _) (hrange _) h with he | hf | hb
    · exact Or.inl he.symm
    · exact Or.inr (Or.inr hf)
    · exact Or.inr (Or.inl hb)
  · exact successor_edge_of_legitimate (hrange _) (hrange _) (edges i)

/-! A missing residue cuts the phase circle.  Since there are fewer sites
than residues, such a cut exists.  Unit edges cannot cross the cut because
crossing would require one endpoint to occupy the missing residue. -/

private def cosetCut (P q r : Nat) : Nat :=
  if r < q then P + r else r

private theorem cosetCut_mod {P q r : Nat} (hr : r < P) :
    cosetCut P q r % P = r := by
  unfold cosetCut
  split
  · simp [Nat.mod_eq_of_lt hr]
  · exact Nat.mod_eq_of_lt hr

private theorem cosetCut_near_forward {P q a b : Nat}
    (ha : a < P) (hq : q < P)
    (hbq : b ≠ q)
    (hab : b = (a + 1) % P) :
    Near (cosetCut P q a) (cosetCut P q b) := by
  by_cases hnext : a + 1 < P
  · have hab' : b = a + 1 := by
      simpa only [Nat.mod_eq_of_lt hnext] using hab
    unfold cosetCut Near
    split <;> split <;> omega
  · have hlast : a + 1 = P := by omega
    have hbzero : b = 0 := by simpa only [hlast, Nat.mod_self] using hab
    have hqpos : 0 < q := by omega
    have haq' : ¬ a < q := by omega
    have hbq' : b < q := by omega
    simp only [cosetCut, if_neg haq', if_pos hbq']
    unfold Near
    omega

private theorem coset_successor_mod {M t : Nat}
    (hM : ClockParams M) :
    successor M t % (M / 2) = (t % (M / 2) + 1) % (M / 2) := by
  have hp : 0 < M / 2 := by have := hM.1; omega
  have hpone : 1 < M / 2 := by have := hM.1; omega
  by_cases ht : t = M - 1
  · have hlast : t = (M / 2 - 1) + M / 2 := by
      have := hM.2
      omega
    have hlt : M / 2 - 1 < M / 2 := by omega
    have hres : t % (M / 2) = M / 2 - 1 := by
      rw [hlast]
      simp [Nat.mod_eq_of_lt hlt]
    have hsum : M / 2 - 1 + 1 = M / 2 := by omega
    simp only [successor, if_pos ht, Nat.mod_self, hres, hsum]
  · simp [successor, ht, Nat.add_mod, Nat.mod_eq_of_lt hpone]

/-- A sparse phase circle admits a coherent natural lift above any chosen
base.  The construction cuts at an unoccupied residue and uses only the
unit-edge hypothesis; in particular it also handles aliased cycle ports. -/
theorem coset_lift_exists {m M : Nat} (hm : 0 < m)
    (hM : ClockParams M) (hmP : m < M / 2)
    (c : Fin m → NativeRecord)
    (hedge : ∀ {i j}, Adjacent hm i j →
      (c j).tick = (c i).tick ∨
      (c j).tick = successor M (c i).tick ∨
      (c i).tick = successor M (c j).tick)
    (base : Nat) :
    ∃ lift : Fin m → Nat,
      (∀ i, base ≤ lift i) ∧
      (∀ i, (c i).tick % (M / 2) = lift i % (M / 2)) ∧
      (∀ {i j}, Adjacent hm i j → Near (lift i) (lift j)) := by
  classical
  let P := M / 2
  have hp : 0 < P := by have := hM.1; dsimp [P]; omega
  let residue : Fin m → Fin P :=
    fun i => ⟨(c i).tick % P, Nat.mod_lt _ hp⟩
  have hmissing : ∃ q : Fin P, ∀ i, (residue i).val ≠ q.val := by
    apply Classical.byContradiction
    intro hnone
    have hcover : List.finRange P ⊆ List.ofFn residue := by
      intro q _
      have hpre : ∃ i, (residue i).val = q.val := by
        apply Classical.byContradiction
        intro hpre
        exact hnone ⟨q, fun i he => hpre ⟨i, he⟩⟩
      obtain ⟨i, hi⟩ := hpre
      exact List.mem_ofFn.mpr ⟨i, Fin.ext hi⟩
    have hlen := List.Nodup.length_le_of_subset
      (List.nodup_finRange P) hcover
    have hPm : P ≤ m := by simpa only [List.length_finRange, List.length_ofFn] using hlen
    exact (Nat.not_le_of_lt hmP) hPm
  obtain ⟨q, hq⟩ := hmissing
  let lift : Fin m → Nat :=
    fun i => base * P + cosetCut P q.val ((c i).tick % P)
  have hbase : base ≤ base * P := by
    have hh := Nat.mul_le_mul_left base (show 1 ≤ P by omega)
    simpa only [Nat.mul_one] using hh
  refine ⟨lift, ?_, ?_, ?_⟩
  · intro i
    dsimp [lift]
    omega
  · intro i
    change (c i).tick % P =
      (base * P + cosetCut P q.val ((c i).tick % P)) % P
    rw [Nat.add_mod, Nat.mul_mod]
    simp only [Nat.mod_self, Nat.mul_zero, Nat.zero_mod, Nat.zero_add, Nat.mod_mod]
    exact (cosetCut_mod (Nat.mod_lt _ hp)).symm
  · intro i j hij
    have hi : (c i).tick % P < P := Nat.mod_lt _ hp
    have hj : (c j).tick % P < P := Nat.mod_lt _ hp
    have hqi : (c i).tick % P ≠ q.val := hq i
    have hqj : (c j).tick % P ≠ q.val := hq j
    have hnear : Near (cosetCut P q.val ((c i).tick % P))
        (cosetCut P q.val ((c j).tick % P)) := by
      rcases hedge hij with heq | hforward | hbackward
      · rw [heq]
        unfold Near
        omega
      · apply cosetCut_near_forward hi q.isLt hqj
        rw [hforward]
        exact coset_successor_mod hM
      · apply near_symm
        apply cosetCut_near_forward hj q.isLt hqi
        rw [hbackward]
        exact coset_successor_mod hM
    dsimp [lift]
    unfold Near at hnear ⊢
    omega

/-- Recovery supplies a lift with an arbitrary prescribed floor. -/
theorem lgSet_coset {α : Type} {n B M : Nat} {hm : 0 < m}
    (C : Chain.ClockChain α n m B M hm) (x : α)
    (hx : Chain.LgSet C x) (hmP : m < M / 2) (hM : ClockParams M) (base : Nat) :
    ∃ lift : Fin m → Nat, (∀ i, base ≤ lift i) ∧ LegitCoset M hm ⟨C.cfg x, lift⟩ := by
  have bound : ∀ i, (C.cfg x i).tick < M := fun i => (hx.2.2 i).1
  obtain ⟨lift, floor, residue, near⟩ :=
    coset_lift_exists hm hM hmP (C.cfg x)
      (fun h => coset_edge hm (C.cfg x) hx.1 hx.2.1 bound h) base
  exact ⟨lift, floor, hx.1, residue, near, bound, hx.2.1⟩

/-- Select the upper representative of a correct clock, retaining both snapshots. -/
def canonRec (M : Nat) (r : NativeRecord) : NativeRecord :=
  if r.err then r else {r with tick := clockOf M r.tick}

/-- Canonicalization changes only the readout. -/
def canon (M : Nat) (s : WordState m) : WordState m :=
  ⟨fun i => canonRec M (s.cfg i), s.lift⟩

theorem canon_legit {M : Nat} {hm : 0 < m} {s : WordState m}
    (hc : LegitCoset M hm s) : Legit M hm (canon M s) := by
  refine ⟨?_, ?_, hc.near⟩
  · intro i
    simp [canon, canonRec, hc.clean i]
  · intro i
    simp [canon, canonRec, hc.clean i, clockOf, hc.residue i]

/-- A chain can already meet the recovery target with every site at tick zero. -/
private def flatClock (_ : Fin 4) : NativeRecord := ⟨0, false, {}, {}⟩

private def flatClockChain : Chain.ClockChain Unit 4 4 1 16 (by decide) where
  next := fun x _ => x
  cfg := fun _ => flatClock
  act := fun _ _ => none
  lastAct := fun _ => none
  cfg_next := fun _ _ => rfl
  last_next := fun _ _ => rfl

private theorem flatClock_lgSet : Chain.LgSet flatClockChain () := by
  refine ⟨fun _ => rfl, ?_, ?_⟩
  · intro i hr
    change false = true at hr
    cases hr
  · intro i
    change 0 < 16 ∧ (false = true → 0 < 16 / 2)
    decide

/-- At this recovery cut the first activation sets the raw anchor in phase
zero and keeps the canonical anchor clear in phase eight, for every lift. -/
theorem lgSet_projection_counterexample :
    ClockParams 16 ∧ 4 < 16 / 2 ∧ Chain.LgSet flatClockChain () ∧
    ∀ lift : Fin 4 → Nat,
      let s : WordState 4 := ⟨flatClockChain.cfg (), lift⟩
      ((canon 16 (activate 1 16 (by decide) s 0 false)).cfg 0).curr.anchor = true ∧
      ((activate 1 16 (by decide) (canon 16 s) 0 false).cfg 0).curr.anchor = false ∧
      canon 16 (activate 1 16 (by decide) s 0 false) ≠
        activate 1 16 (by decide) (canon 16 s) 0 false := by
  refine ⟨⟨by decide, by decide⟩, by decide, flatClock_lgSet, ?_⟩
  intro lift
  refine ⟨rfl, rfl, ?_⟩
  intro heq
  have h := congrArg (fun t : WordState 4 => (t.cfg 0).curr.anchor) heq
  change true = false at h
  cases h

/-- The failed one-step projection has an explicit coherent lift. -/
theorem canon_activate_counterexample :
    ∃ s : WordState 4, LegitCoset 16 (by decide) s ∧
      canon 16 (activate 1 16 (by decide) s 0 false) ≠
        activate 1 16 (by decide) (canon 16 s) 0 false := by
  let lift : Fin 4 → Nat := fun _ => 0
  let s : WordState 4 := ⟨flatClockChain.cfg (), lift⟩
  refine ⟨s, ⟨flatClock_lgSet.1, fun _ => rfl, ?_,
    fun i => (flatClock_lgSet.2.2 i).1, flatClock_lgSet.2.1⟩,
    (lgSet_projection_counterexample.2.2.2 lift).2.2⟩
  intro i j _
  change Near 0 0
  exact ⟨by decide, by decide⟩

/-- Install a fixed native activation as a scheduler step to reuse recovery closure. -/
private def fixedClockChain {B M : Nat} (hm : 0 < m) (i : Fin m) (b : Bool) :
    Chain.ClockChain (WordState m) 1 m B M hm where
  next := fun s _ => activate B M hm s i b
  cfg := WordState.cfg
  act := fun _ _ => some (i, b)
  lastAct := fun _ => some i
  cfg_next := fun _ _ => rfl
  last_next := fun _ _ => rfl

private theorem lg_after_activate {B M : Nat} {hm : 0 < m} {s : WordState m}
    (hM : ClockParams M) (hc : LegitCoset M hm s) (i : Fin m) (b : Bool) :
    let t := activate B M hm s i b
    (∀ j, (t.cfg j).err = false) ∧ StageThree.Quiet M hm t.cfg ∧
      StageTwo.WellFormed M t.cfg := by
  let C := fixedClockChain (B := B) (M := M) hm i b
  apply Chain.lg_closed C ⟨by have := hM.1; omega, hM.2⟩ s 0
  refine ⟨hc.clean, hc.quiet, fun j => ⟨hc.range j, ?_⟩⟩
  intro h
  change (s.cfg j).err = true at h
  rw [hc.clean] at h
  cases h

/-- Upper-half ticks are fixed by normalization. -/
theorem clockOf_upper {M t : Nat} (hM : ClockParams M)
    (hlo : M / 2 ≤ t) (hhi : t < M) : clockOf M t = t := by
  have hp := hM.2
  have hrem : t - M / 2 < M / 2 := by omega
  have he : t = M / 2 + (t - M / 2) := by omega
  calc
    clockOf M t = M / 2 + ((M / 2 + (t - M / 2)) % (M / 2)) :=
      congrArg (fun z => M / 2 + z % (M / 2)) he
    _ = t := by
      rw [Nat.add_mod]
      simp only [Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt hrem]
      omega

/-- Normalization commutes with the native successor on its decoded range. -/
theorem clockOf_successor {M t : Nat} (hM : ClockParams M) (ht : t < M) :
    clockOf M (successor M t) = successor M (clockOf M t) := by
  by_cases hlast : t = M - 1
  · have hp := hM.1
    have hd := hM.2
    have hu : clockOf M t = t := clockOf_upper hM (by omega) ht
    rw [successor, if_pos hlast, hu, successor, if_pos hlast]
    simp [clockOf]
  · rw [successor, if_neg hlast]
    exact clockOf_succ hM

/-- The successor cannot fix a native tick, including lower-half ticks. -/
theorem successor_raw_ne_self {M t : Nat} (hM : ClockParams M)
    (_ht : t < M) : successor M t ≠ t := by
  have hp := hM.1
  have hd := hM.2
  unfold successor
  split <;> omega

/-- Two native successors cannot return to the starting tick. -/
theorem successor_raw_twice_ne_self {M t : Nat} (hM : ClockParams M)
    (_ht : t < M) : successor M (successor M t) ≠ t := by
  have hp := hM.1
  have hd := hM.2
  unfold successor
  by_cases hlast : t = M - 1
  · have hpnot : M / 2 ≠ M - 1 := by omega
    simp only [if_pos hlast, if_neg hpnot]
    omega
  · simp only [if_neg hlast]
    by_cases hnext : t + 1 = M - 1
    · simp only [if_pos hnext]
      omega
    · simp only [if_neg hnext]
      omega

/-- On a legitimate edge normalization preserves the equality selector. -/
theorem clockOf_edge_eq {M t u : Nat} (hM : ClockParams M)
    (ht : t < M) (hu : u < M)
    (hedge : u = t ∨ u = successor M t ∨ t = successor M u) :
    clockOf M u = clockOf M t ↔ u = t := by
  rcases hedge with he | he | he
  · subst u
    simp
  · subst u
    rw [clockOf_successor hM ht]
    have hn := successor_ne_self hM (clockOf_window (ell := t) hM)
    have hr := successor_raw_ne_self hM ht
    simp [hn, hr]
  · subst t
    rw [clockOf_successor hM hu]
    have hn := successor_ne_self hM (clockOf_window (ell := u) hM)
    have hr := successor_raw_ne_self hM hu
    constructor
    · intro heq
      exact False.elim (hn heq.symm)
    · intro heq
      exact False.elim (hr heq.symm)

/-- On a legitimate edge normalization preserves the front classifier. -/
theorem clockOf_edge_front {M t u : Nat} (hM : ClockParams M)
    (ht : t < M) (hu : u < M)
    (hedge : u = t ∨ u = successor M t ∨ t = successor M u) :
    tickFrontBool M (clockOf M t) (clockOf M u) = tickFrontBool M t u := by
  rcases hedge with he | he | he
  · subst u
    simp [tickFrontBool]
  · subst u
    rw [clockOf_successor hM ht]
    simp [tickFrontBool]
  · subst t
    rw [clockOf_successor hM hu]
    have hn := successor_ne_self hM (clockOf_window (ell := u) hM)
    have hnn := successor_twice_ne_self hM (clockOf_window (ell := u) hM)
    have hr := successor_raw_ne_self hM hu
    have hrr := successor_raw_twice_ne_self hM hu
    have ha : u ≠ successor M u := Ne.symm hr
    have hb : u ≠ successor M (successor M u) := Ne.symm hrr
    have hc : clockOf M u ≠ successor M (clockOf M u) := Ne.symm hn
    have hd : clockOf M u ≠ successor M (successor M (clockOf M u)) :=
      Ne.symm hnn
    simp [tickFrontBool, ha, hb, hc, hd]

/-- Quiet clean records have neither upper-gap guard set. -/
theorem coset_upper_gaps {M : Nat} (hm : 0 < m) (s : WordState m)
    (hcos : LegitCoset M hm s) (i : Fin m) :
    upperGapBool M (s.cfg i).tick (s.cfg (left hm i)).tick = false ∧
      upperGapBool M (s.cfg i).tick (s.cfg (right hm i)).tick = false := by
  have hroot : StageThree.rootB M (s.cfg (left hm i)) (s.cfg i)
      (s.cfg (right hm i)) = false := by
    cases he : StageThree.rootB M (s.cfg (left hm i)) (s.cfg i)
        (s.cfg (right hm i)) with
    | false => rfl
    | true =>
      have hh := (hcos.quiet i he).1
      rw [hcos.clean i] at hh
      cases hh
  simpa [StageThree.rootB, hcos.clean i, StageThree.upperGapB,
    upperGapBool] using hroot

/-- Raw and normalized clocks have the same two front bits. -/
theorem coset_front {M : Nat} (hM : ClockParams M) (hm : 0 < m)
    (s : WordState m) (hcos : LegitCoset M hm s) (i j : Fin m)
    (hadj : Adjacent hm i j) :
    tickFrontBool M ((canon M s).cfg i).tick ((canon M s).cfg j).tick =
      tickFrontBool M (s.cfg i).tick (s.cfg j).tick := by
  have hedge := coset_edge hm s.cfg hcos.clean hcos.quiet hcos.range hadj
  simpa [canon, canonRec, hcos.clean] using
    clockOf_edge_front hM (hcos.range i) (hcos.range j) hedge

/-- The literal raw clock has the same lifted advance classifier as its
normalized representative, while retaining its own successor tick. -/
theorem coset_clock_normal {M : Nat} (hM : ClockParams M) (hm : 0 < m)
    (s : WordState m) (hcos : LegitCoset M hm s) (i : Fin m) :
    clockAction M hm s i =
      if canAdvanceBool hm s.lift i = true then
        ClockAction.inc (successor M (s.cfg i).tick) else ClockAction.hold := by
  have hg := coset_upper_gaps hm s hcos i
  have hc := nativeClock_clean M (s.cfg (left hm i)) (s.cfg i)
    (s.cfg (right hm i)) (hcos.clean _) (hcos.clean _) (hcos.clean _) hg.1 hg.2
  have hfront :
      (tickFrontBool M (s.cfg i).tick (s.cfg (left hm i)).tick &&
        tickFrontBool M (s.cfg i).tick (s.cfg (right hm i)).tick) =
        canAdvanceBool hm s.lift i := by
    rw [← coset_front hM hm s hcos i (left hm i) (Or.inl rfl),
      ← coset_front hM hm s hcos i (right hm i) (Or.inr rfl)]
    have hleg := canon_legit hcos
    simp only [hleg.2.1]
    change (frontBool M (s.lift i) (s.lift (left hm i)) &&
      frontBool M (s.lift i) (s.lift (right hm i))) = _
    rw [frontBool_eq hM (hcos.near (Or.inl rfl)),
      frontBool_eq hM (hcos.near (Or.inr rfl))]
    rfl
  change nativeClock M (s.cfg (left hm i)) (s.cfg i) (s.cfg (right hm i)) = _
  rw [hc, hfront]

/-- Raw and normalized activations advance exactly the same lifted sites. -/
theorem coset_activate_lift {B M : Nat} (hM : ClockParams M) (hm : 0 < m)
    (s : WordState m) (hcos : LegitCoset M hm s) (i : Fin m) (b : Bool) :
    (activate B M hm s i b).lift = (activate B M hm (canon M s) i b).lift := by
  have hr := coset_clock_normal hM hm s hcos i
  have hc := nativeClock_normal hM hm (canon M s) (canon_legit hcos) i
  have hc' : clockAction M hm (canon M s) i =
      if canAdvanceBool hm s.lift i = true then
        ClockAction.inc (clockOf M (s.lift i + 1)) else ClockAction.hold := hc
  change setAt s.lift i (advanceLift (clockAction M hm s i) (s.lift i)) =
    setAt s.lift i (advanceLift (clockAction M hm (canon M s) i) (s.lift i))
  rw [hr, hc']
  cases canAdvanceBool hm s.lift i <;> rfl

/-- Every raw activation preserves tick/lift agreement modulo the half-period. -/
theorem coset_activate_residue {B M : Nat} (hM : ClockParams M) (hm : 0 < m)
    (s : WordState m) (hcos : LegitCoset M hm s) (i : Fin m) (b : Bool) :
    ∀ j, ((activate B M hm s i b).cfg j).tick % (M / 2) =
      (activate B M hm s i b).lift j % (M / 2) := by
  intro j
  have hr := coset_clock_normal hM hm s hcos i
  by_cases hji : j = i
  · subst j
    cases hb : canAdvanceBool hm s.lift i with
    | false => simpa [activate, hr, hb, finishNative, advanceLift] using hcos.residue i
    | true =>
      have he : clockOf M (successor M (s.cfg i).tick) =
          clockOf M (s.lift i + 1) := by
        rw [clockOf_successor hM (hcos.range i), clockOf_succ hM]
        simp only [clockOf, hcos.residue i]
      have hmres : (successor M (s.cfg i).tick) % (M / 2) =
          (s.lift i + 1) % (M / 2) := by
        unfold clockOf at he
        omega
      simpa [activate, hr, hb, finishNative, advanceLift] using hmres
  · simpa [activate, hji] using hcos.residue j

/-- Normalization preserves the neighbor selector on each legitimate edge. -/
theorem coset_neighborView {M : Nat} (hM : ClockParams M) (hm : 0 < m)
    (s : WordState m) (hcos : LegitCoset M hm s) (i j : Fin m)
    (hadj : Adjacent hm i j) :
    neighborView ((canon M s).cfg i).tick ((canon M s).cfg j) =
      neighborView (s.cfg i).tick (s.cfg j) := by
  have hedge := coset_edge hm s.cfg hcos.clean hcos.quiet hcos.range hadj
  have he := clockOf_edge_eq hM (hcos.range i) (hcos.range j) hedge
  simp only [canon, canonRec, hcos.clean, Bool.false_eq_true, ↓reduceIte]
  unfold neighborView
  simp only [he]

/-- The two phase choices give identical snapshot updates at every actual
increment. Neighbor snapshots are read from the same raw configuration. -/
def UpdateAgrees (B M : Nat) (hm : 0 < m) (s : WordState m) (i : Fin m)
    (b : Bool) : Prop :=
  canAdvanceBool hm s.lift i = true →
    phaseUpdate B ((s.cfg i).tick % 32)
      (neighborView (s.cfg i).tick (s.cfg (left hm i))) (s.cfg i).curr
      (neighborView (s.cfg i).tick (s.cfg (right hm i))) b =
    phaseUpdate B (((canon M s).cfg i).tick % 32)
      (neighborView (s.cfg i).tick (s.cfg (left hm i))) (s.cfg i).curr
      (neighborView (s.cfg i).tick (s.cfg (right hm i))) b

/-- Full record commutation holds exactly when the two phases give the same
snapshot update on the selected activation. -/
theorem canon_activate_iff_update {B M : Nat} (hM : ClockParams M) (hm : 0 < m)
    (s : WordState m) (hcos : LegitCoset M hm s) (i : Fin m) (b : Bool) :
    canon M (activate B M hm s i b) = activate B M hm (canon M s) i b ↔
      UpdateAgrees B M hm s i b := by
  unfold UpdateAgrees
  have hr := coset_clock_normal hM hm s hcos i
  have hc : clockAction M hm (canon M s) i =
      if canAdvanceBool hm s.lift i = true then
        ClockAction.inc (clockOf M (s.lift i + 1)) else ClockAction.hold :=
    nativeClock_normal hM hm (canon M s) (canon_legit hcos) i
  have hrawself : (activate B M hm s i b).cfg i =
      finishNative B (s.cfg (left hm i)) (s.cfg i) (s.cfg (right hm i))
        (clockAction M hm s i) b := by simp only [activate, setAt_self]
  have hcanself : (activate B M hm (canon M s) i b).cfg i =
      finishNative B ((canon M s).cfg (left hm i)) ((canon M s).cfg i)
        ((canon M s).cfg (right hm i)) (clockAction M hm (canon M s) i) b := by
    simp only [activate, setAt_self]
  by_cases hb : canAdvanceBool hm s.lift i = true
  · have hra : clockAction M hm s i = ClockAction.inc (successor M (s.cfg i).tick) := by
      rw [hr, if_pos hb]
    have hca : clockAction M hm (canon M s) i =
        ClockAction.inc (clockOf M (s.lift i + 1)) := by rw [hc, if_pos hb]
    have ht : clockOf M (successor M (s.cfg i).tick) =
        clockOf M (s.lift i + 1) := by
      rw [clockOf_successor hM (hcos.range i), clockOf_succ hM]
      simp only [clockOf, hcos.residue i]
    have hl := coset_neighborView hM hm s hcos i (left hm i) (Or.inl rfl)
    have hh := coset_neighborView hM hm s hcos i (right hm i) (Or.inr rfl)
    have hcurr : ((canon M s).cfg i).curr = (s.cfg i).curr := by
      simp only [canon, canonRec, hcos.clean i, Bool.false_eq_true, ↓reduceIte]
    constructor
    · intro hcomm _hcan
      have he := congrArg (fun z : WordState m => (z.cfg i).curr) hcomm
      change (canonRec M ((activate B M hm s i b).cfg i)).curr =
        ((activate B M hm (canon M s) i b).cfg i).curr at he
      rw [hrawself, hcanself, hra, hca] at he
      change phaseUpdate B ((s.cfg i).tick % 32)
          (neighborView (s.cfg i).tick (s.cfg (left hm i))) (s.cfg i).curr
          (neighborView (s.cfg i).tick (s.cfg (right hm i))) b =
        phaseUpdate B (((canon M s).cfg i).tick % 32)
          (neighborView ((canon M s).cfg i).tick ((canon M s).cfg (left hm i)))
          ((canon M s).cfg i).curr
          (neighborView ((canon M s).cfg i).tick ((canon M s).cfg (right hm i))) b at he
      rw [hl, hh, hcurr] at he
      exact he
    · intro hupdate
      have hs := hupdate hb
      apply wordState_ext
      · funext j
        by_cases hji : j = i
        · subst j
          change canonRec M ((activate B M hm s i b).cfg i) =
            (activate B M hm (canon M s) i b).cfg i
          rw [hrawself, hcanself, hra, hca]
          change
            ({ tick := clockOf M (successor M (s.cfg i).tick), err := false,
               prior := (s.cfg i).curr,
               curr := phaseUpdate B ((s.cfg i).tick % 32)
                 (neighborView (s.cfg i).tick (s.cfg (left hm i))) (s.cfg i).curr
                 (neighborView (s.cfg i).tick (s.cfg (right hm i))) b } : NativeRecord) =
            { tick := clockOf M (s.lift i + 1), err := false,
              prior := ((canon M s).cfg i).curr,
              curr := phaseUpdate B (((canon M s).cfg i).tick % 32)
                (neighborView ((canon M s).cfg i).tick ((canon M s).cfg (left hm i)))
                ((canon M s).cfg i).curr
                (neighborView ((canon M s).cfg i).tick ((canon M s).cfg (right hm i))) b }
          rw [ht, hl, hh, hcurr, hs]
        · simp [canon, activate, hji]
      · exact coset_activate_lift hM hm s hcos i b
  · have hra : clockAction M hm s i = ClockAction.hold := by rw [hr, if_neg hb]
    have hca : clockAction M hm (canon M s) i = ClockAction.hold := by rw [hc, if_neg hb]
    rw [activate_of_hold hm s i b hra, activate_of_hold hm (canon M s) i b hca]
    simp [hb]

/-- Equal old phases are a sufficient local compatibility condition. -/
theorem canon_activate_of_phase {B M : Nat} (hM : ClockParams M) (hm : 0 < m)
    (s : WordState m) (hcos : LegitCoset M hm s) (i : Fin m) (b : Bool)
    (hphase : (s.cfg i).tick % 32 = ((canon M s).cfg i).tick % 32) :
    canon M (activate B M hm s i b) = activate B M hm (canon M s) i b := by
  apply (canon_activate_iff_update hM hm s hcos i b).2
  intro _hcan
  rw [hphase]

/-- A half-period divisible by 32 preserves every native phase. -/
theorem clockOf_phase {M t : Nat} (hM : ClockParams M) (hdiv : 32 ∣ M / 2)
    (ht : t < M) : clockOf M t % 32 = t % 32 := by
  by_cases hlo : M / 2 ≤ t
  · rw [clockOf_upper hM hlo ht]
  · have hlt : t < M / 2 := by omega
    have hz : (M / 2) % 32 = 0 := Nat.mod_eq_zero_of_dvd hdiv
    simp [clockOf, Nat.mod_eq_of_lt hlt, Nat.add_mod, hz]

/-- Literal asynchronous activation commutes with canonicalization. -/
theorem canon_activate {B M : Nat} (hM : ClockParams M) (hdiv : 32 ∣ M / 2)
    {hm : 0 < m} {s : WordState m} (hcos : LegitCoset M hm s)
    (i : Fin m) (b : Bool) :
    canon M (activate B M hm s i b) = activate B M hm (canon M s) i b := by
  apply canon_activate_of_phase hM hm s hcos i b
  simpa [canon, canonRec, hcos.clean] using
    (clockOf_phase hM hdiv (hcos.range i)).symm

/-- Native recovery stays quiet and in range. Its increment decisions
therefore transport the canonical residue and skew through each activation. -/
theorem coset_activate {B M : Nat} {hm : 0 < m} {s : WordState m}
    (hM : ClockParams M) (hc : LegitCoset M hm s) (i : Fin m) (b : Bool) :
    LegitCoset M hm (activate B M hm s i b) := by
  obtain ⟨clean, quiet, wf⟩ := lg_after_activate (B := B) hM hc i b
  have hl := coset_activate_lift (B := B) hM hm s hc i b
  have canonNext := legit_activate (B := B) hM hm (canon M s) (canon_legit hc) i b
  refine ⟨clean, coset_activate_residue (B := B) hM hm s hc i b, ?_, fun j => (wf j).1, quiet⟩
  rw [hl]
  exact canonNext.2.2

/-- When two canonical states have the same lifts they make the same lift
update, whatever their snapshots contain. -/
private theorem legit_lift_step {B M : Nat} {hm : 0 < m} {s t : WordState m}
    (hM : ClockParams M) (hs : Legit M hm s) (ht : Legit M hm t)
    (he : s.lift = t.lift) (i : Fin m) (b : Bool) :
    (activate B M hm s i b).lift = (activate B M hm t i b).lift := by
  simp only [activate, nativeClock_normal hM hm s hs i, nativeClock_normal hM hm t ht i, he]

/-- Even for an unaligned half-period, arbitrary finite histories have the
same lifts as a legitimate run with the same initial lifts. -/
theorem coset_syncRun_lift {B M : Nat} {hm : 0 < m}
    (hM : ClockParams M) (h : List (Activation m)) (s t : WordState m)
    (hc : LegitCoset M hm s) (ht : Legit M hm t) (he : s.lift = t.lift) :
    (syncRun B M hm h s).lift = (syncRun B M hm h t).lift := by
  induction h generalizing s t with
  | nil => exact he
  | cons e h ih =>
    apply ih _ _ (coset_activate hM hc e.1 e.2) (legit_activate hM hm t ht e.1 e.2)
    exact (coset_activate_lift (B := B) hM hm s hc e.1 e.2).trans
      (legit_lift_step hM (canon_legit hc) ht he e.1 e.2)

/-! Canonical clock representatives preserve finite histories and their consumers. -/

@[simp] theorem canon_lift {m M : Nat} (s : WordState m) :
    (canon M s).lift = s.lift := rfl

@[simp] theorem canon_curr {m M : Nat} (s : WordState m) (i : Fin m) :
    ((canon M s).cfg i).curr = (s.cfg i).curr := by
  change (canonRec M (s.cfg i)).curr = _
  unfold canonRec
  split <;> rfl

@[simp] theorem canon_prior {m M : Nat} (s : WordState m) (i : Fin m) :
    ((canon M s).cfg i).prior = (s.cfg i).prior := by
  change (canonRec M (s.cfg i)).prior = _
  unfold canonRec
  split <;> rfl

/-- Canonicalization leaves the synchronous representation predicate unchanged. -/
@[simp] theorem canon_represents {m B M base : Nat} (hm : 0 < m)
    (choices : Nat → Fin m → Bool) (start : Fin m → Snapshot)
    (s : WordState m) :
    Represents B M base hm choices start (canon M s) ↔
      Represents B M base hm choices start s := by
  simp only [Represents, canon_lift, canon_curr, canon_prior]

/-- Each actual activation has the same snapshot update after canonicalization. -/
def UpdatesAgree {m : Nat} (B M : Nat) (hm : 0 < m) :
    WordState m → List (Activation m) → Prop
  | _, [] => True
  | s, e :: h => UpdateAgrees B M hm s e.1 e.2 ∧
      UpdatesAgree B M hm (activate B M hm s e.1 e.2) h

/-- A phase-aligned half-period gives agreement along every actual history. -/
theorem updatesAgree_of_dvd {m B M : Nat} {hm : 0 < m}
    (hM : ClockParams M) (hp : 32 ∣ M / 2)
    (h : List (Activation m)) (s : WordState m)
    (hc : LegitCoset M hm s) : UpdatesAgree B M hm s h := by
  induction h generalizing s with
  | nil => trivial
  | cons e h ih =>
    exact ⟨(canon_activate_iff_update (B := B) hM hm s hc e.1 e.2).mp
      (canon_activate hM hp hc e.1 e.2),
      ih _ (coset_activate hM hc e.1 e.2)⟩

/-- Canonicalization commutes with histories whose actual updates agree. -/
theorem canon_syncRun_of_updates {m B M : Nat} {hm : 0 < m}
    (hM : ClockParams M) (h : List (Activation m)) (s : WordState m)
    (hc : LegitCoset M hm s) (hup : UpdatesAgree B M hm s h) :
    canon M (syncRun B M hm h s) = syncRun B M hm h (canon M s) := by
  induction h generalizing s with
  | nil => rfl
  | cons e h ih =>
    rcases hup with ⟨hhead, htail⟩
    simp only [syncRun]
    rw [ih _ (coset_activate hM hc e.1 e.2) htail,
      (canon_activate_iff_update (B := B) hM hm s hc e.1 e.2).mpr hhead]

/-- Phase alignment is a sufficient uniform condition for history commutation. -/
theorem canon_syncRun {m B M : Nat} {hm : 0 < m}
    (hM : ClockParams M) (hp : 32 ∣ M / 2)
    (h : List (Activation m)) (s : WordState m)
    (hc : LegitCoset M hm s) :
    canon M (syncRun B M hm h s) = syncRun B M hm h (canon M s) :=
  canon_syncRun_of_updates hM h s hc (updatesAgree_of_dvd hM hp h s hc)

/-- Every prefix remains in the coset invariant. -/
theorem syncRun_coset {m B M : Nat} {hm : 0 < m}
    (hM : ClockParams M) (h : List (Activation m)) (s : WordState m)
    (hc : LegitCoset M hm s) : LegitCoset M hm (syncRun B M hm h s) := by
  induction h generalizing s with
  | nil => exact hc
  | cons e h ih => exact ih _ (coset_activate hM hc e.1 e.2)

/-- The increment classifier is independent of the chosen clock representative. -/
private theorem canon_increment_condition {m B M : Nat} {hm : 0 < m}
    (hM : ClockParams M)
    (s : WordState m) (hc : LegitCoset M hm s) (i : Fin m) (b : Bool)
    (P : Prop) :
    (match clockAction M hm (canon M s) i with
      | .inc _ => P | _ => True) ↔
    (match clockAction M hm s i with
      | .inc _ => P | _ => True) := by
  have he := congrFun (coset_activate_lift (B := B) hM hm s hc i b) i
  simp only [activate, setAt_self, canon_lift] at he
  cases ha : clockAction M hm s i <;>
    cases hb : clockAction M hm (canon M s) i <;>
    simp_all [advanceLift] <;> omega

/-- The same bit history honors the same choices when its updates agree. -/
theorem canon_honors {m B M : Nat} {hm : 0 < m}
    (hM : ClockParams M)
    (choices : Nat → Fin m → Bool) (h : List (Activation m))
    (s : WordState m) (hc : LegitCoset M hm s)
    (hup : UpdatesAgree B M hm s h) :
    Honors B M hm choices (canon M s) h ↔ Honors B M hm choices s h := by
  induction h generalizing s with
  | nil => rfl
  | cons e h ih =>
    rcases hup with ⟨hhead, htail⟩
    simp only [Honors, canon_lift]
    rw [← (canon_activate_iff_update (B := B) hM hm s hc e.1 e.2).mpr hhead,
      ih _ (coset_activate hM hc e.1 e.2) htail]
    exact and_congr (canon_increment_condition (B := B) hM s hc e.1 e.2 _) Iff.rfl

/-- The observed current snapshot at every lifted level is unchanged. -/
theorem canon_levelCurr {m B M : Nat} {hm : 0 < m}
    (hM : ClockParams M)
    (h : List (Activation m)) (s : WordState m)
    (hc : LegitCoset M hm s) (hup : UpdatesAgree B M hm s h)
    (i : Fin m) (ell : Nat) :
    levelCurr B M hm h (canon M s) i ell = levelCurr B M hm h s i ell := by
  induction h generalizing s with
  | nil => simp only [levelCurr, canon_lift, canon_curr]
  | cons e h ih =>
    rcases hup with ⟨hhead, htail⟩
    simp only [levelCurr, canon_lift, canon_curr]
    rw [← (canon_activate_iff_update (B := B) hM hm s hc e.1 e.2).mpr hhead,
      ih _ (coset_activate hM hc e.1 e.2) htail]

/-- The representation theorem applies when the actual history updates agree. -/
theorem syncRun_represents_coset {m B M base : Nat} {hm : 0 < m}
    (hM : ClockParams M)
    (choices : Nat → Fin m → Bool) (start : Fin m → Snapshot)
    (h : List (Activation m)) (s : WordState m)
    (hc : LegitCoset M hm s) (hup : UpdatesAgree B M hm s h)
    (hrep : Represents B M base hm choices start s)
    (hhonor : Honors B M hm choices s h) :
    Represents B M base hm choices start (syncRun B M hm h s) := by
  apply (canon_represents hm choices start _).mp
  rw [canon_syncRun_of_updates hM h s hc hup]
  exact syncRun_represents hM hm choices start h (canon M s) (canon_legit hc)
    ((canon_represents hm choices start s).mpr hrep)
    ((canon_honors hM choices h s hc hup).mpr hhonor)

/-- Actual observed snapshots agree with the synchronous table. -/
theorem levelCurr_eq_sync_coset {m B M base : Nat} {hm : 0 < m}
    (hM : ClockParams M)
    (choices : Nat → Fin m → Bool) (start : Fin m → Snapshot)
    (h : List (Activation m)) (s : WordState m)
    (hc : LegitCoset M hm s) (hup : UpdatesAgree B M hm s h)
    (hrep : Represents B M base hm choices start s)
    (hhonor : Honors B M hm choices s h)
    (i : Fin m) (n : Nat) (value : Snapshot)
    (hvalue : levelCurr B M hm h s i (base + n) = some value) :
    value = syncLevels B M base hm choices start n i := by
  apply levelCurr_eq_sync hM hm choices start h (canon M s) (canon_legit hc)
    ((canon_represents hm choices start s).mpr hrep)
    ((canon_honors hM choices h s hc hup).mpr hhonor) i n value
  rw [canon_levelCurr hM h s hc hup]
  exact hvalue

/-- Actual publications along a scheduler word, omitting stuttering letters. -/
def overrunHistory {n m B M : Nat} (hm : 0 < m) (act : OverrunAct n m) :
    OverrunState m → Thru.Word n → List (Activation m)
  | _, [] => []
  | x, e :: u =>
    match act x e with
    | none => overrunHistory (B := B) (M := M) hm act (x.1, none) u
    | some p => p :: overrunHistory (B := B) (M := M) hm act
        (activate B M hm x.1 p.1 p.2, some p.1) u

/-- Scheduler execution is exactly execution of its actual publications. -/
theorem overrunHistory_run {n m B M : Nat} (hm : 0 < m)
    (act : OverrunAct n m) (x : OverrunState m) (u : Thru.Word n) :
    (Thru.runWord (overrunNext (B := B) (M := M) hm act) x u).1 =
      syncRun B M hm (overrunHistory (B := B) (M := M) hm act x u) x.1 := by
  induction u generalizing x with
  | nil => rfl
  | cons e u ih =>
    cases he : act x e with
    | none => simpa only [Thru.runWord, overrunNext, overrunHistory, he] using ih (x.1, none)
    | some p =>
      simpa only [Thru.runWord, overrunNext, overrunHistory, he, syncRun] using
        ih (activate B M hm x.1 p.1 p.2, some p.1)

/-- Every scheduler prefix projects to the canonical execution of its actual
publications. No invariance of the scheduler's publication selector is needed. -/
theorem canon_overrun_prefix {n m B M : Nat} {hm : 0 < m}
    (hM : ClockParams M) (hp : 32 ∣ M / 2)
    (act : OverrunAct n m) (x : OverrunState m)
    (hc : LegitCoset M hm x.1) (u : Thru.Word n) (t : Nat) :
    canon M (overrunStateAt (B := B) (M := M) hm act x u t).1 =
      syncRun B M hm
        (overrunHistory (B := B) (M := M) hm act x (u.take t)) (canon M x.1) := by
  unfold overrunStateAt
  rw [overrunHistory_run, canon_syncRun hM hp _ _ hc]

/-- The original prefix has the same lifted coordinates as that canonical run. -/
theorem overrun_prefix_lift_projection {n m B M : Nat} {hm : 0 < m}
    (hM : ClockParams M)
    (act : OverrunAct n m) (x : OverrunState m)
    (hc : LegitCoset M hm x.1) (u : Thru.Word n) (t : Nat) :
    (overrunStateAt (B := B) (M := M) hm act x u t).1.lift =
      (syncRun B M hm
        (overrunHistory (B := B) (M := M) hm act x (u.take t)) (canon M x.1)).lift := by
  unfold overrunStateAt
  rw [overrunHistory_run]
  exact coset_syncRun_lift hM _ x.1 (canon M x.1) hc (canon_legit hc) rfl

/-- One lift serves every activation history. Lift trajectories always
project; the full native records project when the half-period preserves phase. -/
theorem lgSet_canon_legit {α : Type} {n B M : Nat} {hm : 0 < m}
    (C : Chain.ClockChain α n m B M hm) (x : α)
    (hx : Chain.LgSet C x) (hmP : m < M / 2) (hM : ClockParams M) (base : Nat) :
    ∃ lift : Fin m → Nat,
      let s : WordState m := ⟨C.cfg x, lift⟩
      (∀ i, base ≤ lift i) ∧ LegitCoset M hm s ∧ Legit M hm (canon M s) ∧
      (∀ h, (syncRun B M hm h s).lift = (syncRun B M hm h (canon M s)).lift) ∧
      (32 ∣ M / 2 → ∀ h, canon M (syncRun B M hm h s) = syncRun B M hm h (canon M s)) := by
  obtain ⟨lift, floor, hc⟩ := lgSet_coset C x hx hmP hM base
  exact ⟨lift, floor, hc, canon_legit hc,
    fun h => coset_syncRun_lift hM h _ _ hc (canon_legit hc) rfl,
    fun hp h => canon_syncRun hM hp h _ hc⟩

end L4.Height

