import Leader.L4.Height.Quiet
import Leader.L4.Height.ClearBridge

namespace L4.Height.Recover

open L4.Compiler.Native
open L4.Height

set_option maxRecDepth 8192
set_option maxHeartbeats 12000000

/-! ## Literal bridges from StageOne to StageThree -/

/-- StageOne's `localUpdate`/`setAt` publication is definitionally the same
literal native publication as StageThree's activation. -/
theorem activate_one_eq {m : Nat} (B M : Nat) (hm : 0 < m)
    (c : Fin m → NativeRecord) (i : Fin m) (delta : Bool) :
    StageOne.activate B M hm c i delta =
      StageThree.activate B M hm c i delta := by
  funext j
  rfl

private theorem isRoot_one_eq_rootB (M : Nat)
    (leftRec centerRec rightRec : NativeRecord) :
    StageOne.IsRoot M leftRec centerRec rightRec =
      StageThree.rootB M leftRec centerRec rightRec := by
  rfl

private theorem signed_tick_zero_iff (M : Nat) (r : NativeRecord) :
    StageThree.signedVal M r = -(Int.ofNat (M / 2)) ↔
      r.tick = 0 := by
  constructor
  · intro h
    unfold StageThree.signedVal at h
    simp only [Int.ofNat_eq_natCast] at h
    omega
  · intro h
    simp [StageThree.signedVal, h]

/-- Pointwise StageOne quietness is exactly StageThree's global quietness. -/
theorem quiet_one_iff {m : Nat} (M : Nat) (hm : 0 < m)
    (c : Fin m → NativeRecord) :
    (∀ i, StageOne.Quiet M hm c i) ↔
      StageThree.Quiet M hm c := by
  constructor
  · intro hone
    unfold StageThree.Quiet
    intro i hroot
    have hsite := hone i
    unfold StageOne.Quiet StageOne.QuietWindow at hsite
    have hrootOne :
        StageOne.IsRoot M (c (left hm i)) (c i) (c (right hm i)) = true := by
      rw [isRoot_one_eq_rootB]
      exact hroot
    have hbase := hsite hrootOne
    unfold StageOne.BaseError at hbase
    exact ⟨hbase.1, (signed_tick_zero_iff M (c i)).2 hbase.2⟩
  · intro hthree
    unfold StageThree.Quiet at hthree
    intro i
    unfold StageOne.Quiet StageOne.QuietWindow
    intro hroot
    unfold StageOne.BaseError
    have hrootThree :
        StageThree.rootB M (c (left hm i)) (c i) (c (right hm i)) = true := by
      rw [← isRoot_one_eq_rootB]
      exact hroot
    have hq := hthree i hrootThree
    exact ⟨hq.1, (signed_tick_zero_iff M (c i)).1 hq.2⟩

/-- The two accepted clock-parameter formulations are equivalent. -/
theorem clock_params_iff (M : Nat) :
    StageOne.ClockParams M ↔ StageTwo.ClockParams M := by
  unfold StageOne.ClockParams StageTwo.ClockParams
  constructor
  · rintro ⟨hfour, heven⟩
    constructor
    · omega
    · exact heven
  · rintro ⟨hhalf, heven⟩
    constructor
    · omega
    · exact heven

/-- StageOne's unconditional one-publication preservation theorem supplies the
`QuietPreserved` interface assumed by ClearBridge. The Frozen and WellFormed
arguments of that interface are not needed by the StageOne theorem. -/
theorem quiet_preserved_holds {m B M D : Nat}
    (hM : StageTwo.ClockParams M) (hm : 0 < m) :
    QuietPreserved B M D hm := by
  intro c owner delta hquiet _hfrozen _hwell
  have hMone : StageOne.ClockParams M :=
    (clock_params_iff M).2 hM
  have hone : ∀ i, StageOne.Quiet M hm c i :=
    (quiet_one_iff M hm c).2 hquiet
  have hnextOne :
      ∀ i, StageOne.Quiet M hm
        (StageOne.activate B M hm c owner delta) i := by
    intro i
    exact StageOne.quiet_preserved (B := B) hMone hm
      c i owner delta (hone i)
  have hnextThree :
      StageThree.Quiet M hm
        (StageOne.activate B M hm c owner delta) :=
    (quiet_one_iff M hm
      (StageOne.activate B M hm c owner delta)).1 hnextOne
  rw [activate_one_eq B M hm c owner delta] at hnextThree
  exact hnextThree

/-- ClearBridge's final stage-three theorem with its last external hypothesis
discharged by StageOne.quiet_preserved. -/
theorem all_clear_time_unconditional {m B M D : Nat}
    (hM : StageTwo.ClockParams M) (hm : 0 < m)
    (s : Fin m → NativeRecord)
    (hquiet : StageThree.Quiet M hm s)
    (hfrozen : StageThree.Frozen M D hm s)
    (hwell : StageTwo.WellFormed M s)
    (w : Nat → StageThree.Activation m) (hinf : FairStream w)
    (u : Fin m) (herr : (s u).err = true) :
    ∃ path,
      StageThree.DepPathFrom M hm s u path ∧
        path.length ≤ D + 1 ∧
        (streamState B M hm s w
          (StageThree.clearSeqTime (serviceTime w hinf) 0 path) u).err =
            false := by
  exact all_clear_time hM hm
    (quiet_preserved_holds (B := B) (D := D) hM hm)
    s hquiet hfrozen hwell w hinf u herr

/-! ## StageOne words and ClearBridge prefix states -/

private theorem runWord_eq_runActivations {m B M : Nat} (hm : 0 < m) :
    ∀ (h : List (Fin m × Bool)) (c : Fin m → NativeRecord),
      StageOne.runWord B M hm h c =
        StageThree.runActivations B M hm c h := by
  intro h
  induction h with
  | nil =>
      intro c
      rfl
  | cons e h ih =>
      intro c
      change
        StageOne.runWord B M hm h
            (StageOne.activate B M hm c e.1 e.2) =
          StageThree.runActivations B M hm
            (StageThree.activate B M hm c e.1 e.2) h
      rw [activate_one_eq B M hm c e.1 e.2]
      exact ih (StageThree.activate B M hm c e.1 e.2)

private theorem streamState_eq_runWord {m B M : Nat} (hm : 0 < m)
    (s : Fin m → NativeRecord)
    (w : Nat → StageThree.Activation m) (t : Nat) :
    streamState B M hm s w t =
      StageOne.runWord B M hm ((List.range t).map w) s := by
  unfold streamState
  exact (runWord_eq_runActivations (B := B) (M := M) hm
    ((List.range t).map w) s).symm

/-! ## A least finite covering prefix from fairness -/

private theorem activated_prefix_mono {m : Nat}
    (w : Nat → StageThree.Activation m) (i : Fin m)
    {t t' : Nat} (htt : t ≤ t')
    (hact : StageOne.Activated ((List.range t).map w) i) :
    StageOne.Activated ((List.range t').map w) i := by
  unfold StageOne.Activated at hact ⊢
  obtain ⟨delta, hmem⟩ := hact
  obtain ⟨q, hq, heq⟩ := List.mem_map.mp hmem
  refine ⟨delta, List.mem_map.mpr ⟨q, ?_, heq⟩⟩
  apply List.mem_range.mpr
  have hqt : q < t := List.mem_range.mp hq
  omega

private theorem covered_prefix_mono {m : Nat}
    (w : Nat → StageThree.Activation m)
    {t t' : Nat} (htt : t ≤ t')
    (hcover : StageOne.Covered ((List.range t).map w)) :
    StageOne.Covered ((List.range t').map w) := by
  unfold StageOne.Covered at hcover ⊢
  intro i
  exact activated_prefix_mono w i htt (hcover i)

private theorem activated_list_exists {m : Nat}
    (w : Nat → StageThree.Activation m) (hinf : FairStream w) :
    ∀ xs : List (Fin m),
      ∃ t, ∀ i, i ∈ xs →
        StageOne.Activated ((List.range t).map w) i := by
  intro xs
  induction xs with
  | nil =>
      refine ⟨0, ?_⟩
      intro i hi
      cases hi
  | cons a xs ih =>
      obtain ⟨t, ht⟩ := ih
      obtain ⟨q, htq, hqa⟩ := hinf a t
      refine ⟨Nat.succ q, ?_⟩
      intro i hi
      simp only [List.mem_cons] at hi
      rcases hi with hia | hi
      · subst i
        unfold StageOne.Activated
        refine ⟨(w q).2, ?_⟩
        apply List.mem_map.mpr
        refine ⟨q, List.mem_range.mpr (Nat.lt_succ_self q), ?_⟩
        apply Prod.ext
        · exact hqa
        · rfl
      · exact activated_prefix_mono w i (by omega) (ht i hi)

private theorem covered_prefix_exists {m : Nat}
    (w : Nat → StageThree.Activation m) (hinf : FairStream w) :
    ∃ t, StageOne.Covered ((List.range t).map w) := by
  obtain ⟨t, ht⟩ :=
    activated_list_exists w hinf (List.finRange m)
  refine ⟨t, ?_⟩
  unfold StageOne.Covered
  intro i
  exact ht i (List.mem_finRange i)

private theorem least_covered_below {m : Nat}
    (w : Nat → StageThree.Activation m) :
    ∀ T,
      StageOne.Covered ((List.range T).map w) →
      ∃ tzero,
        StageOne.Covered ((List.range tzero).map w) ∧
          ∀ r, r < tzero →
            ¬ StageOne.Covered ((List.range r).map w) := by
  intro T
  induction T with
  | zero =>
      intro hzero
      refine ⟨0, hzero, ?_⟩
      intro r hr
      omega
  | succ T ih =>
      intro hsucc
      by_cases hT : StageOne.Covered ((List.range T).map w)
      · exact ih hT
      · refine ⟨Nat.succ T, hsucc, ?_⟩
        intro r hr hcover
        have hrT : r ≤ T := by omega
        exact hT (covered_prefix_mono w hrT hcover)

private theorem first_covered_prefix_exists {m : Nat}
    (w : Nat → StageThree.Activation m) (hinf : FairStream w) :
    ∃ tzero,
      StageOne.Covered ((List.range tzero).map w) ∧
        ∀ r, r < tzero →
          ¬ StageOne.Covered ((List.range r).map w) := by
  obtain ⟨T, hT⟩ := covered_prefix_exists w hinf
  exact least_covered_below w T hT

/-! ## Quietness from the first covering prefix onward -/

private theorem stream_quiet_step {m B M : Nat}
    (hM : StageOne.ClockParams M) (hm : 0 < m)
    (s : Fin m → NativeRecord)
    (w : Nat → StageThree.Activation m) (t : Nat)
    (hquiet : StageThree.Quiet M hm (streamState B M hm s w t)) :
    StageThree.Quiet M hm (streamState B M hm s w (Nat.succ t)) := by
  have hone :
      ∀ i, StageOne.Quiet M hm (streamState B M hm s w t) i :=
    (quiet_one_iff M hm (streamState B M hm s w t)).2 hquiet
  have hnextOne :
      ∀ i, StageOne.Quiet M hm
        (StageOne.activate B M hm (streamState B M hm s w t)
          (w t).1 (w t).2) i := by
    intro i
    exact StageOne.quiet_preserved (B := B) hM hm
      (streamState B M hm s w t) i (w t).1 (w t).2 (hone i)
  have hnextThree :
      StageThree.Quiet M hm
        (StageOne.activate B M hm (streamState B M hm s w t)
          (w t).1 (w t).2) :=
    (quiet_one_iff M hm
      (StageOne.activate B M hm (streamState B M hm s w t)
        (w t).1 (w t).2)).1 hnextOne
  rw [activate_one_eq B M hm (streamState B M hm s w t)
    (w t).1 (w t).2] at hnextThree
  rw [streamState_succ B M hm s w t]
  exact hnextThree

private theorem stream_quiet_mono {m B M : Nat}
    (hM : StageOne.ClockParams M) (hm : 0 < m)
    (s : Fin m → NativeRecord)
    (w : Nat → StageThree.Activation m) :
    ∀ {t t' : Nat}, t ≤ t' →
      StageThree.Quiet M hm (streamState B M hm s w t) →
      StageThree.Quiet M hm (streamState B M hm s w t') := by
  intro t t' htt hquiet
  induction t' generalizing t with
  | zero =>
      have ht : t = 0 := by omega
      subst t
      exact hquiet
  | succ n ih =>
      by_cases ht : t = Nat.succ n
      · subst t
        exact hquiet
      · have hle : t ≤ n := by omega
        have hprev := ih hle hquiet
        exact stream_quiet_step hM hm s w n hprev

/-- For a fair stream, the least prefix covering every site exists. Every
state at or after that first covering prefix is StageThree-quiet. The accepted
TickBound hypothesis is carried through the covering prefix by StageOne's
range-preservation theorem. -/
theorem quiet_stream {m B M : Nat}
    (hM : StageTwo.ClockParams M) (hm : 0 < m)
    (s : Fin m → NativeRecord) (hbound : StageOne.TickBound M s)
    (w : Nat → StageThree.Activation m) (hinf : FairStream w) :
    ∃ tzero,
      StageOne.Covered ((List.range tzero).map w) ∧
        (∀ r, r < tzero →
          ¬ StageOne.Covered ((List.range r).map w)) ∧
        ∀ t, tzero ≤ t →
          StageThree.Quiet M hm (streamState B M hm s w t) := by
  have hMone : StageOne.ClockParams M :=
    (clock_params_iff M).2 hM
  obtain ⟨tzero, hcover, hminimal⟩ :=
    first_covered_prefix_exists w hinf
  have _hboundAt :
      StageOne.TickBound M
        (StageOne.runWord B M hm ((List.range tzero).map w) s) :=
    StageOne.runWord_tickBound (B := B) hMone hm
      ((List.range tzero).map w) s hbound
  have honeAt :
      ∀ i, StageOne.Quiet M hm
        (StageOne.runWord B M hm ((List.range tzero).map w) s) i := by
    have hforever := StageOne.quiet_forever (B := B) hMone hm
      ((List.range tzero).map w) [] s hcover
    simpa only [StageOne.runWord] using hforever
  have hquietRun :
      StageThree.Quiet M hm
        (StageOne.runWord B M hm ((List.range tzero).map w) s) :=
    (quiet_one_iff M hm
      (StageOne.runWord B M hm ((List.range tzero).map w) s)).1 honeAt
  have hquietAt :
      StageThree.Quiet M hm (streamState B M hm s w tzero) := by
    rw [streamState_eq_runWord]
    exact hquietRun
  refine ⟨tzero, hcover, hminimal, ?_⟩
  intro t htt
  exact stream_quiet_mono hMone hm s w htt hquietAt

#print axioms activate_one_eq
#print axioms quiet_one_iff
#print axioms clock_params_iff
#print axioms quiet_preserved_holds
#print axioms all_clear_time_unconditional
#print axioms quiet_stream

end L4.Height.Recover
