import Leader.L4.Height.Frozen
import Leader.L4.Height.Clear

namespace L4.Height.Recover

open L4.Compiler.Native
open L4.Height

set_option maxRecDepth 8192
set_option maxHeartbeats 12000000

/-- The external quietness-preservation fact supplied by the parallel QUIET
round, stated on the StageThree names used by the clearing argument. -/
abbrev QuietPreserved {m : Nat} (B M D : Nat) (hm : 0 < m) : Prop :=
  ∀ (c : Fin m → NativeRecord) (i : Fin m) (delta : Bool),
    StageThree.Quiet M hm c →
    StageThree.Frozen M D hm c →
    StageTwo.WellFormed M c →
    StageThree.Quiet M hm (StageThree.activate B M hm c i delta)

/-! ## Literal bridges between StageTwo and StageThree -/

/-- Both stage files perform the same literal native publication. -/
theorem activate_eq {m : Nat} (B M : Nat) (hm : 0 < m)
    (c : Fin m → NativeRecord) (i : Fin m) (delta : Bool) :
    StageTwo.activate B M hm c i delta =
      StageThree.activate B M hm c i delta := by
  funext j
  by_cases hji : j = i
  · subst j
    rw [StageTwo.activate_self_eq_finish, StageThree.activate_owner]
    rfl
  · rw [StageTwo.activate_other B M hm c i j delta hji,
      StageThree.activate_other B M hm c i j delta hji]

private theorem isRoot_eq_rootB (M : Nat)
    (leftRec centerRec rightRec : NativeRecord) :
    StageTwo.IsRoot M leftRec centerRec rightRec =
      StageThree.rootB M leftRec centerRec rightRec := by
  rfl

private theorem signed_base_iff (M : Nat) (r : NativeRecord) :
    StageThree.signedVal M r = -(Int.ofNat (M / 2)) ↔
      r.tick = 0 := by
  constructor
  · intro h
    unfold StageThree.signedVal at h
    simp only [Int.ofNat_eq_natCast] at h
    omega
  · intro h
    simp [StageThree.signedVal, h]

/-- StageTwo's root/base formulation and StageThree's root/signed formulation
are definitionally the same root test and arithmetically the same base. -/
theorem quiet_iff {m : Nat} (M : Nat) (hm : 0 < m)
    (c : Fin m → NativeRecord) :
    StageTwo.Quiet M hm c ↔ StageThree.Quiet M hm c := by
  constructor
  · intro htwo
    unfold StageTwo.Quiet at htwo
    unfold StageThree.Quiet
    intro i hroot
    have hwindow := htwo i
    unfold StageTwo.QuietAt StageTwo.QuietWindow at hwindow
    have hrootTwo :
        StageTwo.IsRoot M (c (left hm i)) (c i) (c (right hm i)) = true := by
      rw [isRoot_eq_rootB]
      exact hroot
    have hbase := hwindow hrootTwo
    exact ⟨hbase.1, (signed_base_iff M (c i)).2 hbase.2⟩
  · intro hthree
    unfold StageThree.Quiet at hthree
    unfold StageTwo.Quiet
    intro i
    unfold StageTwo.QuietAt StageTwo.QuietWindow
    intro hroot
    have hrootThree :
        StageThree.rootB M (c (left hm i)) (c i) (c (right hm i)) = true := by
      rw [← isRoot_eq_rootB]
      exact hroot
    have hq := hthree i hrootThree
    exact ⟨hq.1, (signed_base_iff M (c i)).1 hq.2⟩

/-- StageThree's signed Frozen condition is exactly StageTwo's raw-neighbour
Frozen condition together with the raw strict cap Below. -/
theorem frozen_iff {m : Nat} (M D : Nat) (hm : 0 < m)
    (c : Fin m → NativeRecord) :
    StageThree.Frozen M D hm c ↔
      StageTwo.Frozen hm c ∧ StageTwo.Below D c := by
  constructor
  · intro hthree
    unfold StageThree.Frozen at hthree
    constructor
    · unfold StageTwo.Frozen
      intro u hu v huv
      rcases huv with hleft | hright
      · subst v
        have hbound := (hthree u hu).1
        simp only [StageThree.signedVal, Int.ofNat_eq_natCast] at hbound
        omega
      · subst v
        have hbound := (hthree u hu).2.1
        simp only [StageThree.signedVal, Int.ofNat_eq_natCast] at hbound
        omega
    · unfold StageTwo.Below
      intro u hu
      have hbound := (hthree u hu).2.2
      simp only [StageThree.signedVal, Int.ofNat_eq_natCast] at hbound
      omega
  · rintro ⟨htwo, hbelow⟩
    unfold StageThree.Frozen
    intro u hu
    have hleft := StageTwo.frozen_signed M hm c htwo
      u (left hm u) hu (Or.inl rfl)
    have hright := StageTwo.frozen_signed M hm c htwo
      u (right hm u) hu (Or.inr rfl)
    have hcap := StageTwo.below_signed M D c hbelow u hu
    constructor
    · simpa only [StageTwo.signedVal, StageThree.signedVal] using hleft
    · constructor
      · simpa only [StageTwo.signedVal, StageThree.signedVal] using hright
      · simpa only [StageTwo.signedVal, StageThree.signedVal] using hcap

/-- ClockParams plus StageTwo's decoded range gives the domain needed by
StageThree.clears_on_poll. -/
theorem clockDomain_of_wellFormed {m M : Nat}
    (hM : StageTwo.ClockParams M)
    (c : Fin m → NativeRecord) (hwell : StageTwo.WellFormed M c) :
    StageThree.ClockDomain M c := by
  unfold StageTwo.ClockParams at hM
  unfold StageThree.ClockDomain
  constructor
  · omega
  · constructor
    · have hdvd : 2 ∣ M := by
        refine ⟨M / 2, ?_⟩
        omega
      exact Nat.mod_eq_zero_of_dvd hdvd
    · intro i
      simpa only [StageTwo.WellFormedRecord] using hwell i

/-! ## Preservation and StableTrace -/

/-- Quiet, Frozen, and WellFormed persist along every StageThree activation
word; the same induction simultaneously constructs StageThree.StableTrace. -/
theorem stable_trace_of {m B M D : Nat}
    (hM : StageTwo.ClockParams M) (hm : 0 < m)
    (hquietPres : QuietPreserved B M D hm)
    (s : Fin m → NativeRecord) (acts : List (StageThree.Activation m))
    (hquiet : StageThree.Quiet M hm s)
    (hfrozen : StageThree.Frozen M D hm s)
    (hwell : StageTwo.WellFormed M s) :
    StageThree.StableTrace B M D hm s acts ∧
      StageThree.Quiet M hm (StageThree.runActivations B M hm s acts) ∧
      StageThree.Frozen M D hm (StageThree.runActivations B M hm s acts) ∧
      StageTwo.WellFormed M (StageThree.runActivations B M hm s acts) := by
  induction acts generalizing s with
  | nil =>
      refine ⟨?_, ?_⟩
      · change True
        trivial
      · change StageThree.Quiet M hm s ∧
          StageThree.Frozen M D hm s ∧ StageTwo.WellFormed M s
        exact ⟨hquiet, ⟨hfrozen, hwell⟩⟩
  | cons a rest ih =>
      have hquietTwo : StageTwo.Quiet M hm s :=
        (quiet_iff M hm s).2 hquiet
      have hraw := (frozen_iff M D hm s).1 hfrozen
      have hpres := StageTwo.frozen_preserved B M D hM hm s
        hquietTwo hraw.1 hraw.2 hwell a.1 a.2
      have hnextTwo :
          StageTwo.Frozen hm (StageThree.activate B M hm s a.1 a.2) := by
        rw [← activate_eq B M hm s a.1 a.2]
        exact hpres.1
      have hnextBelow :
          StageTwo.Below D (StageThree.activate B M hm s a.1 a.2) := by
        rw [← activate_eq B M hm s a.1 a.2]
        exact hpres.2.1
      have hnextWell :
          StageTwo.WellFormed M
            (StageThree.activate B M hm s a.1 a.2) := by
        rw [← activate_eq B M hm s a.1 a.2]
        exact hpres.2.2
      have hnextFrozen :
          StageThree.Frozen M D hm
            (StageThree.activate B M hm s a.1 a.2) :=
        (frozen_iff M D hm
          (StageThree.activate B M hm s a.1 a.2)).2
          ⟨hnextTwo, hnextBelow⟩
      have hnextQuiet :
          StageThree.Quiet M hm
            (StageThree.activate B M hm s a.1 a.2) :=
        hquietPres s a.1 a.2 hquiet hfrozen hwell
      have htail := ih (StageThree.activate B M hm s a.1 a.2)
        hnextQuiet hnextFrozen hnextWell
      refine ⟨?_, ?_⟩
      · change StageThree.Quiet M hm s ∧
          StageThree.Frozen M D hm s ∧
          StageThree.StableTrace B M D hm
            (StageThree.activate B M hm s a.1 a.2) rest
        exact ⟨hquiet, ⟨hfrozen, htail.1⟩⟩
      · change
          StageThree.Quiet M hm
              (StageThree.runActivations B M hm
                (StageThree.activate B M hm s a.1 a.2) rest) ∧
            StageThree.Frozen M D hm
              (StageThree.runActivations B M hm
                (StageThree.activate B M hm s a.1 a.2) rest) ∧
            StageTwo.WellFormed M
              (StageThree.runActivations B M hm
                (StageThree.activate B M hm s a.1 a.2) rest)
        exact htail.2

/-! ## Prefix states of an infinite activation stream -/

private theorem runActivations_append {m B M : Nat} (hm : 0 < m)
    (s : Fin m → NativeRecord)
    (xs ys : List (StageThree.Activation m)) :
    StageThree.runActivations B M hm s (xs ++ ys) =
      StageThree.runActivations B M hm
        (StageThree.runActivations B M hm s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons a xs ih =>
      change
        StageThree.runActivations B M hm
            (StageThree.activate B M hm s a.1 a.2) (xs ++ ys) =
          StageThree.runActivations B M hm
            (StageThree.runActivations B M hm
              (StageThree.activate B M hm s a.1 a.2) xs) ys
      exact ih (StageThree.activate B M hm s a.1 a.2)

/-- State after activations `w 0, ..., w (t-1)`. -/
def streamState {m : Nat} (B M : Nat) (hm : 0 < m)
    (s : Fin m → NativeRecord) (w : Nat → StageThree.Activation m)
    (t : Nat) : Fin m → NativeRecord :=
  StageThree.runActivations B M hm s ((List.range t).map w)

theorem streamState_succ {m : Nat} (B M : Nat) (hm : 0 < m)
    (s : Fin m → NativeRecord) (w : Nat → StageThree.Activation m)
    (t : Nat) :
    streamState B M hm s w (Nat.succ t) =
      StageThree.activate B M hm (streamState B M hm s w t)
        (w t).1 (w t).2 := by
  unfold streamState
  rw [List.range_succ, List.map_append, runActivations_append]
  rfl

private theorem stream_facts {m B M D : Nat}
    (hM : StageTwo.ClockParams M) (hm : 0 < m)
    (hquietPres : QuietPreserved B M D hm)
    (s : Fin m → NativeRecord)
    (hquiet : StageThree.Quiet M hm s)
    (hfrozen : StageThree.Frozen M D hm s)
    (hwell : StageTwo.WellFormed M s)
    (w : Nat → StageThree.Activation m) (t : Nat) :
    StageThree.StableTrace B M D hm s ((List.range t).map w) ∧
      StageThree.Quiet M hm (streamState B M hm s w t) ∧
      StageThree.Frozen M D hm (streamState B M hm s w t) ∧
      StageTwo.WellFormed M (streamState B M hm s w t) := by
  simpa only [streamState] using
    (stable_trace_of hM hm hquietPres s ((List.range t).map w)
      hquiet hfrozen hwell)

/-- Once a site is correct in the stream, one-step error monotonicity prevents
it from ever becoming erroneous again. -/
private theorem stream_correct_mono {m B M D : Nat}
    (hM : StageTwo.ClockParams M) (hm : 0 < m)
    (hquietPres : QuietPreserved B M D hm)
    (s : Fin m → NativeRecord)
    (hquiet : StageThree.Quiet M hm s)
    (hfrozen : StageThree.Frozen M D hm s)
    (hwell : StageTwo.WellFormed M s)
    (w : Nat → StageThree.Activation m) (u : Fin m) :
    ∀ {t t' : Nat}, t ≤ t' →
      (streamState B M hm s w t u).err = false →
      (streamState B M hm s w t' u).err = false := by
  intro t t' htt hclear
  induction t' generalizing t with
  | zero =>
      have ht : t = 0 := by omega
      subst t
      exact hclear
  | succ n ih =>
      by_cases ht : t = Nat.succ n
      · subst t
        exact hclear
      · have hle : t ≤ n := by omega
        have hprev := ih hle hclear
        cases hnew : (streamState B M hm s w (Nat.succ n) u).err with
        | false => rfl
        | true =>
            have hstep := hnew
            rw [streamState_succ B M hm s w n] at hstep
            have hfacts := stream_facts hM hm hquietPres s
              hquiet hfrozen hwell w n
            have hback := StageThree.error_monotone
              (B := B) (M := M) (D := D) hm
              (streamState B M hm s w n) (w n).1 (w n).2
              hfacts.2.1 hfacts.2.2.1 u hstep
            rw [hprev] at hback
            cases hback.1

/-! ## Least future service times -/

/-- Every site occurs again strictly after every stream time. -/
abbrev FairStream {m : Nat} (w : Nat → StageThree.Activation m) : Prop :=
  ∀ i t, ∃ q, t < q ∧ (w q).1 = i

/-- Core-only bounded search for the least true Boolean at or below a bound.
If the prefix has no true entry, the return value is the bound itself. -/
private def leastTrueUpTo (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 =>
      let k := leastTrueUpTo p n
      if p k = true then k else n + 1

private theorem leastTrueUpTo_le (p : Nat → Bool) :
    ∀ n, leastTrueUpTo p n ≤ n := by
  intro n
  induction n with
  | zero =>
      simp [leastTrueUpTo]
  | succ n ih =>
      simp only [leastTrueUpTo]
      split
      · omega
      · omega

private theorem leastTrueUpTo_true_of_true_at (p : Nat → Bool) :
    ∀ n, p n = true → p (leastTrueUpTo p n) = true := by
  intro n hn
  cases n with
  | zero =>
      simpa only [leastTrueUpTo] using hn
  | succ n =>
      simp only [leastTrueUpTo]
      split
      next hprev => exact hprev
      next _ => exact hn

private theorem leastTrueUpTo_true_of_exists (p : Nat → Bool) :
    ∀ n, (∃ j, j ≤ n ∧ p j = true) →
      p (leastTrueUpTo p n) = true := by
  intro n
  induction n with
  | zero =>
      intro hex
      obtain ⟨j, hj, hpj⟩ := hex
      have hjzero : j = 0 := by omega
      subst j
      simpa only [leastTrueUpTo] using hpj
  | succ n ih =>
      intro hex
      simp only [leastTrueUpTo]
      split
      next hprev => exact hprev
      next hprev =>
        obtain ⟨j, hj, hpj⟩ := hex
        by_cases hjn : j ≤ n
        · have hfound := ih ⟨j, hjn, hpj⟩
          exact False.elim (hprev hfound)
        · have heq : j = n + 1 := by omega
          rw [← heq]
          exact hpj

private theorem leastTrueUpTo_min (p : Nat → Bool) :
    ∀ n j, j ≤ n → p j = true → leastTrueUpTo p n ≤ j := by
  intro n
  induction n with
  | zero =>
      intro j hj hpj
      simp only [leastTrueUpTo]
      omega
  | succ n ih =>
      intro j hj hpj
      simp only [leastTrueUpTo]
      split
      next hprev =>
        by_cases hjn : j ≤ n
        · exact ih j hjn hpj
        · have hk := leastTrueUpTo_le p n
          omega
      next hprev =>
        have hjnot : ¬ j ≤ n := by
          intro hjn
          have hfound := leastTrueUpTo_true_of_exists p n
            ⟨j, hjn, hpj⟩
          exact hprev hfound
        omega

private def serviceTest {m : Nat}
    (w : Nat → StageThree.Activation m) (i : Fin m)
    (t q : Nat) : Bool :=
  decide (t < q ∧ (w q).1 = i)

/-- An arbitrary future service supplied by fairness; it bounds the finite
leftmost search used below. -/
private noncomputable def serviceUpper {m : Nat}
    (w : Nat → StageThree.Activation m) (hinf : FairStream w)
    (i : Fin m) (t : Nat) : Nat :=
  Classical.choose (hinf i t)

private theorem serviceUpper_spec {m : Nat}
    (w : Nat → StageThree.Activation m) (hinf : FairStream w)
    (i : Fin m) (t : Nat) :
    t < serviceUpper w hinf i t ∧
      (w (serviceUpper w hinf i t)).1 = i := by
  unfold serviceUpper
  exact Classical.choose_spec (hinf i t)

/-- Least activation index of `i` strictly after `t`. -/
noncomputable def nextServiceIndex {m : Nat}
    (w : Nat → StageThree.Activation m) (hinf : FairStream w)
    (i : Fin m) (t : Nat) : Nat :=
  leastTrueUpTo (serviceTest w i t) (serviceUpper w hinf i t)

theorem nextServiceIndex_spec {m : Nat}
    (w : Nat → StageThree.Activation m) (hinf : FairStream w)
    (i : Fin m) (t : Nat) :
    t < nextServiceIndex w hinf i t ∧
      (w (nextServiceIndex w hinf i t)).1 = i := by
  unfold nextServiceIndex
  have hu := serviceUpper_spec w hinf i t
  have htest :
      serviceTest w i t (serviceUpper w hinf i t) = true := by
    simp [serviceTest, hu.1, hu.2]
  have hfound := leastTrueUpTo_true_of_true_at
    (serviceTest w i t) (serviceUpper w hinf i t) htest
  unfold serviceTest at hfound
  exact of_decide_eq_true hfound

theorem nextServiceIndex_min {m : Nat}
    (w : Nat → StageThree.Activation m) (hinf : FairStream w)
    (i : Fin m) (t q : Nat)
    (hq : t < q ∧ (w q).1 = i) :
    nextServiceIndex w hinf i t ≤ q := by
  unfold nextServiceIndex
  have hqtest : serviceTest w i t q = true := by
    simp [serviceTest, hq.1, hq.2]
  rcases Nat.le_total q (serviceUpper w hinf i t) with hqu | huq
  · exact leastTrueUpTo_min (serviceTest w i t)
      (serviceUpper w hinf i t) q hqu hqtest
  · exact Nat.le_trans
      (leastTrueUpTo_le (serviceTest w i t) (serviceUpper w hinf i t)) huq

/-- State index immediately after the least future activation. -/
noncomputable def serviceTime {m : Nat}
    (w : Nat → StageThree.Activation m) (hinf : FairStream w)
    (i : Fin m) (t : Nat) : Nat :=
  Nat.succ (nextServiceIndex w hinf i t)

theorem serviceTime_after {m : Nat}
    (w : Nat → StageThree.Activation m) (hinf : FairStream w)
    (i : Fin m) (t : Nat) :
    t < serviceTime w hinf i t := by
  have hspec := (nextServiceIndex_spec w hinf i t).1
  unfold serviceTime
  omega

theorem serviceTime_mono {m : Nat}
    (w : Nat → StageThree.Activation m) (hinf : FairStream w)
    (i : Fin m) (t t' : Nat) (htt : t ≤ t') :
    serviceTime w hinf i t ≤ serviceTime w hinf i t' := by
  have hspec := nextServiceIndex_spec w hinf i t'
  have hcand : t < nextServiceIndex w hinf i t' ∧
      (w (nextServiceIndex w hinf i t')).1 = i := by
    constructor
    · omega
    · exact hspec.2
  have hmin := nextServiceIndex_min w hinf i t
    (nextServiceIndex w hinf i t') hcand
  unfold serviceTime
  omega

/-! ## The actual stream supplies ClearProcess -/

/-- The temporal ClearProcess required by StageThree is realized by the
literal fair activation stream. -/
theorem clear_process_stream {m B M D : Nat}
    (hM : StageTwo.ClockParams M) (hm : 0 < m)
    (hquietPres : QuietPreserved B M D hm)
    (s : Fin m → NativeRecord)
    (hquiet : StageThree.Quiet M hm s)
    (hfrozen : StageThree.Frozen M D hm s)
    (hwell : StageTwo.WellFormed M s)
    (w : Nat → StageThree.Activation m) (hinf : FairStream w) :
    StageThree.ClearProcess M hm s
      (serviceTime w hinf)
      (fun u t => (streamState B M hm s w t u).err = false) := by
  refine
    { service_after := ?_
      service_mono := ?_
      correct_mono := ?_
      poll := ?_ }
  · intro i t
    exact serviceTime_after w hinf i t
  · intro i t t' htt
    exact serviceTime_mono w hinf i t t' htt
  · intro i t t' htt hclear
    exact stream_correct_mono hM hm hquietPres s hquiet hfrozen hwell
      w i htt hclear
  · intro u t herr hdeps
    let q := nextServiceIndex w hinf u t
    have hspec : t < q ∧ (w q).1 = u := by
      dsimp [q]
      exact nextServiceIndex_spec w hinf u t
    have hservice : serviceTime w hinf u t = Nat.succ q := by
      rfl
    change
      (streamState B M hm s w (serviceTime w hinf u t) u).err = false
    rw [hservice]
    by_cases hqu : (streamState B M hm s w q u).err = true
    · have hfacts := stream_facts hM hm hquietPres s
        hquiet hfrozen hwell w q
      have hrunU :
          (StageThree.runActivations B M hm s ((List.range q).map w) u).err =
            true := by
        simpa only [streamState] using hqu
      have hmonoUraw := StageThree.error_monotone_run
        (B := B) (M := M) (D := D) hm
        s ((List.range q).map w) hfacts.1 u hrunU
      have hmonoU :
          (s u).err = true ∧
            StageThree.signedVal M (streamState B M hm s w q u) =
              StageThree.signedVal M (s u) := by
        simpa only [streamState] using hmonoUraw
      have hhigher :
          ∀ v, StageThree.Neighbor hm u v →
            StageThree.signedVal M (streamState B M hm s w q u) <
              StageThree.signedVal M (streamState B M hm s w q v) →
            (streamState B M hm s w q v).err = false := by
        intro v hneighbor hstrict
        by_cases hqv : (streamState B M hm s w q v).err = true
        · have hrunV :
              (StageThree.runActivations B M hm s
                ((List.range q).map w) v).err = true := by
            simpa only [streamState] using hqv
          have hmonoVraw := StageThree.error_monotone_run
            (B := B) (M := M) (D := D) hm
            s ((List.range q).map w) hfacts.1 v hrunV
          have hmonoV :
              (s v).err = true ∧
                StageThree.signedVal M (streamState B M hm s w q v) =
                  StageThree.signedVal M (s v) := by
            simpa only [streamState] using hmonoVraw
          have hstrictInitial :
              StageThree.signedVal M (s u) <
                StageThree.signedVal M (s v) := by
            calc
              StageThree.signedVal M (s u) =
                  StageThree.signedVal M
                    (streamState B M hm s w q u) := hmonoU.2.symm
              _ < StageThree.signedVal M
                    (streamState B M hm s w q v) := hstrict
              _ = StageThree.signedVal M (s v) := hmonoV.2
          have hedge : StageThree.DepEdge M hm s u v :=
            ⟨hneighbor, herr, hmonoV.1, hstrictInitial⟩
          have hclearedAtT := hdeps v hedge
          have hclearedAtQ :
              (streamState B M hm s w q v).err = false :=
            stream_correct_mono hM hm hquietPres s hquiet hfrozen hwell
              w v (t := t) (t' := q) (Nat.le_of_lt hspec.1) hclearedAtT
          rw [hqv] at hclearedAtQ
          cases hclearedAtQ
        · cases hv : (streamState B M hm s w q v).err with
          | false => rfl
          | true => exact False.elim (hqv hv)
      have hdomain :
          StageThree.ClockDomain M (streamState B M hm s w q) :=
        clockDomain_of_wellFormed hM (streamState B M hm s w q)
          hfacts.2.2.2
      have hclear := StageThree.clears_on_poll
        (B := B) (M := M) (D := D) hm
        (streamState B M hm s w q) u (w q).2 hdomain
        hfacts.2.1 hfacts.2.2.1 hqu hhigher
      rw [streamState_succ B M hm s w q, hspec.2]
      exact hclear
    · have hquFalse : (streamState B M hm s w q u).err = false := by
        cases hv : (streamState B M hm s w q u).err with
        | false => rfl
        | true => exact False.elim (hqu hv)
      exact stream_correct_mono hM hm hquietPres s hquiet hfrozen hwell
        w u (t := q) (t' := Nat.succ q) (by omega) hquFalse

/-! ## Clearance of every initial error -/

/-- Every initial error clears by the service time along a fixed dependency
path of at most `D+1` vertices. The accepted StageThree.clear_time theorem is
exactly the already-proved combination of the recursive clearance argument
with the dependency-path bound. -/
theorem all_clear_time {m B M D : Nat}
    (hM : StageTwo.ClockParams M) (hm : 0 < m)
    (hquietPres : QuietPreserved B M D hm)
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
  have hproc := clear_process_stream hM hm hquietPres s
    hquiet hfrozen hwell w hinf
  exact StageThree.clear_time hm s hfrozen
    (serviceTime w hinf) 0
    (fun v t => (streamState B M hm s w t v).err = false)
    hproc u herr

end L4.Height.Recover
