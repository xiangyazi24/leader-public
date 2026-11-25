import Leader.L4.Height.RepairStrict
import Leader.L4.Height.QuietBridge

namespace L4.Height.Recover.Chain

open L4.Compiler.Native
open L4.Height

set_option maxRecDepth 8192
set_option maxHeartbeats 12000000

/-- An abstract scheduler chain whose effective steps are either stutters or
literal native-clock activations. -/
structure ClockChain (α : Type) (n m : Nat) (B M : Nat) (hm : 0 < m) where
  next : α → Fin n → α
  cfg : α → Fin m → NativeRecord
  act : α → Fin n → Option (Fin m × Bool)
  lastAct : α → Option (Fin m)
  cfg_next : ∀ x e, cfg (next x e) =
    match act x e with
    | none => cfg x
    | some p => StageThree.activate B M hm (cfg x) p.1 p.2
  last_next : ∀ x e, lastAct (next x e) = (act x e).map Prod.fst

variable {α : Type} {n m B M D L : Nat} {hm : 0 < m}

/-- The site served by the most recent effective activation. -/
def ClockChain.served
    (C : ClockChain α n m B M hm) (i : Fin m) (x : α) : Prop :=
  C.lastAct x = some i

/-- The quiet-stage target, including the decoded native range invariant. -/
def QuSet (C : ClockChain α n m B M hm) (x : α) : Prop :=
  StageThree.Quiet M hm (C.cfg x) ∧
    StageTwo.WellFormed M (C.cfg x)

/-- The frozen-stage target. -/
def FrSet (C : ClockChain α n m B M hm) (D : Nat) (x : α) : Prop :=
  QuSet C x ∧ StageThree.Frozen M D hm (C.cfg x)

/-- The legitimate-clock target used by the physical theorem. -/
def LgSet (C : ClockChain α n m B M hm) (x : α) : Prop :=
  (∀ i, (C.cfg x i).err = false) ∧
    StageThree.Quiet M hm (C.cfg x) ∧
    StageTwo.WellFormed M (C.cfg x)

/-- StageThree quietness is preserved by one literal activation.  This is the
pointwise StageOne theorem transported through the accepted bridges. -/
private theorem quiet_activate {m B M : Nat}
    (hM : StageTwo.ClockParams M) (hm : 0 < m)
    (c : Fin m → NativeRecord) (i : Fin m) (delta : Bool)
    (hq : StageThree.Quiet M hm c) :
    StageThree.Quiet M hm (StageThree.activate B M hm c i delta) := by
  have hMone : StageOne.ClockParams M :=
    (L4.Height.Recover.clock_params_iff M).2 hM
  have hone : ∀ j, StageOne.Quiet M hm c j :=
    (L4.Height.Recover.quiet_one_iff M hm c).2 hq
  have hnextOne :
      ∀ j, StageOne.Quiet M hm
        (StageOne.activate B M hm c i delta) j := by
    intro j
    exact StageOne.quiet_preserved (B := B) hMone hm
      c j i delta (hone j)
  have hnextThree :
      StageThree.Quiet M hm
        (StageOne.activate B M hm c i delta) :=
    (L4.Height.Recover.quiet_one_iff M hm
      (StageOne.activate B M hm c i delta)).1 hnextOne
  rw [L4.Height.Recover.activate_one_eq B M hm c i delta]
    at hnextThree
  exact hnextThree

/-- The decoded native range is in fact preserved without a Frozen premise.
Reset and propagation create only lower-half errors, clear and increment create
correct records, and hold preserves the old record. -/
private theorem wellFormed_activate {m B M : Nat}
    (hM : StageTwo.ClockParams M) (hm : 0 < m)
    (c : Fin m → NativeRecord) (hw : StageTwo.WellFormed M c)
    (i : Fin m) (delta : Bool) :
    StageTwo.WellFormed M (StageThree.activate B M hm c i delta) := by
  have hparams := hM
  unfold StageTwo.ClockParams at hparams
  have hMpos : 0 < M := by omega
  have hhalfPos : 0 < M / 2 := by omega
  have hhalfLe : M / 2 ≤ M := by omega
  rw [← L4.Height.Recover.activate_eq B M hm c i delta]
  unfold StageTwo.WellFormed
  intro j
  by_cases hji : j = i
  · subst j
    rw [StageTwo.activate_self_eq_finish]
    unfold StageTwo.actionAt
    rw [StageTwo.nativeClock_eq_spec]
    unfold StageTwo.clockSpec
    split
    next _ =>
      change 0 < M ∧ (true = true → 0 < M / 2)
      exact ⟨hMpos, fun _ => hhalfPos⟩
    next _ =>
      split
      next hprop =>
        have hleastHalf :
            StageTwo.leastTick M (c (left hm i)) (c i)
                (c (right hm i)) < M / 2 := by
          rcases StageTwo.least_lt_cases M
              (c (left hm i)) (c i) (c (right hm i)) hprop with
            hleft | hright
          · have hp := StageTwo.proposal_lt_center M
              (c i) (c (left hm i)) hleft
            have heq :
                StageTwo.proposalTick M (c i) (c (left hm i)) =
                  (c (left hm i)).tick + 1 := by
              simp [StageTwo.proposalTick, hp.1, hp.2.1, hp.2.2]
            unfold StageTwo.leastTick
            rw [heq]
            exact Nat.lt_of_le_of_lt (Nat.min_le_left _ _) hp.2.1
          · have hp := StageTwo.proposal_lt_center M
              (c i) (c (right hm i)) hright
            have heq :
                StageTwo.proposalTick M (c i) (c (right hm i)) =
                  (c (right hm i)).tick + 1 := by
              simp [StageTwo.proposalTick, hp.1, hp.2.1, hp.2.2]
            unfold StageTwo.leastTick
            rw [heq]
            exact Nat.lt_of_le_of_lt (Nat.min_le_right _ _) hp.2.1
        change
          StageTwo.leastTick M (c (left hm i)) (c i)
                (c (right hm i)) < M ∧
            (true = true →
              StageTwo.leastTick M (c (left hm i)) (c i)
                (c (right hm i)) < M / 2)
        constructor
        · exact Nat.lt_of_lt_of_le hleastHalf hhalfLe
        · intro _
          exact hleastHalf
      next _ =>
        split
        next _ =>
          change (c i).tick < M ∧
            (false = true → (c i).tick < M / 2)
          refine ⟨(hw i).1, ?_⟩
          intro hbad
          cases hbad
        next _ =>
          split
          next _ =>
            have hs := StageTwo.successor_lt_modulus
              M (c i).tick hM (hw i).1
            change successor M (c i).tick < M ∧
              (false = true → successor M (c i).tick < M / 2)
            refine ⟨hs, ?_⟩
            intro hbad
            cases hbad
          next _ =>
            simpa only [finishNative] using hw i
  · rw [StageTwo.activate_other B M hm c i j delta hji]
    exact hw j

/-- Quiet plus WellFormed is forward closed along any clock-driving chain. -/
theorem qu_closed (C : ClockChain α n m B M hm)
    (hM : StageTwo.ClockParams M) :
    ∀ x e, QuSet C x → QuSet C (C.next x e) := by
  intro x e hx
  unfold QuSet at hx ⊢
  rcases hx with ⟨hq, hw⟩
  cases hact : C.act x e with
  | none =>
      have hcfg : C.cfg (C.next x e) = C.cfg x := by
        simpa [hact] using C.cfg_next x e
      rw [hcfg]
      exact ⟨hq, hw⟩
  | some p =>
      rcases p with ⟨i, delta⟩
      have hcfg :
          C.cfg (C.next x e) =
            StageThree.activate B M hm (C.cfg x) i delta := by
        simpa [hact] using C.cfg_next x e
      rw [hcfg]
      exact ⟨quiet_activate hM hm (C.cfg x) i delta hq,
        wellFormed_activate hM hm (C.cfg x) hw i delta⟩

/-- Quiet, Frozen, and WellFormed are forward closed along the chain. -/
theorem fr_closed (C : ClockChain α n m B M hm) (D : Nat)
    (hM : StageTwo.ClockParams M) :
    ∀ x e, FrSet C D x → FrSet C D (C.next x e) := by
  intro x e hx
  unfold FrSet at hx ⊢
  rcases hx with ⟨hqu, hfrozen⟩
  have hquNext := qu_closed C hM x e hqu
  refine ⟨hquNext, ?_⟩
  unfold QuSet at hqu
  cases hact : C.act x e with
  | none =>
      have hcfg : C.cfg (C.next x e) = C.cfg x := by
        simpa [hact] using C.cfg_next x e
      rw [hcfg]
      exact hfrozen
  | some p =>
      rcases p with ⟨i, delta⟩
      have hcfg :
          C.cfg (C.next x e) =
            StageThree.activate B M hm (C.cfg x) i delta := by
        simpa [hact] using C.cfg_next x e
      have hraw :=
        (L4.Height.Recover.frozen_iff M D hm (C.cfg x)).1 hfrozen
      have hquietTwo : StageTwo.Quiet M hm (C.cfg x) :=
        (L4.Height.Recover.quiet_iff M hm (C.cfg x)).2 hqu.1
      have hpres := StageTwo.frozen_preserved B M D hM hm
        (C.cfg x) hquietTwo hraw.1 hraw.2 hqu.2 i delta
      have hrawNext :
          StageTwo.Frozen hm
              (StageThree.activate B M hm (C.cfg x) i delta) ∧
            StageTwo.Below D
              (StageThree.activate B M hm (C.cfg x) i delta) := by
        rw [← L4.Height.Recover.activate_eq B M hm
          (C.cfg x) i delta]
        exact ⟨hpres.1, hpres.2.1⟩
      rw [hcfg]
      exact (L4.Height.Recover.frozen_iff M D hm
        (StageThree.activate B M hm (C.cfg x) i delta)).2 hrawNext

/-- An all-correct configuration satisfies every Frozen condition vacuously. -/
private theorem correct_frozen {m M D : Nat} (hm : 0 < m)
    (c : Fin m → NativeRecord)
    (hc : ∀ i, (c i).err = false) :
    StageThree.Frozen M D hm c := by
  unfold StageThree.Frozen
  intro i hi
  rw [hc i] at hi
  cases hi

/-- A quiet all-correct configuration stays all-correct after one activation. -/
private theorem correct_activate {m B M : Nat} (hm : 0 < m)
    (c : Fin m → NativeRecord) (i : Fin m) (delta : Bool)
    (hc : ∀ j, (c j).err = false)
    (hq : StageThree.Quiet M hm c) :
    ∀ j, (StageThree.activate B M hm c i delta j).err = false := by
  intro j
  have hfrozen : StageThree.Frozen M 0 hm c :=
    correct_frozen hm c hc
  cases hnew : (StageThree.activate B M hm c i delta j).err with
  | false => rfl
  | true =>
      have hmono := StageThree.error_monotone
        (B := B) (M := M) (D := 0) hm
        c i delta hq hfrozen j hnew
      have hbad := hmono.1
      rw [hc j] at hbad
      cases hbad

/-- The all-correct quiet target is also forward closed. -/
theorem lg_closed (C : ClockChain α n m B M hm)
    (hM : StageTwo.ClockParams M) :
    ∀ x e, LgSet C x → LgSet C (C.next x e) := by
  intro x e hx
  unfold LgSet at hx ⊢
  rcases hx with ⟨hcorrect, hquiet, hwell⟩
  have hqu : QuSet C x := ⟨hquiet, hwell⟩
  have hquNext := qu_closed C hM x e hqu
  unfold QuSet at hquNext
  have hcorrectNext :
      ∀ j, (C.cfg (C.next x e) j).err = false := by
    cases hact : C.act x e with
    | none =>
        have hcfg : C.cfg (C.next x e) = C.cfg x := by
          simpa [hact] using C.cfg_next x e
        rw [hcfg]
        exact hcorrect
    | some p =>
        rcases p with ⟨i, delta⟩
        have hcfg :
            C.cfg (C.next x e) =
              StageThree.activate B M hm (C.cfg x) i delta := by
          simpa [hact] using C.cfg_next x e
        rw [hcfg]
        exact correct_activate hm (C.cfg x) i delta hcorrect hquiet
  exact ⟨hcorrectNext, hquNext.1, hquNext.2⟩

/-- The three strict stage covers give the uniform `17 L m` recovery bound. -/
theorem chain_repair (C : ClockChain α n m B M hm)
    (Cust : α → Prop)
    (hM : StageTwo.ClockParams M)
    (hL : 1 ≤ L) (hmOne : 1 ≤ m) (hhalf : 2 * D ≤ m)
    (hQ : StageCoverStrict C.next Cust (QuSet C) L m 4)
    (hF : StageCoverStrict C.next (QuSet C) (FrSet C D)
      L (m * m) (4 ^ D))
    (hC : StageCoverStrict C.next (FrSet C D) (LgSet C)
      L (m * 3 ^ (D + 1)) (4 ^ (D + 1))) :
    ∀ x, Cust x →
      IIDExpectedHittingTimeAtMost C.next (LgSet C) x (17 * L * m) := by
  intro x hx
  have hFour : 1 ≤ (4 : Nat) := by omega
  have hNqFrozen : 1 ≤ m * m := by
    have hp : 0 < m * m := Nat.mul_pos hm hm
    omega
  have hMqFrozen : 1 ≤ 4 ^ D := by
    have hp : 0 < 4 ^ D := Nat.pow_pos (by omega)
    omega
  have hNqClear : 1 ≤ m * 3 ^ (D + 1) := by
    have hthree : 0 < 3 ^ (D + 1) := Nat.pow_pos (by omega)
    have hp : 0 < m * 3 ^ (D + 1) := Nat.mul_pos hm hthree
    omega
  have hMqClear : 1 ≤ 4 ^ (D + 1) := by
    have hp : 0 < 4 ^ (D + 1) := Nat.pow_pos (by omega)
    omega
  have hmean :
      IIDExpectedHittingTimeAtMost C.next (LgSet C) x
        (repairTimeBudget L m D) := by
    have hraw := repair_mean_strict
      (next := C.next)
      (Cust := Cust) (Qu := QuSet C) (Fr := FrSet C D) (Lg := LgSet C)
      (L := L)
      (NqQuiet := m) (MqQuiet := 4)
      (NqFrozen := m * m) (MqFrozen := 4 ^ D)
      (NqClear := m * 3 ^ (D + 1)) (MqClear := 4 ^ (D + 1))
      hL hmOne hFour hNqFrozen hMqFrozen hNqClear hMqClear
      (qu_closed C hM) (fr_closed C D hM) (lg_closed C hM)
      hQ hF hC x hx
    simpa only [repairTimeBudget] using hraw
  exact expected_bound_mono
    (next := C.next) (target := LgSet C) (x := x)
    hmean (repair_budget_seventeen L m D hmOne hhalf)

end L4.Height.Recover.Chain
