import Leader.L4.Height.ChainRepair
import Leader.L4.Height.QuietCover

/-!
# Bridge the StageOne strict cover into the three-stage chain repair

The Chain interface stores literal StageThree activations, while CoverOne
expects the equivalent StageOne activation.  The accepted activate_one_eq
bridge transports the chain.  WellFormed is carried separately through the
scheduler prefix, upgrading StageOne all-quiet to Chain.QuSet.
-/

namespace L4.Height.Recover.Chain

open L4.Compiler.Native
open L4.Height
open Classical

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000

noncomputable section

variable {α : Type} {n m B M D L : Nat} {hm : 0 < m}

/-- Regard a Chain clock driver as the StageOne clock driver consumed by the
strict quiet-stage cover. -/
def toCoverOne (C : ClockChain α n m B M hm) :
    CoverOne.ClockChain α n m B M hm where
  next := C.next
  cfg := C.cfg
  act := C.act
  lastAct := C.lastAct
  cfg_next := by
    intro x e
    rw [C.cfg_next x e]
    cases hact : C.act x e with
    | none =>
        simp only [hact]
    | some p =>
        rcases p with ⟨i, delta⟩
        simp only [hact]
        exact (L4.Height.Recover.activate_one_eq
          B M hm (C.cfg x) i delta).symm
  last_next := C.last_next

/-- The transported chain records exactly the same served site. -/
@[simp] theorem toCoverOne_served
    (C : ClockChain α n m B M hm) (i : Fin m) (x : α) :
    CoverOne.ClockChain.served (toCoverOne C) i x ↔
      C.served i x := by
  rfl

/-- Every literal native activation preserves the decoded native range.
Reset creates tick zero, propagation creates a lower-half proposal, clear and
increment create correct records, and hold keeps the old WellFormed record. -/
theorem wellFormed_activate {m B M : Nat}
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

/-- WellFormed persists along every scheduler word of a clock-driving chain. -/
theorem wellFormed_run
    (C : ClockChain α n m B M hm)
    (hM : StageTwo.ClockParams M) :
    ∀ (x : α) (u : Thru.Word n),
      StageTwo.WellFormed M (C.cfg x) →
      StageTwo.WellFormed M (C.cfg (runWord C.next x u)) := by
  intro x u hw
  induction u generalizing x with
  | nil =>
      exact hw
  | cons e u ih =>
      have hstep : StageTwo.WellFormed M (C.cfg (C.next x e)) := by
        cases hact : C.act x e with
        | none =>
            have hcfg : C.cfg (C.next x e) = C.cfg x := by
              simpa [hact] using C.cfg_next x e
            rw [hcfg]
            exact hw
        | some p =>
            rcases p with ⟨i, delta⟩
            have hcfg :
                C.cfg (C.next x e) =
                  StageThree.activate B M hm (C.cfg x) i delta := by
              simpa [hact] using C.cfg_next x e
            rw [hcfg]
            exact wellFormed_activate hM hm (C.cfg x) hw i delta
      exact ih (x := C.next x e) hstep

/-- The StageOne quiet cover, upgraded with preservation of WellFormed, is the
quiet-stage input required by chain_repair. -/
theorem quiet_stage_cover
    (C : ClockChain α n m B M hm) (L : Nat)
    (hM : StageTwo.ClockParams M) (hL : 1 ≤ L)
    (hMom : ∀ i y, Thru.MomentAt C.next (C.served i) L y) :
    StageCoverStrict C.next
      (fun x => StageTwo.WellFormed M (C.cfg x))
      (QuSet C) L m 4 := by
  have hMone : StageOne.ClockParams M :=
    (L4.Height.Recover.clock_params_iff M).2 hM
  have hMomOne :
      ∀ i y, Thru.MomentAt (toCoverOne C).next
        (CoverOne.ClockChain.served (toCoverOne C) i) L y := by
    intro i y
    have hserved :
        CoverOne.ClockChain.served (toCoverOne C) i =
          C.served i := by
      funext z
      exact propext (toCoverOne_served C i z)
    rw [hserved]
    exact hMom i y
  have hcover :
      StageCoverStrict (toCoverOne C).next
        (CoverOne.ClockChain.BoundedSource (toCoverOne C))
        (CoverOne.ClockChain.AllQuiet (toCoverOne C))
        L m 4 :=
    CoverOne.quiet_cover (toCoverOne C) L hMone hL hMomOne
  unfold StageCoverStrict at hcover ⊢
  intro x hx
  have hbound :
      CoverOne.ClockChain.BoundedSource (toCoverOne C) x := by
    unfold CoverOne.ClockChain.BoundedSource
    intro i
    exact (hx i).1
  obtain ⟨Ws, hlen, hmoment, hcoverage⟩ := hcover x hbound
  refine ⟨Ws, hlen, hmoment, ?_⟩
  intro u k hmax hk
  have hone := hcoverage u k hmax hk
  have hpoint :
      ∀ i, StageOne.Quiet M hm
        (C.cfg (runWord C.next x (u.take k))) i := by
    unfold CoverOne.ClockChain.AllQuiet at hone
    simpa only [toCoverOne] using hone
  have hquiet :
      StageThree.Quiet M hm
        (C.cfg (runWord C.next x (u.take k))) :=
    (L4.Height.Recover.quiet_one_iff M hm
      (C.cfg (runWord C.next x (u.take k)))).1 hpoint
  have hwell :
      StageTwo.WellFormed M
        (C.cfg (runWord C.next x (u.take k))) :=
    wellFormed_run C hM x (u.take k) hx
  unfold QuSet
  exact ⟨hquiet, hwell⟩

/-- With the StageOne bridge supplying hQ, only the frozen and clearance
covers remain as external inputs to the accepted three-stage composition. -/
theorem chain_repair_two_covers
    (C : ClockChain α n m B M hm)
    (hM : StageTwo.ClockParams M)
    (hL : 1 ≤ L) (hmOne : 1 ≤ m) (hhalf : 2 * D ≤ m)
    (hMom : ∀ i y, Thru.MomentAt C.next (C.served i) L y)
    (hF : StageCoverStrict C.next (QuSet C) (FrSet C D)
      L (m * m) (4 ^ D))
    (hC : StageCoverStrict C.next (FrSet C D) (LgSet C)
      L (m * 3 ^ (D + 1)) (4 ^ (D + 1))) :
    ∀ x, StageTwo.WellFormed M (C.cfg x) →
      IIDExpectedHittingTimeAtMost C.next (LgSet C) x
        (17 * L * m) := by
  exact chain_repair C
    (fun x => StageTwo.WellFormed M (C.cfg x))
    hM hL hmOne hhalf
    (quiet_stage_cover C L hM hL hMom) hF hC

end

end L4.Height.Recover.Chain

