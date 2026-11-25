import Leader.L4.Height.ChainRepair
import Leader.L4.Height.ClearCover

namespace L4.Height.Recover.ChainThree

open L4.Compiler.Native
open L4.Height
open Classical

set_option maxRecDepth 8192
set_option maxHeartbeats 40000000

noncomputable section

/-! ## Transport between the two clock-chain interfaces -/

/-- `Chain.ClockChain` and `CoverThree.ClockChain` have the same literal
fields.  This adapter is therefore definitionally transparent on every
projection used by the stage-three cover. -/
def toCoverThree
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : Chain.ClockChain α n m B M hm) :
    CoverThree.ClockChain α n m B M hm where
  next := C.next
  cfg := C.cfg
  act := C.act
  lastAct := C.lastAct
  cfg_next := C.cfg_next
  last_next := C.last_next

@[simp] theorem toCoverThree_served
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : Chain.ClockChain α n m B M hm)
    (i : Fin m) (x : α) :
    CoverThree.ClockChain.served (toCoverThree C) i x ↔
      Chain.ClockChain.served C i x := by
  rfl

@[simp] theorem toCoverThree_runWord
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : Chain.ClockChain α n m B M hm)
    (x : α) (u : List (Fin n)) :
    L4.Height.runWord (toCoverThree C).next x u =
      L4.Height.runWord C.next x u := by
  rfl

/-! ## Preservation of the decoded native range -/

/-- The decoded native range is preserved by one literal StageThree
activation.  Reset creates the base error, propagation creates a lower-half
error, clear and increment create correct records, and hold preserves the old
record. -/
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

private theorem wellFormed_next
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : Chain.ClockChain α n m B M hm)
    (hM : StageTwo.ClockParams M)
    (x : α) (e : Fin n)
    (hw : StageTwo.WellFormed M (C.cfg x)) :
    StageTwo.WellFormed M (C.cfg (C.next x e)) := by
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

/-- WellFormed persists along every finite scheduler word of the abstract
clock-driving chain. -/
theorem wellFormed_run
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : Chain.ClockChain α n m B M hm)
    (hM : StageTwo.ClockParams M) :
    ∀ (x : α), StageTwo.WellFormed M (C.cfg x) →
      ∀ u : List (Fin n),
        StageTwo.WellFormed M
          (C.cfg (L4.Height.runWord C.next x u)) := by
  intro x hx u
  induction u generalizing x with
  | nil =>
      simpa [L4.Height.runWord] using hx
  | cons e u ih =>
      have hnext := wellFormed_next C hM x e hx
      simpa [L4.Height.runWord] using
        (ih (C.next x e) hnext)

/-! ## The stage-three cover in the ChainRepair vocabulary -/

/-- The accepted dependency-path cover, transported to `Chain.ClockChain` and
strengthened by the independently preserved WellFormed invariant, is exactly
the `hC` input expected by `Chain.chain_repair`. -/
theorem clear_stage_cover
    {α : Type} {n m B M L D : Nat} (hm : 0 < m)
    (C : Chain.ClockChain α n m B M hm)
    (hM : StageTwo.ClockParams M)
    (hD : D = m / 2)
    (hMom : ∀ i y,
      Thru.MomentAt C.next (Chain.ClockChain.served C i) L y) :
    StageCoverStrict C.next (Chain.FrSet C D) (Chain.LgSet C)
      L (m * 3 ^ (D + 1)) (4 ^ (D + 1)) := by
  let Cthree := toCoverThree C
  have hMomThree :
      ∀ i y,
        Thru.MomentAt Cthree.next
          (CoverThree.ClockChain.served Cthree i) L y := by
    intro i y
    change Thru.MomentAt C.next
      (fun z => C.lastAct z = some i) L y
    exact hMom i y
  have hcover := CoverThree.clear_cover hm Cthree hM hD hMomThree
  unfold StageCoverStrict at hcover ⊢
  intro x hx
  unfold Chain.FrSet at hx
  unfold Chain.QuSet at hx
  rcases hx with ⟨⟨hquiet, hwell⟩, hfrozen⟩
  have hxSrc : CoverThree.Src Cthree D x := by
    unfold CoverThree.Src
    change
      StageThree.Quiet M hm (C.cfg x) ∧
        StageThree.Frozen M D hm (C.cfg x) ∧
          StageTwo.WellFormed M (C.cfg x)
    exact ⟨hquiet, hfrozen, hwell⟩
  obtain ⟨Ws, hlength, heach, hstrict⟩ := hcover x hxSrc
  refine ⟨Ws, hlength, heach, ?_⟩
  intro u k hmax hk
  have htgt := hstrict u k hmax hk
  have hwellRun := wellFormed_run C hM x hwell (u.take k)
  change
    (∀ i,
      (C.cfg (L4.Height.runWord C.next x (u.take k)) i).err = false) ∧
      StageThree.Quiet M hm
        (C.cfg (L4.Height.runWord C.next x (u.take k))) at htgt
  unfold Chain.LgSet
  exact ⟨htgt.1, htgt.2, hwellRun⟩

#print axioms L4.Height.Recover.ChainThree.toCoverThree_served
#print axioms L4.Height.Recover.ChainThree.wellFormed_activate
#print axioms L4.Height.Recover.ChainThree.wellFormed_run
#print axioms L4.Height.Recover.ChainThree.clear_stage_cover

end

end L4.Height.Recover.ChainThree

