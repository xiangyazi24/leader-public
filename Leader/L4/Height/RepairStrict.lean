import Leader.L4.Height.RepairTime

namespace L4.Height

open Classical

set_option maxRecDepth 8192
set_option maxHeartbeats 12000000

/-- Unlike StageCover, coverage is asserted only at proper prefixes. -/
def StageCoverStrict {α : Type} {n : Nat}
    (next : α → Fin n → α) (Src Tgt : α → Prop)
    (L Nq Mq : Nat) : Prop :=
  ∀ x, Src x →
    ∃ Ws : List (Thru.Word n → Nat),
      Ws.length = Nq ∧
      (∀ W, W ∈ Ws → ∀ t,
        Thru.wordSum
            (fun u => 2 ^ (Nat.min (W u) t / L)) t ≤
          Mq * n ^ t) ∧
      (∀ u : Thru.Word n, ∀ k,
        Thru.maxWait Ws u ≤ k →
        k < u.length →
        Tgt (runWord next x (u.take k)))

theorem stage_mean_strict {α : Type} {n L Nq Mq : Nat}
    (next : α → Fin n → α) (Src Tgt : α → Prop)
    (hCover : StageCoverStrict next Src Tgt L Nq Mq)
    (hNq : 1 ≤ Nq) (hMq : 1 ≤ Mq) (hL : 1 ≤ L)
    (x : α) (hx : Src x) :
    IIDExpectedHittingTimeAtMost next Tgt x
      (L * (Nat.log2 Nq + Nat.log2 Mq + 4)) := by
  rcases hCover x hx with ⟨Ws, hLength, hEach, hReach⟩
  unfold IIDExpectedHittingTimeAtMost
  intro t
  have hmax :
      Thru.wordSum
          (fun u => Nat.min (Thru.maxWait Ws u) t) t ≤
        L * (Nat.log2 Nq + Nat.log2 Mq + 4) * n ^ t := by
    exact Thru.mean_max Ws Nq Mq L t
      hLength hNq hMq hL
      (fun W hW => hEach W hW t)
  have hpoint :
      ∀ u, u.length = t →
        stoppedTime next Tgt x u ≤
          Nat.min (Thru.maxWait Ws u) t := by
    intro u hu
    by_cases hw : Thru.maxWait Ws u < t
    · have hwlen : Thru.maxWait Ws u ≤ u.length := by omega
      have hwstrict : Thru.maxWait Ws u < u.length := by omega
      have hhit :
          Tgt (runWord next x
            (u.take (Thru.maxWait Ws u))) :=
        hReach u (Thru.maxWait Ws u)
          (Nat.le_refl _) hwstrict
      have hstop := repair_stoppedTime_le_prefix
        next Tgt x u (Thru.maxWait Ws u) hwlen hhit
      have hle : Thru.maxWait Ws u ≤ t := by omega
      simpa only [Nat.min_eq_left hle] using hstop
    · have htmax : t ≤ Thru.maxWait Ws u := by omega
      have hstop := stoppedTime_le_length next Tgt x u
      have hstop' : stoppedTime next Tgt x u ≤ t := by
        rw [hu] at hstop
        exact hstop
      simpa only [Nat.min_eq_right htmax] using hstop'
  calc
    iidHitCost next Tgt t x =
        wordSum (stoppedTime next Tgt x) t :=
      iidHitCost_eq_wordSum next Tgt t x
    _ ≤ wordSum
          (fun u => Nat.min (Thru.maxWait Ws u) t) t :=
      repair_wordSum_mono_length
        (stoppedTime next Tgt x)
        (fun u => Nat.min (Thru.maxWait Ws u) t)
        t hpoint
    _ = Thru.wordSum
          (fun u => Nat.min (Thru.maxWait Ws u) t) t :=
      repair_wordSum_eq_thru
        (fun u => Nat.min (Thru.maxWait Ws u) t) t
    _ ≤ L * (Nat.log2 Nq + Nat.log2 Mq + 4) * n ^ t :=
      hmax

theorem repair_mean_strict {α : Type} {n : Nat}
    (next : α → Fin n → α)
    (Cust Qu Fr Lg : α → Prop)
    (L NqQuiet MqQuiet NqFrozen MqFrozen NqClear MqClear : Nat)
    (hL : 1 ≤ L)
    (hNqQuiet : 1 ≤ NqQuiet) (hMqQuiet : 1 ≤ MqQuiet)
    (hNqFrozen : 1 ≤ NqFrozen) (hMqFrozen : 1 ≤ MqFrozen)
    (hNqClear : 1 ≤ NqClear) (hMqClear : 1 ≤ MqClear)
    (hQuClosed : ∀ x e, Qu x → Qu (next x e))
    (hFrClosed : ∀ x e, Fr x → Fr (next x e))
    (_hLgClosed : ∀ x e, Lg x → Lg (next x e))
    (hQuietCover :
      StageCoverStrict next Cust Qu L NqQuiet MqQuiet)
    (hFrozenCover :
      StageCoverStrict next Qu Fr L NqFrozen MqFrozen)
    (hClearCover :
      StageCoverStrict next Fr Lg L NqClear MqClear)
    (x : α) (hxCust : Cust x) :
    IIDExpectedHittingTimeAtMost next Lg x
      (repairBound L
        NqQuiet MqQuiet NqFrozen MqFrozen NqClear MqClear) := by
  have hCQ : ∀ y, Cust y →
      IIDExpectedHittingTimeAtMost next Qu y
        (stageBound L NqQuiet MqQuiet) := by
    intro y hy
    exact stage_mean_strict
      (next := next) (Src := Cust) (Tgt := Qu)
      (L := L) (Nq := NqQuiet) (Mq := MqQuiet)
      hQuietCover hNqQuiet hMqQuiet hL y hy
  have hQF : ∀ y, Qu y →
      IIDExpectedHittingTimeAtMost next Fr y
        (stageBound L NqFrozen MqFrozen) := by
    intro y hy
    exact stage_mean_strict
      (next := next) (Src := Qu) (Tgt := Fr)
      (L := L) (Nq := NqFrozen) (Mq := MqFrozen)
      hFrozenCover hNqFrozen hMqFrozen hL y hy
  have hFL : ∀ y, Fr y →
      IIDExpectedHittingTimeAtMost next Lg y
        (stageBound L NqClear MqClear) := by
    intro y hy
    exact stage_mean_strict
      (next := next) (Src := Fr) (Tgt := Lg)
      (L := L) (Nq := NqClear) (Mq := MqClear)
      hClearCover hNqClear hMqClear hL y hy
  have hCF : ∀ y, Cust y →
      IIDExpectedHittingTimeAtMost next Fr y
        (stageBound L NqQuiet MqQuiet +
          stageBound L NqFrozen MqFrozen) := by
    intro y hy
    exact expected_then_closed
      (next := next) (A := Cust) (B := Qu) (C := Fr)
      (a := stageBound L NqQuiet MqQuiet)
      (b := stageBound L NqFrozen MqFrozen)
      hCQ hQuClosed hQF y hy
  have hCL := expected_then_closed
    (next := next) (A := Cust) (B := Fr) (C := Lg)
    (a := stageBound L NqQuiet MqQuiet +
      stageBound L NqFrozen MqFrozen)
    (b := stageBound L NqClear MqClear)
    hCF hFrClosed hFL x hxCust
  simpa only [repairBound] using hCL

/-- A strict first-hit time really witnesses the target. -/
theorem wait_lt_length_hit {α : Type} {n : Nat}
    (next : α → Fin n → α) (A : α → Prop) :
    ∀ (x : α) (u : Thru.Word n),
      Thru.wait next A x u < u.length →
      A (runWord next x
        (u.take (Thru.wait next A x u))) := by
  intro x u
  induction u generalizing x with
  | nil =>
      intro h
      simp [Thru.wait] at h
  | cons e u ih =>
      intro h
      by_cases hx : A x
      · have hw : Thru.wait next A x (e :: u) = 0 :=
          Thru.wait_of_hit next A x hx (e :: u)
        simpa [hw, runWord] using hx
      · have hw := Thru.wait_cons_of_not next A x hx e u
        rw [hw] at h ⊢
        have ht : Thru.wait next A (next x e) u < u.length := by
          simp only [List.length_cons] at h
          omega
        have htail := ih (next x e) ht
        simpa [runWord] using htail

/-- For singleton query lists, seqWait is exactly wait. -/
theorem seqWait_single_lt_length_hit {α : Type} {n : Nat}
    (next : α → Fin n → α) (A : α → Prop)
    (x : α) (u : Thru.Word n)
    (h : Thru.seqWait next [A] x u < u.length) :
    A (runWord next x
      (u.take (Thru.seqWait next [A] x u))) := by
  rw [Thru.seqWait_single] at h ⊢
  exact wait_lt_length_hit next A x u h

/-- A nontrivial model and its concrete witness family. -/
def strictBoolNext (x : Bool) (e : Fin 2) : Bool :=
  x || (e.val == 1)

noncomputable def strictBoolWs (x : Bool) :
    List (Thru.Word 2 → Nat) :=
  [Thru.wait strictBoolNext (fun y => y = true) x]

theorem strictBoolWs_length (x : Bool) :
    (strictBoolWs x).length = 1 := by
  rfl

/-- Initially false, hence the target is genuinely nontrivial. -/
theorem strictBool_initially_outside :
    ¬ ((false : Bool) = true) := by decide

/-- Direct one-step check of the strict stopping convention. -/
theorem strictBool_one_step_hit :
    strictBoolNext false ⟨1, by decide⟩ = true := by decide

end L4.Height
