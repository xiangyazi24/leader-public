import Leader.L4.RearTrackGeometry
import Leader.L4.FreshInvariant
import Leader.L4.TaggedTail

/-! # Literal rank dynamics and root-peaceful restart closure -/

namespace L4.RankPhysical
open TaggedTail Classical

private theorem sSucc {n : Nat} (f : Fin (n+1) → Nat) :
    sumEdge f = f 0 + sumEdge (fun j : Fin n => f j.succ) := by
  simp [sumEdge, List.ofFn_succ]

private theorem sConst (n a : Nat) : sumEdge (fun _ : Fin n => a) = n*a := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sSucc, ih, Nat.succ_mul, Nat.add_comm]

private theorem sMono {n : Nat} (f g : Fin n → Nat) (h : ∀ e, f e ≤ g e) :
    sumEdge f ≤ sumEdge g := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    rw [sSucc f, sSucc g]
    exact Nat.add_le_add (h 0) (ih _ _ (fun e => h e.succ))

private theorem sAdd {n : Nat} (f g : Fin n → Nat) :
    sumEdge (fun e => f e + g e) = sumEdge f + sumEdge g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sSucc, sSucc f, sSucc g, ih]; omega

private theorem sSelector {n : Nat} (i : Fin n) (a : Nat) :
    sumEdge (fun e => if e = i then a else 0) = a := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [sSucc]
      have hz : (fun e : Fin n => if e.succ = (0 : Fin (n+1)) then a else 0) =
          (fun _ : Fin n => 0) := by funext e; simp [Fin.succ_ne_zero]
      rw [hz, sConst]
      simp
    · rw [sSucc, if_neg (Ne.symm (Fin.succ_ne_zero j))]
      have hc : (fun e : Fin n => if e.succ = j.succ then a else 0) =
          (fun e : Fin n => if e = j then a else 0) := by funext e; simp
      rw [hc, ih, Nat.zero_add]

/-- On MCOV the incoming marks enumerate exactly the effective roots. -/
def rank {p c n : Nat} (x : Config p c n) : Nat :=
  sumEdge (fun e => (x e).mark.toNat)

/-- A paid root moves into an existing root exactly if its old responder
already carries the next outgoing mark. The resident root then survives. -/
def retirement {p c n : Nat} (x : Config p c n) (e : Fin n) : Bool :=
  geometricPay (x e) (x (rightNeighbor e)) && (x (rightNeighbor e)).mark

private theorem no_self {n : Nat} (hn : 4 ≤ n) (e : Fin n) : rightNeighbor e ≠ e := by
  intro h
  have he : liftedSite e 1 = liftedSite e 0 := by
    simpa [liftedSite_succ,liftedSite_zero] using h
  have he' := liftedSite_inj e (by omega : 1<n) (by omega : 0<n) he
  omega

theorem rank_step {p c n : Nat} (hn : 4 ≤ n) (x : Config p c n) (e : Fin n)
    (hm : MCOV x) :
    rank (step x e) + (retirement x e).toNat = rank x := by
  let r := rightNeighbor e
  by_cases hp : geometricPay (x e) (x r) = true
  · have he0 := RearTrace.paid_was_marked hm e hp
    let g : Fin n → Nat := fun i => (x i).mark.toNat
    let f : Fin n → Nat := fun i => (step x e i).mark.toNat
    have hpt : (fun i => f i + (if i=e then 1 else 0) + (if i=r then g r else 0)) =
        (fun i => g i + (if i=r then 1 else 0)) := by
      funext i
      dsimp only [f,g]
      rw [covered_step_mark hn x hm]
      change ((if geometricPay (x e) (x r) then
         if i=e then false else if i=r then true else (x i).mark else (x i).mark).toNat +
           (if i=e then 1 else 0)) + (if i=r then (x r).mark.toNat else 0) =
           (x i).mark.toNat + (if i=r then 1 else 0)
      by_cases he : i=e
      · subst i
        simp [hp,Ne.symm (no_self hn e),he0,r]
      · by_cases hr : i=r
        · subst i
          simp [hp,he,Nat.add_comm]
        · simp [hp,he,hr]
    have hsum := congrArg sumEdge hpt
    rw [sAdd,sAdd,sAdd,sSelector,sSelector,sSelector] at hsum
    change sumEdge f + 1 + g r = sumEdge g + 1 at hsum
    change sumEdge f + (geometricPay (x e) (x r) && (x r).mark).toNat = sumEdge g
    simp only [hp,Bool.true_and]
    change sumEdge f + g r = sumEdge g
    omega
  · have he : (fun i => (step x e i).mark.toNat) = fun i => (x i).mark.toNat := by
      funext i
      rw [covered_step_mark hn x hm]
      have hf : geometricPay (x e) (x (rightNeighbor e)) = false := Bool.eq_false_iff.mpr hp
      simp [hf]
    have hf : geometricPay (x e) (x (rightNeighbor e)) = false := Bool.eq_false_iff.mpr hp
    simp [rank,retirement,he,hf]

theorem rank_step_le {p c n : Nat} (hn : 4 ≤ n) (x : Config p c n) (e : Fin n)
    (hm : MCOV x) : rank (step x e) ≤ rank x := by
  have h := rank_step hn x e hm
  omega

theorem retirement_iff_rank_drop {p c n : Nat} (hn : 4 ≤ n) (x : Config p c n) (e : Fin n)
    (hm : MCOV x) :
    retirement x e = true ↔ rank (step x e) < rank x := by
  have h := rank_step hn x e hm
  cases hret : retirement x e <;> simp [hret] at h ⊢ <;> omega

/-- The operational restart class is already forward closed. Apply the
literal fresh-mask step with no inherited tags, not a new entrance proof. -/
theorem quiet_step {p c n : Nat} (x : Config p c n) (e : Fin n)
    (hp : 2 ≤ p) (hc : 12 ≤ c) (hn : 4 ≤ n) (hnd : ¬ p ∣ n)
    (hx : QuietEntrance x) : QuietEntrance (step x e) := by
  have hcover := EntranceCover.cover_closed hn x e ⟨hx.1,hx.2.1⟩
  refine ⟨hcover.1,hcover.2,covered_mark_exists_of_not_dvd _ e hcover.1 hnd,?_⟩
  have hf : freshAt x (fun _ => False) := fun b h _ => hx.2.2.2 b h
  have hnew := freshMaskStep_literal x (fun _ => False) e hp hc hn hnd hx.1 hx.2.1
    (fun _ h => h.elim) hf
  exact fun b hb => hnew b hb (fun ⟨_,h,_⟩ => h)

theorem quiet_run {p c n : Nat} (x : Config p c n) (w : List (Fin n))
    (hp : 2 ≤ p) (hc : 12 ≤ c) (hn : 4 ≤ n) (hnd : ¬ p ∣ n)
    (hx : QuietEntrance x) : QuietEntrance (run x w) := by
  induction w generalizing x with
  | nil => exact hx
  | cons e w ih => exact ih (step x e) (quiet_step x e hp hc hn hnd hx)

/-- Literal uniform first-retirement endpoint, independent of initial
rank except for requiring two roots. -/
def ConcreteBoundedRank : Prop :=
  ∀ c : Nat, 12 ≤ c → ∃ A : Nat, ∀ {p n : Nat} (x : Config p c n),
    2 ≤ p → 4 ≤ n → (¬ p ∣ n) → QuietEntrance x → 2 ≤ rank x →
      IIDExpectedHittingTimeAtMost step (fun y => rank y < rank x) x (A*n^2)

end L4.RankPhysical

#print axioms L4.RankPhysical.rank_step
#print axioms L4.RankPhysical.rank_step_le
#print axioms L4.RankPhysical.retirement_iff_rank_drop
#print axioms L4.RankPhysical.quiet_step
#print axioms L4.RankPhysical.quiet_run
