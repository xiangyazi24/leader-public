import Leader.L4.Height.StrictPublication
import Leader.L4.Height.Trial

namespace L4.PhysicalStrictServiceTail
open AllSizeProtocol PhysicalCustody BStarTrace BStarAcquireAnchors BStarH6WordChart
open BStarGrantWriterHistory Height Height.ProductionCustody
open Classical

private abbrev hp : 0 < 2 := by decide

private theorem wait_le {s n : Nat} (x : Raw s n) (i : Fin n) (w : List (Fin n)) :
    RawServiceCore.strictWait x i w ≤ w.length := by
  induction w generalizing x with
  | nil => exact Nat.le_refl 0
  | cons e w ih =>
    rw [RawServiceCore.strictWait]
    split
    · simp
    · have E := ih (rawNext s x e)
      simp only [List.length_cons]; omega

/-- The uniform service moment, without redundant censoring and the exact
original tape followed by the supplied actual raw prefix. -/
theorem actual_prefix_moment {s n : Nat}
    (hn : 4≤n) (hs : 6≤s) (hadvice : s=ell (ell n))
    (space : 3*1024*radWidth s<n) {x : Raw s n}
    (g : CustodyWitness x) (a : List (Fin n))
    (i : Header (oldH6 (rows s) g.base)) (t : Nat) :
    let y := rawRun g.initial (((g.u++g.v)++g.past)++a)
    wordSum (fun w=>2^(RawServiceCore.strictWait y i.val w /
      (2^(5*longBudget+34)*n*radWidth s))) t ≤ 2*n^t := by
  have H := strict_publication_moment hn hs hadvice space (ProductionCustody.extend g a) i t
  have le (w : List (Fin n)) (len : w.length=t) :
      min (RawServiceCore.strictWait (rawRun x a) i.val w) t =
        RawServiceCore.strictWait (rawRun x a) i.val w := by
    exact Nat.min_eq_left (len ▸ wait_le _ _ _)
  dsimp only
  rw [show rawRun g.initial (((g.u++g.v)++g.past)++a)=rawRun (rawRun g.initial ((g.u++g.v)++g.past)) a from
    BStarResetSchedule.run_append (rawNext s) _ _ _,g.here]
  refine Nat.le_trans (wordSum_mono_on_length _ _ t ?_) H
  intro w len
  rw [le w len]
  exact Nat.le_refl _

private theorem wait_miss {s n : Nat} (x : Raw s n) (i : Fin n) (w : List (Fin n))
    (miss : ¬RawServiceCore.publishes x i w) :
    RawServiceCore.strictWait x i w=w.length := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih =>
    rw [RawServiceCore.strictWait,if_neg (fun H=>miss ((RawServiceCore.publishes_cons x i e w).2 (.inl H))),
      ih _ (fun H=>miss ((RawServiceCore.publishes_cons x i e w).2 (.inr H))),List.length_cons,Nat.one_add]

/-- A single owner misses the next actual publication by three service
scales on at most a quarter of the exact-length raw words. This is not
yet a simultaneous multi-level display bound. -/
theorem actual_prefix_next_quarter {s n : Nat}
    (hn : 4≤n) (hs : 6≤s) (hadvice : s=ell (ell n))
    (space : 3*1024*radWidth s<n) {x : Raw s n}
    (g : CustodyWitness x) (a : List (Fin n))
    (i : Header (oldH6 (rows s) g.base)) :
    let y := rawRun g.initial (((g.u++g.v)++g.past)++a)
    let L := 2^(5*longBudget+34)*n*radWidth s
    4*wordSum (fun w=>if ¬RawServiceCore.publishes y i.val w then 1 else 0) (3*L) ≤ n^(3*L) := by
  dsimp only
  let L := 2^(5*longBudget+34)*n*radWidth s
  let y := rawRun g.initial (((g.u++g.v)++g.past)++a)
  let f := fun w=>if ¬RawServiceCore.publishes y i.val w then 1 else 0
  have b := actual_prefix_moment hn hs hadvice space g a i (3*L)
  have pos : 0<L := Nat.mul_pos
    (Nat.mul_pos (Nat.two_pow_pos _) (by omega)) (radius_pos (production_of_space g hs hadvice space))
  have h : wordSum (fun w=>8*f w) (3*L) ≤
      wordSum (fun w=>2^(RawServiceCore.strictWait y i.val w/L)) (3*L) := by
    apply wordSum_mono_on_length
    intro w len
    by_cases miss : ¬RawServiceCore.publishes y i.val w
    · rw [wait_miss y i.val w miss,len,Nat.mul_div_cancel _ pos]
      simp [f,miss]
    · exact (show 8*f w=0 by rw [show f w=0 from if_neg miss]).symm ▸ Nat.zero_le _
  rw [wordSum_mul_left] at h
  change 4*wordSum f (3*L)≤n^(3*L)
  change wordSum (fun w=>2^(RawServiceCore.strictWait y i.val w/L)) (3*L)≤2*n^(3*L) at b
  omega

#print axioms actual_prefix_moment
#print axioms actual_prefix_next_quarter
end L4.PhysicalStrictServiceTail
