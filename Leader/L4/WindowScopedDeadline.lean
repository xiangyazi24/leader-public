import Leader.L4.WindowScopedWait
import Leader.L4.RankRace

namespace L4.WindowScopedDeadline
open RankSupplier WindowScopedWait RankRace RankRenewal

def nominate {p c n : Nat} (v : Fin n) (s : Obs p c n × Nat) : Fin n :=
  liftedSite v s.2

private theorem raw_count {p c n : Nat} (v : Fin n) (d : Nat)
    (w : List (Fin n)) (s : Obs p c n × Nat) (b m : Nat)
    (hb : s.2 = min b (d+1)) :
    let z := GGTiming.runMarks (countStep (rawWatch v d) (fun a => some (nominate v a)))
      (s,b,m) w
    z.1 = w.foldl (rawWatch v d) s ∧ z.1.2 = min z.2.1 (d+1) := by
  induction w generalizing s b m with
  | nil => exact ⟨rfl,hb⟩
  | cons e w ih =>
    by_cases he : e=nominate v s
    · have hh : some (nominate v s) = some e := congrArg some he.symm
      simp only [GGTiming.runMarks,countStep,if_pos hh,List.foldl_cons]
      apply ih
      change (if s.2≤d ∧ e=liftedSite v s.2 then s.2+1 else s.2) = _
      rw [he]
      unfold nominate
      by_cases h : b≤d
      · have hs : s.2=b := hb.trans (Nat.min_eq_left (by omega))
        rw [hs,if_pos ⟨h,rfl⟩,Nat.min_eq_left (by omega)]
      · have hs : s.2=d+1 := hb.trans (Nat.min_eq_right (by omega))
        rw [if_neg (fun H => by omega),hs,Nat.min_eq_right (by omega)]
    · have hh : ¬ some (nominate v s) = some e := fun h => he (Option.some.inj h).symm
      simp only [GGTiming.runMarks,countStep,if_neg hh,List.foldl_cons]
      apply ih
      change (if s.2≤d ∧ e=liftedSite v s.2 then s.2+1 else s.2) = _
      rw [if_neg (fun h => he h.2)]
      exact hb

/-- A raw-word numerator bound for any actual outer observer. A scored
word must have retained the source/target corridor throughout and still
be unpaid, checked on the same physical word. No IID conditioning on
retention is used. -/
theorem unpaid_deadline {α : Type} {p c n : Nat} (hn : 4≤n) (hc : 12≤c)
    (v : Fin n) (d : Nat) (x : Config p c n) (hx : Live v (init x d))
    (outer : α → Fin n → α) (score : α → Nat) (a : α)
    (hone : ∀ y, score y≤1)
    (refineScore : ∀ w, 0 < score (GGTiming.runMarks outer a w) →
      RetainedWord v (init x d) w ∧
      (w.foldl (rawWatch v d) (init x d,0)).1.donor=d) :
    let h := d+1
    let t := 2*n*(c*h)
    2048^h * endpointSum outer score t a ≤ n^t := by
  let s := (init x d,0)
  let h := d+1
  let t := 2*n*(c*h)
  have cmp : endpointSum outer score t a ≤ slowMass (rawWatch v d) (nominate v) s t h := by
    unfold slowMass
    apply endpointSum_le_of_common_words
    intro w
    let z := GGTiming.runMarks (countStep (rawWatch v d) (fun a => some (nominate v a)))
      (s,0,0) w
    change score (GGTiming.runMarks outer a w) ≤ (if z.2.1≤h then 1 else 0)
    by_cases hp : 0 < score (GGTiming.runMarks outer a w)
    · obtain ⟨hw,hd⟩ := refineScore w hp
      have H := raw_count v d w s 0 0 rfl
      have hlt : z.2.1 < d+1 := by
        apply Nat.lt_of_not_ge
        intro hh
        have he : z.1.2=d+1 := H.2.trans (Nat.min_eq_right hh)
        have hCount (u : Obs p c n × Nat) :
            (w.foldl (rawWatch v d) u).2=w.foldl (tickCount v d) u.2 := by
          clear hp hw hd H he hh
          induction w generalizing u with
          | nil => rfl
          | cons e w ih => exact ih (rawWatch v d u e)
        have hout := rawWatch_complete hn v d x w hw hx (by
          rw [←hCount s,←H.1]
          exact he)
        omega
      simpa [if_pos (show z.2.1 ≤ h from Nat.le_of_lt hlt)] using
        hone (GGTiming.runMarks outer a w)
    · have hz : score (GGTiming.runMarks outer a w)=0 := by omega
      rw [hz]
      exact Nat.zero_le _
  exact Nat.le_trans (Nat.mul_le_mul_left _ cmp)
    (sharp_slow_gap_tail (rawWatch v d) (nominate v) s c h (by omega) hc)

#print axioms unpaid_deadline
end L4.WindowScopedDeadline
