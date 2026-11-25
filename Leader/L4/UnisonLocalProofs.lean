import Leader.L4.UnisonRows

namespace L4.UnisonLocalProofs
open UnisonRows

def AtQuiet (P : Int) (l x r : Clock) : Prop :=
  root P l x r=true → base P x=true

private theorem noReset (P : Int) (l x r : Clock) (h : AtQuiet P l x r) :
    (root P l x r && !base P x)=false := by
  apply Bool.eq_false_iff.mpr
  intro hh
  have hf := Bool.and_eq_true_iff.mp hh
  have ht := h hf.1
  simp [ht] at hf

theorem error_descent (P : Int) (l x r : Clock) (hQ : AtQuiet P l x r)
    (he : x.err=true) (hV : -P<x.value) :
    ∃ u, (u=l ∨ u=r) ∧ u.err=true ∧ u.value<x.value := by
  have hb : base P x=false := by
    unfold base
    have ht : x.value ≠ -P := by omega
    simp [ht]
  have hr : root P l x r = false := Bool.eq_false_iff.mpr (fun hh => by rw [hQ hh] at hb; cases hb)
  have hh : (lowerError x l || lowerError x r) = true := by
    cases hL : lowerError x l <;> cases hR : lowerError x r <;> simp_all [root]
  rcases Bool.or_eq_true_iff.mp hh with h|h
  · have hf := Bool.and_eq_true_iff.mp h
    exact ⟨l,.inl rfl,hf.1,of_decide_eq_true hf.2⟩
  · have hf := Bool.and_eq_true_iff.mp h
    exact ⟨r,.inr rfl,hf.1,of_decide_eq_true hf.2⟩

theorem error_poll (P : Int) (l x r : Clock) (hQ : AtQuiet P l x r)
    (he : (poll P l x r).err=true) :
    (x.err=true ∧ (poll P l x r).value=x.value) ∨
      ∃ u, (u=l ∨ u=r) ∧ u.err=true ∧
        (poll P l x r).value=u.value+1 ∧ (poll P l x r).value<x.value := by
  generalize hP : poll P l x r = z at he ⊢
  have facts := hP ▸ poll_facts P l x r
  cases facts with
  | reset hRoot hBase =>
    rw [hQ hRoot] at hBase
    cases hBase
  | propagate v hl _ hw =>
    obtain ⟨u,hu,hE,hV⟩ := hw
    exact .inr ⟨u,hu,hE,hV,hl⟩
  | clear _ _ _ => cases he
  | inc _ _ _ => cases he
  | hold => exact .inl ⟨he,rfl⟩

theorem propagate_gap (P : Int) (l x r u : Clock) (hu : u=l ∨ u=r)
    (hQ : AtQuiet P l x r) (he : u.err=true) (hNeg : u.value+1<0)
    (hGap : u.value+1<x.value) :
    (poll P l x r).value≤u.value+1 := by
  have hU : suggestion x u=u.value+1 := by
    simp only [suggestion,he,decide_eq_true hNeg,Bool.true_and,if_true]
    omega
  have hP : propValue l x r≤u.value+1 := by
    unfold propValue
    rcases hu with rfl | rfl
    · exact Int.le_trans (Int.min_le_left ..) (by rw [hU]; exact Int.le_refl _)
    · exact Int.le_trans (Int.min_le_right ..) (by rw [hU]; exact Int.le_refl _)
  have h : propValue l x r<x.value := by omega
  unfold poll signedRow
  rw [if_neg (by simp [noReset P l x r hQ]),if_pos h]
  exact hP

theorem correct_low_neighbor (P : Int) (l x r u : Clock) (hu : u=l ∨ u=r)
    (hQ : AtQuiet P l x r) (he : x.err=false) (hNeg : u.value<0) :
    u.value≤x.value+1 := by
  by_cases h : u.value≤x.value+1
  · exact h
  · have hlt : x.value+2≤u.value := by omega
    have hf : lowerGap P x.value u.value = true := by
      unfold lowerGap
      exact decide_eq_true ⟨hlt,by omega⟩
    have hR : root P l x r=true := by
      rcases hu with rfl|rfl <;> simp [root,he,hf]
    have hb := hQ hR
    simp [base,he] at hb

theorem clear_at_max (P : Int) (l x r : Clock) (hQ : AtQuiet P l x r)
    (he : x.err=true)
    (hWithin : ∀ u, (u=l ∨ u=r) → u.value≤x.value+1 ∧ x.value≤u.value+1)
    (hMax : ∀ u, (u=l ∨ u=r) → u.err=true → u.value≤x.value) :
    (poll P l x r).err=false := by
  have suggestion0 (u : Clock) (hu : u=l ∨ u=r) : suggestion x u=x.value := by
    unfold suggestion
    split
    · have hh := (hWithin u hu).2
      omega
    · rfl
  have p : propValue l x r=x.value := by
    simp [propValue,suggestion0 l (.inl rfl),suggestion0 r (.inr rfl)]
  have clears (u : Clock) (hu : u=l ∨ u=r) : clearOK x u=true := by
    obtain ⟨a,b⟩ := hWithin u hu
    unfold clearOK near
    apply Bool.and_eq_true_iff.mpr
    refine ⟨decide_eq_true ⟨b,a⟩,?_⟩
    cases h : u.err
    · simp
    · simp [show u.value≤x.value from hMax u hu h]
  simp [poll,signedRow,noReset P l x r hQ,p,he,clears l (.inl rfl),clears r (.inr rfl)]

theorem adjacent_of_no_lower (P a b : Int) (ha : a<P) (hb : b<P)
    (hA : lowerGap P a b=false) (hB : lowerGap P b a=false) : Adjacent P a b := by
  by_cases hEq : a=b
  · exact .inl hEq
  have aF : ¬(a+2≤b ∧ ¬(a=0 ∧ b=P-1)) := of_decide_eq_false hA
  have bF : ¬(b+2≤a ∧ ¬(b=0 ∧ a=P-1)) := of_decide_eq_false hB
  by_cases h : a<b
  · by_cases d : b=a+1
    · exact .inr (.inl (by simp [succ,d,show a≠P-1 by omega]))
    · have w : a=0 ∧ b=P-1 := by omega
      exact .inr (.inr (by simp [succ,w]))
  · by_cases d : a=b+1
    · exact .inr (.inr (by simp [succ,d,show b≠P-1 by omega]))
    · have w : b=0 ∧ a=P-1 := by omega
      exact .inr (.inl (by simp [succ,w]))

end L4.UnisonLocalProofs
