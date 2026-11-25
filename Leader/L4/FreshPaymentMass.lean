import Leader.L4.FreshPaySweep
import Leader.L4.RankRace

namespace L4.FreshPaymentMass
open RankSupplier RankRenewal RankRace TaggedTail FreshPaySweep

abbrev Worker (p c n : Nat) := Obs p c n × Nat

/-- One predictable nominated bond. Padding continues to nominate even
when the actual epoch has ended; the unpaid test can never credit that. -/
def nominate {p c n : Nat} (v : Fin n) (a : Worker p c n) : Fin n :=
  liftedSite v a.2

def step {p c n : Nat} (v : Fin n) (a : Worker p c n) (e : Fin n) : Worker p c n :=
  (advance v a.1 e, if e = nominate v a then a.2+1 else a.2)

private theorem sum_mono {n : Nat} (f g : Fin n → Nat) (h : ∀ e, f e≤g e) :
    sumEdge f≤sumEdge g := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    simp only [sumEdge,List.ofFn_succ,List.sum_cons]
    exact Nat.add_le_add (h 0) (ih _ _ (fun e => h e.succ))

private theorem still_live {p c n : Nat} (hn : 4≤n) (v e : Fin n) (s : Obs p c n)
    (h : Live v s ∨ s.stopped=true) :
    Live v (advance v s e) ∨ (advance v s e).stopped=true := by
  by_cases ht : (advance v s e).stopped=true
  · exact Or.inr ht
  have hs : Live v s := h.resolve_right (fun hh => ht (by simp [advance,hh]))
  exact Or.inl (live_step hn v e s hs (Bool.eq_false_iff.mpr ht))

private theorem ready_step {p c n : Nat} (hn : 4≤n) (v : Fin n) (a : Worker p c n)
    (d : Nat) (e : Fin n) (hd : d≤a.1.donor)
    (hs : Live v a.1 ∨ a.1.stopped=true) (h : ready v a.1 d a.2) :
    ready v (step v a e).1 d (step v a e).2 := by
  by_cases he : e = nominate v a
  · have hE : e = liftedSite v a.2 := he
    rw [hE] at *
    simpa [step,nominate] using ready_nomination hn v a.1 d a.2 hd hs h
  · simpa [step,he] using ready_wait hn v a.1 d a.2 hd e hs h

/-- The observed target neither stopped nor paid, on the strictly
surviving prefix. This is a raw word count, not a conditional law given
survival or a policy that selects future progress. -/
def unpaidIndicator {p c n : Nat} (d : Nat) (s : Obs p c n) : Nat :=
  if s.stopped=false ∧ s.donor=d then 1 else 0

theorem unpaid_le_abstract {p c n : Nat} (hn : 4≤n) (v : Fin n)
    (s : Obs p c n) (hs : Live v s) (t : Nat) :
    endpointSum (advance v) (unpaidIndicator s.donor) t s ≤
      slowMass (step v) (nominate v) (s,0) t (s.donor+1) := by
  let d := s.donor
  let f := unpaidIndicator (p:=p) (c:=c) (n:=n) d
  let g := fun y : Worker p c n × Nat × Nat => if y.2.1≤d+1 then 1 else 0
  have main (t : Nat) (a : Worker p c n) (hits misses : Nat)
      (hc : a.2=hits) (hd : d≤a.1.donor)
      (hl : Live v a.1 ∨ a.1.stopped=true) (hr : ready v a.1 d a.2) :
      endpointSum (advance v) f t a.1 ≤
        endpointSum (countStep (step v) (fun x => some (nominate v x))) g t (a,hits,misses) := by
    induction t generalizing a hits misses with
    | zero =>
      change f a.1≤g (a,hits,misses)
      unfold f unpaidIndicator
      by_cases e : a.1.stopped=false ∧ a.1.donor=d
      · rw [if_pos e]
        have hbound : hits≤d+1 := by
          rcases hr with x|x|⟨x,_⟩
          · exact False.elim (Bool.noConfusion (x.symm.trans e.1))
          · omega
          · omega
        simp [g,hbound]
      · rw [if_neg e]
        exact Nat.zero_le _
    | succ t ih =>
      change sumEdge (fun e => endpointSum (advance v) f t (advance v a.1 e)) ≤
        sumEdge (fun e => endpointSum (countStep (step v) (fun x => some (nominate v x)))
          g t (countStep (step v) (fun x => some (nominate v x)) (a,hits,misses) e))
      apply sum_mono
      intro e
      let b := step v a e
      have hD : d≤b.1.donor := Nat.le_trans hd (donor_mono_step v e a.1)
      have hL := still_live hn v e a.1 hl
      have hR := ready_step hn v a d e hd hl hr
      by_cases he : e = nominate v a
      · have hh : some (nominate v a) = some e := congrArg some he.symm
        rw [countStep, if_pos hh]
        exact ih b (hits+1) misses (by simp [b,step,he,hc]) hD hL hR
      · have hh : ¬ some (nominate v a) = some e := fun h => he (Option.some.inj h).symm
        rw [countStep, if_neg hh]
        exact ih b hits (misses+1) (by simp [b,step,he,hc]) hD hL hR
  exact main t (s,0) 0 0 rfl (Nat.le_refl _) (Or.inl hs)
    (Or.inr (Or.inr ⟨Nat.zero_le _,Or.inl rfl⟩))

theorem unpaid_gap_tail {p c n : Nat} (hn : 4≤n) (hc : 12≤c)
    (v : Fin n) (s : Obs p c n) (hs : Live v s) :
    let h := s.donor+1
    let t := 2*n*(c*h)
    2048^h * endpointSum (advance v) (unpaidIndicator s.donor) t s ≤ n^t := by
  let h := s.donor+1
  let t := 2*n*(c*h)
  have hcount := unpaid_le_abstract hn v s hs t
  have hSlow := sharp_slow_gap_tail (step v) (nominate v) (s,0) c h (by omega) hc
  exact Nat.le_trans (Nat.mul_le_mul_left _ hcount) hSlow

end L4.FreshPaymentMass

#print axioms L4.FreshPaymentMass.unpaid_le_abstract
#print axioms L4.FreshPaymentMass.unpaid_gap_tail
