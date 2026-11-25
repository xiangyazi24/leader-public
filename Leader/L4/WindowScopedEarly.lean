import Leader.L4.WindowScopedRoute
import Leader.L4.FreshFailure

namespace L4.WindowScopedEarly
open RankSupplier SevenTagCharge WindowScopedSupplier WindowScopedRoute FreshEpochEarly

/-- A finite raw ledger prefix ending at its tagged birth, at one fixed
unpaid gap. Keep includes exterior retirements; the following donor
counter is local and is not reset by them. -/
inductive BirthPrefix {p c n : Nat} (v : Fin n) (d : Nat)
    (group cert : List (Fin n)) (a : Fin n) :
    Ledger p c n → List (Fin n) → Prop where
  | terminal {z e site} :
      WindowLocal.route group cert (some a) z e = .targetBirth a site →
      BirthPrefix v d group cert a z [e]
  | keep {z e w} :
      WindowLocal.route group cert (some a) z e = .keep →
      (follow v d z.config e).donor=d →
      BirthPrefix v d group cert a (SevenTagCharge.advance z e) w →
      BirthPrefix v d group cert a z (e::w)

private theorem routed_birth {p c n : Nat} (group cert : List (Fin n))
    (z : Ledger p c n) (a e site : Fin n)
    (h : WindowLocal.route group cert (some a) z e = .targetBirth a site) :
    z.slots e=some a ∧ WindowLocal.birthAt z.config e=true := by
  unfold WindowLocal.route at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i b hb
      unfold WindowLocal.routeKnown at h
      split at h
      · cases h
      · split at h
        · rename_i hyes
          have H := Bool.and_eq_true_iff.mp hyes
          have hab := Option.some.inj (beq_iff_eq.mp H.1)
          subst b
          exact ⟨hb,H.2⟩
        · cases h

theorem valid_birth_prefix {p c n d : Nat} {z0 : Config p c n} (hn : 4≤n)
    (v : Fin n) (group cert : List (Fin n)) (a : Fin n) (ha : a∈group)
    (z : Ledger p c n) (w : List (Fin n)) (hz : Valid z z0)
    (h : Protected v (init z.config d)) (hs : z.slots (liftedSite v d)=some a)
    (hw : BirthPrefix v d group cert a z w) :
    FreshCountHits.ValidCountWord z.config v d w ∧
      (run z.config w (liftedSite v (d+1))).leader=true := by
  induction hw with
  | @terminal z e site hb =>
    obtain ⟨ht,hb'⟩ := routed_birth group cert z a e site hb
    have he := hz.unique e (liftedSite v d) a ht hs
    have hc := (WindowLocal.target_birth_at_same_slot hn z e a hz.markCover hz.sourceCover ht hb').2.1
    have hf : geometricPay (z.config e) (z.config (rightNeighbor e))=false := by
      apply Bool.eq_false_iff.mpr
      intro hp
      have hh := (covered_step_mark hn z.config hz.markCover e e)
      rw [if_pos hp] at hh
      have hm := (EntranceCover.cover_closed hn z.config e ⟨hz.markCover,hz.sourceCover⟩).1 e (.inl hc)
      simp only [if_true] at hh
      rw [hm] at hh
      cases hh
    refine ⟨⟨hz.markCover,hz.sourceCover,h.2,(fun _ => hf),trivial⟩,?_⟩
    change (step z.config e (liftedSite v (d+1))).leader=true
    rwa [liftedSite_succ,←he]
  | @keep z e w hr hd ht ih =>
    obtain ⟨_,hp,hs'⟩ := follow_of_keep hn v group cert z e a h hz ha hs hr
    have hEq : follow v d z.config e=init (step z.config e) d := by
      change init (step z.config e) (follow v d z.config e).donor=_
      rw [hd]
    rw [hEq] at hp hs'
    have hs'' : (SevenTagCharge.advance z e).slots (liftedSite v d)=some a := hs'
    have hp' : Protected v (init (SevenTagCharge.advance z e).config d) := hp
    obtain ⟨hvalid,hborn⟩ := ih (valid_step hn z z0 e hz) hp' hs''
    have hUnpaid (he : e=liftedSite v d) :
        geometricPay (z.config e) (z.config (rightNeighbor e))=false := by
      apply Bool.eq_false_iff.mpr
      intro hh
      have hx : (follow v d z.config e).donor=d+1 := by subst e; simp [follow,init,hh]
      omega
    exact ⟨⟨hz.markCover,hz.sourceCover,h.2,hUnpaid,hvalid⟩,hborn⟩

#print axioms valid_birth_prefix

private theorem born_sticky {p c n : Nat} (v : Fin n) (d : Nat) (w : List (Fin n)) :
    GGTiming.runMarks (FreshFailure.earlyNext (p:=p) (c:=c) v d) .born w = .born := by
  induction w with
  | nil => rfl
  | cons e w ih => exact ih

private theorem valid_birth_to_score {p c n : Nat} (x : Config p c n) (v : Fin n)
    (d : Nat) (w tail : List (Fin n))
    (hw : FreshCountHits.ValidCountWord x v d w)
    (hb : (run x w (liftedSite v (d+1))).leader=true) :
    GGTiming.runMarks (FreshFailure.earlyNext v d) (FreshFailure.earlyStart v d x) (w++tail) =
      FreshFailure.EarlyState.born := by
  induction w generalizing x with
  | nil =>
    rw [List.nil_append]
    change (x (liftedSite v (d+1))).leader=true at hb
    simp only [FreshFailure.earlyStart,hb,if_true]
    exact born_sticky v d tail
  | cons e w ih =>
    by_cases he : (x (liftedSite v (d+1))).leader=true
    · simp only [FreshFailure.earlyStart,he,if_true]
      exact born_sticky _ _ _
    · have hF := Bool.eq_false_iff.mpr he
      have hm : readyMark x v e d := ⟨hw.1,hw.2.1,hw.2.2.1,hw.2.2.2.1⟩
      simp only [FreshFailure.earlyStart,hF,Bool.false_eq_true,if_false,List.cons_append,GGTiming.runMarks,
        FreshFailure.earlyNext,if_pos hm]
      exact ih _ hw.2.2.2.2 hb

/-- Common raw words, arbitrary outer observer: at the inclusive
cutoff the numerator of a birth attributed to this fresh gap has the
early bound. A post-birth suffix is padding and remains free. -/
theorem early_deadline_of_birthPrefix {α : Type} {p c n d : Nat} {z0 : Config p c n}
    (hn : 4≤n) (hc : 12≤c) (v : Fin n) (group cert : List (Fin n)) (a : Fin n) (ha : a∈group)
    (z : Ledger p c n) (hz : Valid z z0) (h : Protected v (init z.config d))
    (hs : z.slots (liftedSite v d)=some a) (hFresh : freshInit z.config v d)
    (outer : α→Fin n→α) (score : α→Nat) (start : α) (hone : ∀ y, score y≤1)
    (t : Nat) (ht : t≤2*n*(c*(d+1)))
    (hscore : ∀ w, w.length=t → 0<score (GGTiming.runMarks outer start w) →
      ∃ pre tail, w=pre++tail ∧ BirthPrefix v d group cert a z pre) :
    256^(d+1)*RankRenewal.endpointSum outer score t start≤n^t := by
  have hm := FreshFailure.endpoint_le_words outer (FreshFailure.earlyNext v d)
    score FreshFailure.earlyScore t start (FreshFailure.earlyStart v d z.config) (by
      intro w hw
      by_cases hb : 0<score (GGTiming.runMarks outer start w)
      · obtain ⟨pre,tail,hEq,hBirth⟩ := hscore w hw hb
        obtain ⟨hV,hB⟩ := valid_birth_prefix hn v group cert a ha z pre hz h hs hBirth
        have H := valid_birth_to_score z.config v d pre tail hV hB
        rw [hEq] at *
        rw [H]
        exact hone _
      · exact Nat.le_trans (by omega : score (GGTiming.runMarks outer start w) ≤ 0) (Nat.zero_le _))
  rw [FreshFailure.early_mass_exact] at hm
  exact Nat.le_trans (Nat.mul_le_mul_left _ hm)
    (early_of_freshInit hn hc v h.2.gap t ht z.config hFresh)

/-- A surviving motion on a kept mark starts a new authenticated
epoch at exactly the next gap. Unrelated events at other marks do not
reset such an epoch. -/
theorem paid_fresh_of_keep {p c n d : Nat} {z0 : Config p c n} (hn : 4≤n)
    (v : Fin n) (group cert : List (Fin n)) (z : Ledger p c n) (e a : Fin n)
    (hz : Valid z z0) (h : Protected v (init z.config d))
    (ha : a∈group) (hs : z.slots (liftedSite v d)=some a)
    (hkeep : WindowLocal.route group cert (some a) z e = .keep)
    (hmove : d < (follow v d z.config e).donor) :
    let t := follow v d z.config e
    t.donor=d+1 ∧ Protected v t ∧ freshInit t.config v t.donor := by
  let t := follow v d z.config e
  let pay := geometricPay (z.config e) (z.config (rightNeighbor e))
  obtain ⟨hret,hprot,_⟩ := follow_of_keep hn v group cert z e a h hz ha hs hkeep
  have hflag : ((e == liftedSite v d) && pay)=true := by
    cases hB : ((e == liftedSite v d) && pay)
    · have hD : t.donor=d := by simp [t,follow,init,←show pay=geometricPay _ _ from rfl,hB]
      change d<t.donor at hmove
      omega
    · rfl
  obtain ⟨he,hpay⟩ := Bool.and_eq_true_iff.mp hflag
  have he := beq_iff_eq.mp he
  have hD : t.donor=d+1 := by simp [t,follow,init,←show pay=geometricPay _ _ from rfl,hflag]
  have hb := FreshTimerEpoch.paid_landing_off hn z.config e hz.markCover hz.sourceCover hpay (hret he)
  have ht : liftedSite v (t.donor+1)=rightNeighbor (rightNeighbor e) := by
    rw [hD,liftedSite_succ,liftedSite_succ,←he]
  exact ⟨hD,hprot,hprot.2.ghost,Or.inl (ht.symm ▸ hb.1)⟩

/-- Track the selected gap on the same raw word, with the usual
first-decision hold of the gap (the physical route is not held).
This function is used only to count gaps before terminal routing. -/
def trackGap {p c n : Nat} (v : Fin n) (group cert : List (Fin n)) (a : Fin n)
    (q : Ledger p c n × Nat × Bool) (e : Fin n) : Ledger p c n × Nat × Bool :=
  let next := SevenTagCharge.advance q.1 e
  if q.2.2 || decide (WindowLocal.route group cert (some a) q.1 e ≠ .keep) then
    (next,q.2.1,true)
  else
    (next,(follow v q.2.1 q.1.config e).donor,false)

theorem gap_nondecreasing {p c n : Nat} (v : Fin n) (group cert : List (Fin n))
    (a : Fin n) (q : Ledger p c n × Nat × Bool) (w : List (Fin n)) :
    q.2.1 ≤ (w.foldl (trackGap v group cert a) q).2.1 := by
  induction w generalizing q with
  | nil => exact Nat.le_refl _
  | cons e w ih =>
    apply Nat.le_trans _ (ih (trackGap v group cert a q e))
    unfold trackGap
    split
    · exact Nat.le_refl _
    · exact Nat.le_add_right _ _

theorem no_reentry_of_strict_exit {p c n : Nat} (v : Fin n) (group cert : List (Fin n))
    (a : Fin n) (q : Ledger p c n × Nat × Bool) (w w' : List (Fin n)) (d : Nat)
    (h : d < (w.foldl (trackGap v group cert a) q).2.1) :
    d < ((w++w').foldl (trackGap v group cert a) q).2.1 := by
  rw [List.foldl_append]
  exact Nat.lt_of_lt_of_le h (gap_nondecreasing v group cert a _ w')

#print axioms no_reentry_of_strict_exit
#print axioms paid_fresh_of_keep
#print axioms early_deadline_of_birthPrefix
end L4.WindowScopedEarly
