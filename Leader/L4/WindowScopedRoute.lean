import Leader.L4.WindowScopedDeadline

namespace L4.WindowScopedRoute
open RankSupplier RankPhysical SevenTagCharge WindowScopedSupplier

private theorem newGhost_after_pay {p c n d : Nat} (hn : 4≤n)
    (x : Config p c n) (v : Fin n)
    (h : Protected v (init x d))
    (pay : geometricPay (x (liftedSite v d)) (x (rightNeighbor (liftedSite v d)))=true)
    (hret : retirement x (liftedSite v d)=false) :
    (step x (liftedSite v d) (liftedSite v (d+2))).leader = false := by
  let e := liftedSite v d
  let r := rightNeighbor e
  let w := liftedSite v (d+2)
  have hS := (RankFresh.corridor_supplier_step hn x v e h.1.2.1 h.2).1
  have hNext := firstMark_after_local_step hn x v e h.1.2.1 h.2.first h.2.gap
    h.2.leader hS (fun _ => hret)
  have hcap : d+2<n := by simpa [e,init,pay] using hNext.2
  have hR : r = liftedSite v (d+1) := (liftedSite_succ v d).symm
  have he : w ≠ e := fun q => by
    have H := liftedSite_inj v hcap (show d<n by omega) q
    omega
  have hr : w ≠ r := fun q => by
    rw [hR] at q
    have H := liftedSite_inj v hcap (show d+1<n by omega) q
    omega
  have hM : (x r).mark = false := by
    change (geometricPay (x e) (x r) && (x r).mark)=false at hret
    simpa [pay,e,r] using hret
  have hW : (x w).leader = false := by
    apply Bool.eq_false_iff.mpr
    intro hw
    have hne : rightNeighbor r = w := by rw [hR,←liftedSite_succ]
    have H := h.1.2.1 r (.inl (hne.symm ▸ hw))
    change (x r).mark=true at H
    rw [hM] at H
    cases H
  change (step x e w).leader=false
  have hr' : w ≠ rightNeighbor e := hr
  simpa [step,he,hr'] using hW

/-- Tie the ledger's target identity and completed-pair routing to the
scoped supplier follow. This does not assume the old global stop bit
stays false. -/
theorem follow_of_keep {p c n d : Nat} {z0 : Config p c n} (hn : 4≤n)
    (v : Fin n) (group cert : List (Fin n)) (z : Ledger p c n) (e a : Fin n)
    (h : Protected v (init z.config d)) (hz : Valid z z0)
    (ha : a ∈ group) (hs : z.slots (liftedSite v d)=some a)
    (hkeep : WindowLocal.route group cert (some a) z e = .keep) :
    let t := follow v d z.config e
    (e=liftedSite v d → retirement z.config e=false) ∧
    Protected v t ∧ (SevenTagCharge.advance z e).slots (liftedSite v t.donor) = some a := by
  have hc := hz.sourceCover
  have hnoloss : WindowLocal.selectedGroupLoss group z e=none := by
    unfold WindowLocal.route at hkeep
    split at hkeep
    · rename_i b hb
      cases hkeep
    · assumption
  have hret (he : e=liftedSite v d) : retirement z.config e=false :=
    tracked_no_retirement_of_group_keep group z e a ha (he ▸ hs) hnoloss
  let t := follow v d z.config e
  refine ⟨hret,?_,?_⟩
  · by_cases he : e=liftedSite v d
    · subst e
      apply protected_follow hn z.config v _ h hc hret
      by_cases hp : geometricPay (z.config (liftedSite v d))
          (z.config (rightNeighbor (liftedSite v d)))=true
      · simpa [follow,init,hp] using newGhost_after_pay hn z.config v h hp (hret rfl)
      · have hf : geometricPay (z.config (liftedSite v d))
           (z.config (rightNeighbor (liftedSite v d)))=false := Bool.eq_false_iff.mpr hp
        have hdT : (follow v d z.config (liftedSite v d)).donor=d := by simp [follow,init,hf]
        rw [hdT]
        apply Bool.eq_false_iff.mpr
        intro hL
        have hb : WindowLocal.birthAt z.config (liftedSite v d)=true := by
          unfold WindowLocal.birthAt
          have hg : (z.config (liftedSite v (d+1))).leader=false := h.2.ghost
          rw [←liftedSite_succ,hg,hL]
          rfl
        have hh := (WindowLocal.target_birth_result hn group cert z (liftedSite v d) a
          h.1.2.1 hc hs hb).1
        rw [hh] at hkeep
        cases hkeep
    · exact (exterior_continues_protection hn z.config v e h hc he).2
  · by_cases he : e=liftedSite v d
    · subst e
      by_cases hp : geometricPay (z.config (liftedSite v d))
        (z.config (rightNeighbor (liftedSite v d)))=true
      · have hM : (z.config (rightNeighbor (liftedSite v d))).mark=false := by
          have H := hret rfl
          change (geometricPay _ _ && (z.config (rightNeighbor (liftedSite v d))).mark)=false at H
          simpa [hp] using H
        have hm0 : (z.slots (rightNeighbor (liftedSite v d))).isSome=false :=
          (hz.covers _).trans hM
        have hm : z.slots (rightNeighbor (liftedSite v d)) = none := by
          cases hh : z.slots (rightNeighbor (liftedSite v d)) <;> simp_all
        rw [show (follow v d z.config (liftedSite v d)).donor=d+1 by simp [follow,init,hp],
          liftedSite_succ]
        exact (by simpa [SevenTagCharge.advance,slotsStep,hp,hm,hs] using
          (paid_mover_or_resident hn z.slots (liftedSite v d)).2)
      · simp [follow,init,SevenTagCharge.advance,slotsStep,hp,hs]
    · have hb : (e == liftedSite v d)=false := Bool.eq_false_iff.mpr
          (fun h => he (beq_iff_eq.mp h))
      rw [show (follow v d z.config e).donor=d by simp [follow,init,hb]]
      by_cases hp : geometricPay (z.config e) (z.config (rightNeighbor e))=true
      · by_cases hr : liftedSite v d=rightNeighbor e
        · have hs' : z.slots (rightNeighbor e)=some a := hr ▸ hs
          change slotsStep z.config z.slots e (liftedSite v d)=some a
          rw [hr,show slotsStep z.config z.slots e = SevenTagCharge.move z.slots e by simp [slotsStep,hp],
            (paid_mover_or_resident hn z.slots e).2,hs']
          rfl
        · change slotsStep z.config z.slots e (liftedSite v d)=some a
          simp [slotsStep,hp,SevenTagCharge.move,Ne.symm he,hr,hs]
      · simp [SevenTagCharge.advance,slotsStep,hp,hs]

/-- Predicate on the actual raw ledger, independent of the supplier
counter. No exterior event is filtered out of its transition. -/
def allKeep {p c n : Nat} (group cert : List (Fin n)) (a : Fin n)
    (z : Ledger p c n) : List (Fin n) → Prop
  | [] => True
  | e::w => WindowLocal.route group cert (some a) z e = .keep ∧
      allKeep group cert a (SevenTagCharge.advance z e) w

theorem retained_of_allKeep {p c n d : Nat} {z0 : Config p c n} (hn : 4≤n)
    (v : Fin n) (group cert : List (Fin n)) (a : Fin n) (ha : a ∈ group)
    (z : Ledger p c n) (w : List (Fin n)) (hz : Valid z z0)
    (h : Protected v (init z.config d)) (hs : z.slots (liftedSite v d)=some a)
    (hw : allKeep group cert a z w) :
    WindowScopedWait.RetainedWord v (init z.config d) w := by
  induction w generalizing z d with
  | nil => exact .nil
  | cons e w ih =>
    obtain ⟨hr,hp,ht⟩ := follow_of_keep hn v group cert z e a h hz ha hs hw.1
    exact .cons hr hp.1 (ih _ (valid_step hn z z0 e hz) hp ht hw.2)

/-- Unpaid cutoff pushed back onto the actual local ledger route. The
outer event still needs to show it is scored only on the selected
epoch's uninterrupted unpaid prefix. -/
theorem unpaid_deadline_of_allKeep {α : Type} {p c n d : Nat} {z0 : Config p c n}
    (hn : 4≤n) (hc : 12≤c) (v : Fin n) (group cert : List (Fin n))
    (a : Fin n) (ha : a ∈ group) (z : Ledger p c n)
    (hz : Valid z z0) (h : Protected v (init z.config d))
    (hs : z.slots (liftedSite v d)=some a) (outer : α → Fin n → α)
    (score : α → Nat) (start : α) (hone : ∀ y, score y≤1)
    (hrefine : ∀ w, 0 < score (GGTiming.runMarks outer start w) →
      allKeep group cert a z w ∧
      (w.foldl (WindowScopedWait.rawWatch v d) (init z.config d,0)).1.donor=d) :
    let k := d+1
    let t := 2*n*(c*k)
    2048^k * RankRenewal.endpointSum outer score t start ≤ n^t := by
  apply WindowScopedDeadline.unpaid_deadline hn hc v d z.config h.1 outer score start hone
  intro w hw
  exact ⟨retained_of_allKeep hn v group cert a ha z w hz h hs (hrefine w hw).1,
    (hrefine w hw).2⟩

#print axioms follow_of_keep
#print axioms retained_of_allKeep
#print axioms unpaid_deadline_of_allKeep
end L4.WindowScopedRoute
