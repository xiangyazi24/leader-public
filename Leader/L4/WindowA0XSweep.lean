import Leader.L4.WindowFiveStages
import Leader.L4.WindowA0ClosedEntry
import Leader.L4.WindowA0Cleanup
import Leader.L4.WindowA0AttemptCredit

/-! Initial A0 X sweep. Its nominations ignore launches, including an
L1 on the last cleanup mark; the next phase still owes a fresh L1. -/
namespace L4.WindowA0XSweep
open WindowA0IH GGStage SevenTagCharge

private theorem leftPrefix {p c : Nat} (u v : Site p c) :
    (pairStep u v).1.mark=(stepPrefix u v).1.mark := by
  unfold pairStep finishBirth
  dsimp only
  split <;> rfl

private theorem rightPrefix {p c : Nat} (u v : Site p c)
    (h : (pairStep u v).2.leader=false) : (stepPrefix u v).2.leader=false := by
  unfold pairStep finishBirth at h
  dsimp only at h
  split at h
  · contradiction
  · exact h

private theorem notLoop {n : Nat} (hn : 4≤n) (e : Fin n) : rightNeighbor e≠e := by
  intro h
  have h' : liftedSite e 1=liftedSite e 0 := by simpa [liftedSite_succ,liftedSite_zero] using h
  have := liftedSite_inj e (by omega : 1<n) (by omega : 0<n) h'
  omega

private theorem old_noleader {p c n : Nat} {J : Fin n} {H : Nat} {z : Cut p c n}
    (h : Live J H z) (k : Nat) (hk : k<z.gap) :
    (z.config (liftedSite z.top k)).leader=false := by
  cases k with
  | zero => simpa only [liftedSite_zero] using h.topGhost
  | succ k =>
    apply Bool.eq_false_iff.mpr
    intro hp
    have hm := h.mc (liftedSite z.top k) (.inl (by rwa [←liftedSite_succ]))
    rw [h.openBonds k hk] at hm
    cases hm

private theorem old_nopay {p c n : Nat} (hn : 4≤n) {J : Fin n} {H : Nat}
    {z : Cut p c n} (h : Live J H z) (k : Nat) (hk : k<z.gap) :
    geometricPay (z.config (liftedSite z.top k))
      (z.config (rightNeighbor (liftedSite z.top k)))=false := by
  by_cases hki : k+1<z.gap
  · apply Bool.eq_false_iff.mpr
    intro hp
    have hm := RearTrace.paid_was_marked h.mc _ hp
    rw [h.openBonds k hki] at hm
    cases hm
  · have Heq : k+1=z.gap := by omega
    have hI : incoming z.top z.gap=liftedSite z.top k := by
      rw [←Heq,incoming_succ_lift]
    have H' := (WindowA0Drained.drained_step hn z.config z.top (liftedSite z.top k)
      h.gapPos h.markTop (by simpa [hI,show z.gap-1=k by omega] using h.markRight)
      h.empty (old_noleader h)).1
    simpa [moved,hI] using H'

/-- Every retained outgoing donor is a valid X-clearing nomination:
interior bonds are ordinary and OFF, and the final donor uses the
pinned door row even if the mark launches a worker. The retained
right endpoint ghost test is deliberately on the completed physical step. -/
theorem outgoing_break {p c n : Nat} (hn : 4≤n) {J : Fin n} {H : Nat}
    {z : Cut p c n} (h : Live J H z) (k : Nat) (hk : k<z.gap)
    (hRight : (step z.config (liftedSite z.top k)
      (rightNeighbor (liftedSite z.top k))).leader=false) :
    (step z.config (liftedSite z.top k) (liftedSite z.top k)).rail≠.x ∧
    (k+1<z.gap →
      (z.config (liftedSite z.top k)).rail≠.x →
      (z.config (liftedSite z.top (k+1))).rail≠.x →
      (step z.config (liftedSite z.top k) (liftedSite z.top (k+1))).rail≠.x) := by
  let e := liftedSite z.top k
  let u := z.config e
  let v := z.config (rightNeighbor e)
  have hn' := notLoop hn e
  have hp := old_nopay hn h k hk
  have hL : (stepPrefix u v).2.leader=false :=
    rightPrefix u v (by simpa [step,e,u,v,hn'] using hRight)
  have hm : (stepPrefix u v).1.mark=u.mark := by
    rw [←leftPrefix]
    have HH := covered_step_mark hn z.config h.mc e e
    simpa [step,e,u,v,hp] using HH
  by_cases hi : k+1<z.gap
  · have hM := h.openBonds k hi
    have hS : v.source=.off := Classical.byContradiction (fun hs => by
      have T := (h.cv e hs).2
      rw [hM] at T
      cases T)
    have hR := WindowA0Cleanup.ordinary_break u v hL (hm.trans hM)
      ((FreshEpochAuthentication.prefix_payload u v).2.2.trans hS)
    constructor
    · simpa [step,e,u,v] using hR.1
    · intro _ hx hy
      have TT := FreshEpochAuthentication.prefix_payload u v
      have hy' : v.rail≠.x := by simpa [v,e,←liftedSite_succ] using hy
      have H := hR.2 (fun hh => hx (TT.1.symm.trans hh)) (fun hh => hy' (TT.2.1.symm.trans hh))
      simpa [liftedSite_succ,step,e,u,v,hn'] using H
  · have hi' : k=z.gap-1 := by omega
    have hM : u.mark=true := by simpa [u,e,hi'] using h.markRight
    exact ⟨by simpa [step,e,u,v] using WindowA0Cleanup.pinned_break u v hL (hm.trans hM),
      fun H => (hi H).elim⟩

/-- Unpaid incoming mark into the old ghost top cannot put an X into
a clean retained top, even if the incoming socket itself was dirty. -/
theorem incoming_break_hold {p c n : Nat} (hn : 4≤n) {J : Fin n} {H : Nat}
    {z : Cut p c n} (h : Live J H z) (e : Fin n)
    (he : rightNeighbor e=z.top) (hp : geometricPay (z.config e) (z.config (rightNeighbor e))=false)
    (hRight : (step z.config e z.top).leader=false)
    (hx : (z.config z.top).rail≠.x) :
    (step z.config e z.top).rail≠.x := by
  let u := z.config e
  let v := z.config (rightNeighbor e)
  have hn' := notLoop hn e
  have he' : e=incoming z.top 0 := by
    apply FreshSeparation.succ_inj
    rw [incoming_right,liftedSite_zero]
    exact he
  have hpR : (stepPrefix u v).2.leader=false :=
    rightPrefix u v (by simpa [←he,step,u,v,hn'] using hRight)
  have hpM : (stepPrefix u v).1.mark=true := by
    rw [←leftPrefix]
    have H := covered_step_mark hn z.config h.mc e e
    simp [hp,step] at H
    exact H.trans (he'.symm ▸ h.markTop)
  have R := (WindowA0Cleanup.pinned_rails u v hpR hpM).2
  have H : FixedResidual.topRail (stepPrefix u v).2.rail ≠ .x := by
    exact fun hX => hx ((congrArg (fun i => (z.config i).rail) he).symm.trans
      ((FreshEpochAuthentication.prefix_payload u v).2.1.symm.trans
        (by cases hR : (stepPrefix u v).2.rail <;> simp_all [FixedResidual.topRail])))
  simpa [←he,step,u,v,hn',R] using H

open WindowFourHeadTrace

def Clean {p c n : Nat} (x : Cut p c n) (k : Nat) : Prop :=
  k≤x.gap ∧ ∀ j, j<k → (x.config (liftedSite x.top j)).rail≠.x

def topShift {p c n : Nat} (x : WindowA0ClosedEntry.State p c n) (e : Fin n) : Nat :=
  if moves x.tag.ledger e x.tag.iSlot then 1 else 0

theorem cut_keep_fields {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (x : WindowA0ClosedEntry.State p c n) (e : Fin n)
    (h : x.tag.reason=none) (h' : ¬WindowA0Ledger.done (WindowA0ClosedEntry.next S x e).tag) :
    let z := WindowA0ClosedEntry.cut x
    let y := WindowA0ClosedEntry.cut (WindowA0ClosedEntry.next S x e)
    y.config=step z.config e ∧ y.top=liftedSite z.top (topShift x e) ∧
      y.gap=z.gap-topShift x e := by
  have he : WindowA0Route.routeTwo S.group S.iTag S.jTag x.tag.ledger e=.keep := by
    apply Classical.byContradiction
    intro hR
    exact h' ((WindowA0Ledger.physical_exit_iff S x.tag e h).mpr hR)
  by_cases H : moves x.tag.ledger e x.tag.iSlot
  · simp [WindowA0ClosedEntry.cut,WindowA0ClosedEntry.next,WindowA0Ledger.next,
      h,he,landing,topShift,H,SevenTagCharge.advance,liftedSite_succ,liftedSite_zero]
  · simp [WindowA0ClosedEntry.cut,WindowA0ClosedEntry.next,WindowA0Ledger.next,
      h,he,landing,topShift,H,SevenTagCharge.advance,liftedSite_zero]

private theorem lift_add {n : Nat} (base : Fin n) (i j : Nat) :
    liftedSite (liftedSite base i) j=liftedSite base (i+j) := by
  apply Fin.ext
  change ((base.val+i)%n+j)%n=(base.val+(i+j))%n
  simp [Nat.add_assoc]

theorem clean_keep {p c n : Nat} (hn : 4≤n) {J : Fin n} {H : Nat}
    (x y : Cut p c n) (e : Fin n) (k δ : Nat)
    (hX : Live J H x) (hY : Live J H y) (hK : k<x.gap) (h : Clean x k)
    (hδ : δ≤1) (hy : y.config=step x.config e)
    (ht : y.top=liftedSite x.top δ) (hg : y.gap=x.gap-δ)
    (hpay : rightNeighbor e=x.top → δ=0 →
      geometricPay (x.config e) (x.config (rightNeighbor e))=false) :
    Clean y (k+(if e=liftedSite x.top k then 1 else 0)-δ) := by
  let b := if e=liftedSite x.top k then 1 else 0
  have hb : b≤1 := by dsimp [b]; split <;> omega
  change Clean y (k+b-δ)
  refine ⟨by rw [hg]; omega,?_⟩
  have L (j : Nat) (hj : δ≤j) (hJ : j≤x.gap) :
      (step x.config e (liftedSite x.top j)).leader=false := by
    have T : liftedSite y.top (j-δ)=liftedSite x.top j := by
      rw [ht,lift_add,show δ+(j-δ)=j by omega]
    rw [←T,←hy]
    by_cases hi : j<x.gap
    · exact old_noleader hY (j-δ) (by rw [hg]; omega)
    · have eq : j-δ=y.gap := by rw [hg]; omega
      rw [eq]
      change (y.config (target y)).leader=false
      rw [hY.fixedRight]
      exact hY.rightGhost
  intro r hr
  let j := δ+r
  have hj : j<k+b := by dsimp [j]; omega
  have hjg : j<x.gap := by omega
  rw [ht,lift_add,hy]
  change (step x.config e (liftedSite x.top j)).rail≠.x
  by_cases he : e=liftedSite x.top j
  · have hright := L (j+1) (by dsimp [j]; omega) (by omega)
    rw [he,liftedSite_succ] at hright
    rw [he]
    exact (outgoing_break hn hX j hjg hright).1
  · by_cases hR : rightNeighbor e=liftedSite x.top j
    · cases je : j with
      | zero =>
        have hT : rightNeighbor e=x.top := by simpa only [je,liftedSite_zero] using hR
        have hd : δ=0 := by dsimp [j] at je; omega
        have hkpos : 0<k := by
          by_cases H : k=0
          · have hb' : b=0 := by
              have hn' : e≠liftedSite x.top k := by simpa only [je,H] using he
              simp [b,hn']
            omega
          · omega
        rw [liftedSite_zero]
        exact incoming_break_hold hn hX e hT (hpay hT hd)
          (by simpa only [je,liftedSite_zero] using L j (by dsimp [j]; omega) (Nat.le_of_lt hjg))
          (by simpa only [liftedSite_zero] using h.2 0 hkpos)
      | succ q =>
        have hE : e=liftedSite x.top q := by
          apply FreshSeparation.succ_inj
          simpa only [je,liftedSite_succ] using hR
        have hk' : q+1<k := by
          by_cases HH : q+1<k
          · exact HH
          · have eq : q+1=k := by omega
            have hNe : e≠liftedSite x.top k := by
              simpa only [je,eq] using he
            have hb' : b=0 := by simp [b,hNe]
            omega
        have hL := L j (by dsimp [j]; omega) (Nat.le_of_lt hjg)
        rw [hE,je,liftedSite_succ] at hL
        rw [hE]
        exact (outgoing_break hn hX q (by omega) hL).2 (by omega)
          (h.2 q (by omega)) (h.2 (q+1) hk')
    · have hj' : j<k := by
        by_cases hh : j<k
        · exact hh
        · have eq : j=k := by omega
          have hb' : b=0 := by simp [b,←eq,he]
          omega
      simpa [step,Ne.symm he,Ne.symm hR] using h.2 j hj'

theorem clean_keep_capped {p c n : Nat} (hn : 4≤n) {J : Fin n} {H : Nat}
    (x y : Cut p c n) (e : Fin n) (k δ : Nat)
    (hX : Live J H x) (hY : Live J H y) (hK : k≤x.gap) (h : Clean x k)
    (hδ : δ≤1) (hy : y.config=step x.config e)
    (ht : y.top=liftedSite x.top δ) (hg : y.gap=x.gap-δ)
    (hpay : rightNeighbor e=x.top → δ=0 →
      geometricPay (x.config e) (x.config (rightNeighbor e))=false) :
    Clean y (k+(if k<x.gap ∧ e=liftedSite x.top k then 1 else 0)-δ) := by
  let b := if k<x.gap ∧ e=liftedSite x.top k then 1 else 0
  have hb : b≤1 := by dsimp [b]; split <;> omega
  have hkb : k+b≤x.gap := by
    dsimp [b]
    split
    · rename_i hh; have := hh.1; omega
    · omega
  change Clean y (k+b-δ)
  refine ⟨by rw [hg]; omega,?_⟩
  have L (j : Nat) (hj : δ≤j) (hJ : j≤x.gap) :
      (step x.config e (liftedSite x.top j)).leader=false := by
    have T : liftedSite y.top (j-δ)=liftedSite x.top j := by
      rw [ht,lift_add,show δ+(j-δ)=j by omega]
    rw [←T,←hy]
    by_cases hi : j<x.gap
    · exact old_noleader hY (j-δ) (by rw [hg]; omega)
    · have eq : j-δ=y.gap := by rw [hg]; omega
      rw [eq]
      change (y.config (target y)).leader=false
      rw [hY.fixedRight]
      exact hY.rightGhost
  intro r hr
  let j := δ+r
  have hj : j<k+b := by dsimp [j]; omega
  have hjg : j<x.gap := by omega
  rw [ht,lift_add,hy]
  change (step x.config e (liftedSite x.top j)).rail≠.x
  by_cases he : e=liftedSite x.top j
  · have hright := L (j+1) (by dsimp [j]; omega) (by omega)
    rw [he,liftedSite_succ] at hright
    rw [he]
    exact (outgoing_break hn hX j hjg hright).1
  · by_cases hR : rightNeighbor e=liftedSite x.top j
    · cases je : j with
      | zero =>
        have hT : rightNeighbor e=x.top := by simpa only [je,liftedSite_zero] using hR
        have hd : δ=0 := by dsimp [j] at je; omega
        have hkpos : 0<k := by
          by_cases H : k=0
          · have hb' : b=0 := by
              have hn' : e≠liftedSite x.top k := by simpa only [je,H] using he
              simp [b,hn']
            omega
          · omega
        rw [liftedSite_zero]
        exact incoming_break_hold hn hX e hT (hpay hT hd)
          (by simpa only [je,liftedSite_zero] using L j (by dsimp [j]; omega) (Nat.le_of_lt hjg))
          (by simpa only [liftedSite_zero] using h.2 0 hkpos)
      | succ q =>
        have hE : e=liftedSite x.top q := by
          apply FreshSeparation.succ_inj
          simpa only [je,liftedSite_succ] using hR
        have hk' : q+1<k := by
          by_cases HH : q+1<k
          · exact HH
          · have eq : q+1=k := by omega
            have hNe : e≠liftedSite x.top k := by
              simpa only [je,eq] using he
            have hb' : b=0 := by simp [b,hNe]
            omega
        have hL := L j (by dsimp [j]; omega) (Nat.le_of_lt hjg)
        rw [hE,je,liftedSite_succ] at hL
        rw [hE]
        exact (outgoing_break hn hX q (by omega) hL).2 (by omega)
          (h.2 q (by omega)) (h.2 (q+1) hk')
    · have hj' : j<k := by
        by_cases hh : j<k
        · exact hh
        · have eq : j=k := by omega
          have hb' : b=0 := by simp [b,←eq,he]
          omega
      simpa [step,Ne.symm he,Ne.symm hR] using h.2 j hj'

structure SweepState (p c n : Nat) where
  physical : WindowA0ClosedEntry.State p c n
  cleaned : Nat

def sweepNext {p c n : Nat} (S : WindowA0Ledger.Scope n) (z : SweepState p c n)
    (e : Fin n) : SweepState p c n :=
  ⟨WindowA0ClosedEntry.next S z.physical e,
    z.cleaned+(if e=liftedSite (WindowA0ClosedEntry.cut z.physical).top z.cleaned then 1 else 0)
      -topShift z.physical e⟩

def goal {p c n : Nat} (z : SweepState p c n) : Prop :=
  WindowA0Ledger.done z.physical.tag ∨ z.physical.gap≤z.cleaned

def Valid {p c n : Nat} (z₀ : Config p c n) (S : WindowA0Ledger.Scope n)
    (J : Fin n) (H : Nat) (z : SweepState p c n) : Prop :=
  WindowA0ClosedEntry.Admitted z₀ S J H z.physical ∧
    (WindowA0Ledger.done z.physical.tag ∨ Clean (WindowA0ClosedEntry.cut z.physical) z.cleaned)

private theorem noPay_when_noShift {p c n : Nat}
    (x : WindowA0ClosedEntry.State p c n) (e : Fin n)
    (he : rightNeighbor e=(WindowA0ClosedEntry.cut x).top) (hδ : topShift x e=0) :
    geometricPay ((WindowA0ClosedEntry.cut x).config e)
      ((WindowA0ClosedEntry.cut x).config (rightNeighbor e))=false := by
  have he' : e=x.tag.iSlot := FreshSeparation.succ_inj he
  apply Bool.eq_false_iff.mpr
  intro hp
  have H : moves x.tag.ledger e x.tag.iSlot := ⟨he',hp⟩
  simp [topShift,H] at hδ

theorem sweep_keep {p c n : Nat} {z₀ : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat) (z : SweepState p c n)
    (e : Fin n) (h : Valid z₀ S J H z) (hs : ¬ goal z) :
    Valid z₀ S J H (sweepNext S z e) := by
  have HG := WindowA0ClosedEntry.close hn S J H z.physical e h.1
  refine ⟨HG,?_⟩
  by_cases hG : WindowA0Ledger.done (WindowA0ClosedEntry.next S z.physical e).tag
  · exact .inl hG
  have old := h.1.resolve_left (fun hp => hs (.inl hp))
  have new := HG.resolve_left hG
  have hC := h.2.resolve_left (fun hp => hs (.inl hp))
  have hN := cut_keep_fields S z.physical e old.2.1.2.1 hG
  exact .inr (clean_keep hn _ _ e z.cleaned (topShift z.physical e) old.1 new.1
    (Nat.lt_of_not_ge (fun hh => hs (.inr hh))) hC (by unfold topShift; split <;> omega)
    hN.1 hN.2.1 hN.2.2 (noPay_when_noShift z.physical e))

noncomputable def reserve {p c n : Nat} (z : SweepState p c n) : Nat := by
  classical
  exact if goal z then 0 else z.physical.gap-z.cleaned

theorem sweep_reserve {p c n : Nat} (S : WindowA0Ledger.Scope n) (z : SweepState p c n)
    (e : Fin n) (hs : ¬goal z) :
    reserve (sweepNext S z e)+
      (if e=liftedSite (WindowA0ClosedEntry.cut z.physical).top z.cleaned then 1 else 0)≤reserve z := by
  let b := if e=liftedSite (WindowA0ClosedEntry.cut z.physical).top z.cleaned then 1 else 0
  have hb : b≤1 := by dsimp [b]; split <;> omega
  have hGap : z.cleaned<z.physical.gap := Nat.lt_of_not_ge (fun h => hs (.inr h))
  by_cases hg : goal (sweepNext S z e)
  · simp only [reserve,if_pos hg,if_neg hs]
    change 0+b≤_
    omega
  · have hr : z.physical.tag.reason=none := by
      cases he : z.physical.tag.reason
      · rfl
      · exact (hs (.inl (by simp [WindowA0Ledger.done,he]))).elim
    have hD : ¬WindowA0Ledger.done (WindowA0ClosedEntry.next S z.physical e).tag :=
      fun hh => hg (.inl hh)
    have hN := (cut_keep_fields S z.physical e hr hD).2.2
    let δ := topShift z.physical e
    have hδ : δ≤1 := by unfold δ topShift; split <;> omega
    change (WindowA0ClosedEntry.next S z.physical e).gap=z.physical.gap-δ at hN
    simp only [reserve,if_neg hs,if_neg hg]
    change (WindowA0ClosedEntry.next S z.physical e).gap-(z.cleaned+b-δ)+b≤z.physical.gap-z.cleaned
    rw [hN]
    omega

theorem expected_x_sweep {p c n : Nat} {z₀ : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat)
    (z : WindowA0ClosedEntry.State p c n)
    (h : WindowA0ClosedEntry.Admitted z₀ S J H z) :
    IIDExpectedHittingTimeAtMost (sweepNext S) goal (⟨z,0⟩ : SweepState p c n) (n*H) := by
  let start : SweepState p c n := ⟨z,0⟩
  have hV : Valid z₀ S J H start := ⟨h,.inr ⟨Nat.zero_le _,fun j hj =>
    (Nat.not_lt_zero j hj).elim⟩⟩
  have hM := TripleControlled.mean_of_potential (sweepNext S) goal (Valid z₀ S J H)
    reserve (sweep_keep hn S J H) (fun x _ hx => by
      let e := liftedSite (WindowA0ClosedEntry.cut x.physical).top x.cleaned
      exact TripleControlled.progress_raw_drift (reserve x) e _
        (by simpa only [e,if_true] using sweep_reserve S x e hx)
        (fun i => Nat.le_trans (Nat.le_add_right _ _) (sweep_reserve S x i hx))) start hV
  apply TripleRenewal.expected_mono hM
  apply Nat.mul_le_mul_left
  classical
  by_cases hs : goal start
  · simp [reserve,hs]
  · rw [reserve,if_neg hs]
    have hL := h.resolve_left (fun he => hs (.inl he))
    change z.gap-0≤H
    simp only [Nat.sub_zero]
    exact hL.1.bounded

theorem sweep_sound {p c n : Nat} {z₀ : Config p c n} {S : WindowA0Ledger.Scope n}
    {J : Fin n} {H : Nat} {z : SweepState p c n}
    (h : Valid z₀ S J H z) (he : goal z) :
    WindowA0Ledger.done z.physical.tag ∨
      ∀ j, j<z.physical.gap →
        ((WindowA0ClosedEntry.cut z.physical).config
          (liftedSite (WindowA0ClosedEntry.cut z.physical).top j)).rail≠.x := by
  by_cases hd : WindowA0Ledger.done z.physical.tag
  · exact .inl hd
  · have hp := he.resolve_left hd
    have hc := h.2.resolve_left hd
    exact .inr (fun j hj => hc.2 j (Nat.lt_of_lt_of_le hj hp))

open RootedAssembly WindowFiveStages

theorem sweep_run_of_clean {p c n : Nat} {z₀ : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat) (z : SweepState p c n)
    (u : List (Fin n)) (hz : Valid z₀ S J H z)
    (h : WindowFiveStages.Clean (fun w => goal (GGTiming.runMarks (sweepNext S) z w)) u) :
    Valid z₀ S J H (GGTiming.runMarks (sweepNext S) z u) := by
  induction u generalizing z with
  | nil => exact hz
  | cons e u ih =>
    have hnot : ¬goal z := by simpa [GGTiming.runMarks] using h 0 (by simp)
    have hTail : WindowFiveStages.Clean
        (fun w => goal (GGTiming.runMarks (sweepNext S) (sweepNext S z e) w)) u := by
      intro k hk
      have H := h (k+1) (by simp; omega)
      simpa [GGTiming.runMarks] using H
    exact ih _ (sweep_keep hn S J H z e hz hnot) hTail

/-- The handoff tests exact first exit rather than a padded X-clean
endpoint. The actual physical suffix remains unconstrained after the
handoff; no other phase may consume a stale launch from this sweep. -/
theorem exact_sweep_handoff {p c n : Nat} {z₀ : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat)
    (z : WindowA0ClosedEntry.State p c n)
    (hz : WindowA0ClosedEntry.Admitted z₀ S J H z)
    (u : List (Fin n))
    (hu : FirstExit (fun w => goal (GGTiming.runMarks (sweepNext S) ⟨z,0⟩ w)) u) :
    let y := GGTiming.runMarks (WindowA0ClosedEntry.next S) z u
    WindowA0Ledger.done y.tag ∨ ∀ j, j<y.gap →
      ((WindowA0ClosedEntry.cut y).config (liftedSite (WindowA0ClosedEntry.cut y).top j)).rail≠.x := by
  classical
  let init : SweepState p c n := ⟨z,0⟩
  have hV : Valid z₀ S J H init := ⟨hz,.inr ⟨Nat.zero_le _,fun j hj =>
    (Nat.not_lt_zero j hj).elim⟩⟩
  have hh := sweep_sound (sweep_run_of_clean hn S J H init u hV hu.1) hu.2
  have proj (init : SweepState p c n) (u : List (Fin n)) :
      (GGTiming.runMarks (sweepNext S) init u).physical=
        GGTiming.runMarks (WindowA0ClosedEntry.next S) init.physical u := by
    induction u generalizing init with
    | nil => rfl
    | cons e u ih => exact ih (sweepNext S init e)
  rw [proj] at hh
  exact hh

def xStage {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (z : WindowA0ClosedEntry.State p c n) : TripleRenewal.Stage (WindowA0ClosedEntry.next S) z where
  State := List (Fin n)
  start := []
  next := wordNext
  project := GGTiming.runMarks (WindowA0ClosedEntry.next S) z
  ready := FirstExit (fun w => goal (GGTiming.runMarks (sweepNext S) ⟨z,0⟩ w))
  reachable := fun _ => True
  projInit := rfl
  projStep y e := GGTiming.runMarks_append _ _ y [e]
  reachStart := trivial
  reachStep _ _ _ := trivial

theorem xStage_mean {p c n : Nat} {z₀ : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat)
    (z : WindowA0ClosedEntry.State p c n) (hz : WindowA0ClosedEntry.Admitted z₀ S J H z) :
    let Y := xStage S z
    IIDExpectedHittingTimeAtMost Y.next Y.ready Y.start (n*H) := by
  classical
  let init : SweepState p c n := ⟨z,0⟩
  let fold := GGTiming.runMarks (sweepNext S) init
  let stop := fun w => goal (fold w)
  dsimp only
  intro t
  change iidHitCost wordNext (FirstExit stop) t []≤_
  rw [cost_firstExit stop t [] (clean_nil stop)]
  have cost (t : Nat) (w : List (Fin n)) :
      iidHitCost wordNext stop t w=iidHitCost (sweepNext S) goal t (fold w) := by
    induction t generalizing w with
    | zero => rfl
    | succ t ih =>
      unfold iidHitCost
      change (if stop w then _ else _)=if stop w then _ else _
      have H : (fun e => iidHitCost wordNext stop t (wordNext w e)) =
          (fun e => iidHitCost (sweepNext S) goal t (sweepNext S (fold w) e)) :=
        funext (fun e => by rw [ih]; unfold fold wordNext; rw [GGTiming.runMarks_append]; rfl)
      rw [H]
  rw [cost]
  exact expected_x_sweep hn S J H z hz t

/-- Charge the real cleanup before an arbitrary later physical clock.
Only exact sweep exits need a continuation proof. -/
theorem mean_after_sweep {p c n : Nat} {z₀ : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H B : Nat)
    (z : WindowA0ClosedEntry.State p c n) (hz : WindowA0ClosedEntry.Admitted z₀ S J H z)
    (after : ∀ y : WindowA0ClosedEntry.State p c n, WindowA0ClosedEntry.Admitted z₀ S J H y →
      (∀ j, j<y.gap →
        ((WindowA0ClosedEntry.cut y).config (liftedSite (WindowA0ClosedEntry.cut y).top j)).rail≠.x) →
      IIDExpectedHittingTimeAtMost (WindowA0ClosedEntry.next S)
        (fun y => WindowA0Ledger.done y.tag) y B) :
    IIDExpectedHittingTimeAtMost (WindowA0ClosedEntry.next S)
      (fun y => WindowA0Ledger.done y.tag) z (n*H+B) := by
  let Y := xStage S z
  let D := fun y : WindowA0ClosedEntry.State p c n => WindowA0Ledger.done y.tag
  intro t
  have E := TripleRenewal.glue_until_stop (WindowA0ClosedEntry.next S) Y.next Y.project
    Y.projStep D Y.ready Y.reachable Y.reachStep B t (fun u k _ hu hD _ => by
      let w : List (Fin n) := u
      have hx := (exact_sweep_handoff hn S J H z hz w hu).resolve_left hD
      exact after _ (WindowA0ClosedEntry.close_word hn S J H z w hz) hx k)
    t (Nat.le_refl _) Y.start Y.reachStart
  rw [Y.projInit] at E
  rw [Nat.add_mul]
  exact Nat.le_trans E (Nat.add_le_add (xStage_mean hn S J H z hz t)
    (Nat.mul_le_mul_left _ (TripleRenewal.terminalMass_le_total _ _ _ _ _)))

end L4.WindowA0XSweep
