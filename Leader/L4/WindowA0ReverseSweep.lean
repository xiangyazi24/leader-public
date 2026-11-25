import Leader.L4.WindowA0XSweep

/-! Physical reverse U sweep. A new L1/L2 on the actual J door
interrupts cleanup; it is never identified from a resident U alone. -/
namespace L4.WindowA0ReverseSweep
open WindowA0IH GGStage SevenTagCharge ResidualSweep WindowA0XSweep

def freshDoor {p c n : Nat} (z : WindowA0ClosedEntry.State p c n) (e : Fin n) : Prop :=
  e=z.tag.jSlot ∧ launches (z.tag.ledger.config (rightNeighbor e)).source
    (z.tag.ledger.config e).rail

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

private theorem pair_up {p c : Nat} (u v : Site p c)
    (hR : (pairStep u v).2.leader=false)
    (hOrd : (stepPrefix u v).1.mark=false → v.source=.off)
    (hPin : (stepPrefix u v).1.mark=true → ¬launches v.source u.rail) :
    ¬Up (pairStep u v).2.rail ∧
      ((¬Up u.rail) → ((stepPrefix u v).1.mark=false → ¬Up v.rail) →
        ¬Up (pairStep u v).1.rail) := by
  have hp := FreshEpochAuthentication.prefix_payload u v
  have hl := rightPrefix _ _ hR
  cases hm : (stepPrefix u v).1.mark
  · have hs := hp.2.2.trans (hOrd hm)
    obtain ⟨right,left⟩ := WindowA0Cleanup.ordinary_reverse u v hl hm hs
    refine ⟨right,fun hU hV => left ?_ ?_⟩
    · rwa [hp.1]
    · rw [hp.2.1]
      exact hV rfl
  · constructor
    · rw [(WindowA0Cleanup.pinned_rails _ _ hl hm).2]
      exact top_no_up _
    · intro hU _
      have hN : ¬ launches (stepPrefix u v).2.source (stepPrefix u v).1.rail := by
        rw [hp.2.2,hp.1]
        exact hPin hm
      exact (WindowA0Cleanup.pinned_up _ _ hl hm hN (by rwa [hp.1])).1

/-- The nominated ordinary incoming clears its responder, even from
a dirty U. This is also the persistence side of the reverse sweep. -/
theorem ordinary_row {p c : Nat} (u v : Site p c)
    (hR : (pairStep u v).2.leader=false)
    (hM : (stepPrefix u v).1.mark=false) (hS : v.source=.off) :
    ¬Up (pairStep u v).2.rail ∧
      (¬Up u.rail → ¬Up v.rail → ¬Up (pairStep u v).1.rail) := by
  have H := pair_up u v hR (fun _ => hS) (fun hm => by rw [hM] at hm; contradiction)
  exact ⟨H.1,fun a b => H.2 a (fun _ => b)⟩

/-- In a pinned row the retained responder is cleared; the donor is
U-free if it already was and no actual fresh door launch occurs. -/
theorem pinned_row {p c : Nat} (u v : Site p c)
    (hR : (pairStep u v).2.leader=false)
    (hM : (stepPrefix u v).1.mark=true) :
    ¬Up (pairStep u v).2.rail ∧
      (¬Up u.rail → ¬launches v.source u.rail → ¬Up (pairStep u v).1.rail) := by
  have ho : (stepPrefix u v).1.mark=false → v.source=.off := fun h => by rw [hM] at h; contradiction
  refine ⟨?_,?_⟩
  · rw [(WindowA0Cleanup.pinned_rails u v (rightPrefix _ _ hR) hM).2]
    exact top_no_up _
  · intro hU hn
    exact (pair_up u v hR ho (fun _ => hn)).2 hU (fun h => by rw [hM] at h; contradiction)

#print axioms ordinary_row
#print axioms pinned_row

/-- Actual ordinary bond, between two retained sites. The incoming
responder becomes U-free and a U-free donor stays so if both old sites
were U-free. -/
theorem ordinary_site {p c n : Nat} (hn : 4≤n)
    {J : Fin n} {H : Nat} {x : Cut p c n} (hx : Live J H x)
    (k : Nat) (hk : k+1<x.gap)
    (hR : (step x.config (liftedSite x.top k) (liftedSite x.top (k+1))).leader=false) :
    let e := liftedSite x.top k
    let t := liftedSite x.top (k+1)
    ¬Up (step x.config e t).rail ∧
      (¬Up (x.config e).rail → ¬Up (x.config t).rail → ¬Up (step x.config e e).rail) := by
  let e := liftedSite x.top k
  let u := x.config e
  let v := x.config (rightNeighbor e)
  have hM : u.mark=false := hx.openBonds k hk
  have hP : geometricPay u v=false := Bool.eq_false_iff.mpr (fun hh => by
    have h := RearTrace.paid_was_marked hx.mc e hh
    rw [show (x.config e).mark=false from hM] at h
    cases h)
  have hS : v.source=.off := Classical.byContradiction (fun h => by
    have H := (hx.cv e h).2
    rw [show (x.config e).mark=false from hM] at H
    cases H)
  have hpM : (stepPrefix u v).1.mark=false := by
    rw [←leftPrefix]
    have HH := covered_step_mark hn x.config hx.mc e e
    have hp' : geometricPay (x.config e) (x.config (rightNeighbor e))=false := hP
    simp [hp',step] at HH
    exact HH.trans hM
  have hN := notLoop hn e
  have hR' : (pairStep u v).2.leader=false := by
    simpa [liftedSite_succ,step,e,u,v,hN] using hR
  have R := ordinary_row u v hR' hpM hS
  simpa [liftedSite_succ,step,e,u,v,hN] using R

/-- The old marked incoming bond clears a retained ghost responder
whether or not its own left corridor's controller launches. -/
theorem incoming_top_site {p c n : Nat} (hn : 4≤n) {J : Fin n} {H : Nat} {x : Cut p c n}
    (hx : Live J H x) (e : Fin n) (he : rightNeighbor e=x.top)
    (hp : geometricPay (x.config e) (x.config (rightNeighbor e))=false)
    (hR : (step x.config e x.top).leader=false) :
    ¬Up (step x.config e x.top).rail := by
  let u := x.config e
  let v := x.config (rightNeighbor e)
  have hn' := notLoop hn e
  have he' : e=incoming x.top 0 := by
    apply FreshSeparation.succ_inj
    rw [incoming_right,liftedSite_zero]
    exact he
  have hpR : (pairStep u v).2.leader=false := by simpa [←he,step,u,v,hn'] using hR
  have hpM : (stepPrefix u v).1.mark=true := by
    rw [←leftPrefix]
    have H := covered_step_mark hn x.config hx.mc e e
    simp [hp,step] at H
    exact H.trans (he'.symm ▸ hx.markTop)
  simpa [←he,step,u,v,hn'] using (pinned_row u v hpR hpM).1

/-- On the fixed right door only an actual fresh launch can introduce
U into an already U-free retained donor. -/
theorem fixed_door_site {p c n : Nat} (hn : 4≤n) {J : Fin n} {H : Nat} {x : Cut p c n}
    (hx : Live J H x) (e : Fin n) (he : e=liftedSite x.top (x.gap-1))
    (hR : (step x.config e J).leader=false)
    (hU : ¬Up (x.config e).rail)
    (hLaunch : ¬launches (x.config J).source (x.config e).rail) :
    ¬Up (step x.config e e).rail := by
  let u := x.config e
  let v := x.config (rightNeighbor e)
  have hJ : rightNeighbor e=J := by
    rw [he,←liftedSite_succ,show x.gap-1+1=x.gap by have := hx.gapPos; omega]
    exact hx.fixedRight
  have hm : u.mark=true := by simpa [u,he] using hx.markRight
  have hp : geometricPay u v=false := by
    have hIn : incoming x.top x.gap=e := by
      apply FreshSeparation.succ_inj
      rw [incoming_right,hJ]
      exact hx.fixedRight
    have nolead (q : Nat) (hq : q<x.gap) :
        (x.config (liftedSite x.top q)).leader=false := by
      cases q with
      | zero => simpa only [liftedSite_zero] using hx.topGhost
      | succ q =>
        apply Bool.eq_false_iff.mpr
        intro h
        have hh := hx.mc (liftedSite x.top q) (.inl (by rwa [←liftedSite_succ]))
        rw [hx.openBonds q hq] at hh
        cases hh
    have H := (WindowA0Drained.drained_step hn x.config x.top e hx.gapPos
      hx.markTop (hIn.symm ▸ hm) hx.empty nolead).1
    simpa [moved,hIn,u,v] using H
  have hpM : (stepPrefix u v).1.mark=true := by
    rw [←leftPrefix]
    have H := covered_step_mark hn x.config hx.mc e e
    have hp' : geometricPay (x.config e) (x.config (rightNeighbor e))=false := hp
    simp [hp',step] at H
    exact H.trans hm
  have hN := notLoop hn e
  have hR' : (pairStep u v).2.leader=false := by
    rw [←hJ] at hR
    simpa [step,hN] using hR
  have hLaunch' : ¬launches v.source u.rail := by simpa [u,v,hJ] using hLaunch
  have H := (pinned_row u v hR' hpM).2 hU hLaunch'
  simpa [step,u,v] using H

#print axioms ordinary_site
#print axioms incoming_top_site
#print axioms fixed_door_site

def UFreeSuffix {p c n : Nat} (x : Cut p c n) (k : Nat) : Prop :=
  k≤x.gap ∧ ∀ j, k≤j → j<x.gap → ¬Up (x.config (liftedSite x.top j)).rail

private theorem lift_add {n : Nat} (s : Fin n) (a b : Nat) :
    liftedSite (liftedSite s a) b=liftedSite s (a+b) := by
  apply Fin.ext
  change ((s.val+a)%n+b)%n=(s.val+(a+b))%n
  simp [Nat.add_assoc]

private theorem noLeader {p c n : Nat} {J : Fin n} {H : Nat} {x : Cut p c n}
    (hx : Live J H x) (j : Nat) (hj : j≤x.gap) :
    (x.config (liftedSite x.top j)).leader=false := by
  by_cases he : j=x.gap
  · rw [he]
    change (x.config (target x)).leader=false
    rw [hx.fixedRight]
    exact hx.rightGhost
  cases j with
  | zero => simpa only [liftedSite_zero] using hx.topGhost
  | succ j =>
    apply Bool.eq_false_iff.mpr
    intro hp
    have HM := hx.mc (liftedSite x.top j) (.inl (by rwa [←liftedSite_succ]))
    rw [hx.openBonds j (by omega)] at HM
    cases HM

theorem suffix_keep {p c n : Nat} (hn : 4≤n) {J : Fin n} {H : Nat}
    (x y : Cut p c n) (e : Fin n) (k δ : Nat)
    (hx : Live J H x) (hy : Live J H y) (hk : 0<k) (hc : UFreeSuffix x k)
    (hδ : δ≤1) (hC : y.config=step x.config e)
    (hT : y.top=liftedSite x.top δ) (hG : y.gap=x.gap-δ)
    (hpay : rightNeighbor e=x.top → δ=0 →
      geometricPay (x.config e) (x.config (rightNeighbor e))=false)
    (hLaunch : e=liftedSite x.top (x.gap-1) →
      ¬launches (x.config J).source (x.config e).rail) :
    UFreeSuffix y (k-(if e=incoming x.top (k-1) then 1 else 0)-δ) := by
  let b := if e=incoming x.top (k-1) then 1 else 0
  change UFreeSuffix y (k-b-δ)
  have hb : b≤1 := by dsimp [b]; split <;> omega
  have hkg := hc.1
  refine ⟨by rw [hG]; omega,?_⟩
  have L (j : Nat) (hj : δ≤j) (hJ : j≤x.gap) :
      (step x.config e (liftedSite x.top j)).leader=false := by
    have T : liftedSite y.top (j-δ)=liftedSite x.top j := by
      rw [hT,lift_add,show δ+(j-δ)=j by omega]
    rw [←T,←hC]
    exact noLeader hy _ (by rw [hG]; omega)
  intro r hr hrg
  let j := δ+r
  have hj : k-b≤j := by dsimp [j]; omega
  have hjg : j<x.gap := by dsimp [j]; rw [hG] at hrg; omega
  have hδj : δ≤j := by dsimp [j]; omega
  have nomRight : b=1 → rightNeighbor e=liftedSite x.top (k-1) := by
    intro hh
    have H : e=incoming x.top (k-1) := by
      unfold b at hh
      split at hh
      · assumption
      · contradiction
    rw [H,incoming_right]
  have cleared : j<k → rightNeighbor e=liftedSite x.top j := by
    intro hjk
    have hB : b=1 := by omega
    have eq : j=k-1 := by omega
    simpa only [eq] using nomRight hB
  rw [hT,lift_add,hC]
  change ¬Up (step x.config e (liftedSite x.top j)).rail
  by_cases he : e=liftedSite x.top j
  · have hjk : k≤j := by
      apply Nat.le_of_not_gt
      intro hh
      exact notLoop hn e ((cleared hh).trans he.symm)
    by_cases hD : j+1<x.gap
    · have hR := L (j+1) (by omega) (by omega)
      rw [he] at hR
      rw [he]
      exact (ordinary_site hn hx j hD hR).2 (hc.2 j hjk hjg) (hc.2 (j+1) (by omega) hD)
    · have eq : j=x.gap-1 := by omega
      have hR := L x.gap (by omega) (Nat.le_refl _)
      change (step x.config e (target x)).leader=false at hR
      rw [hx.fixedRight] at hR
      have door := he.trans (congrArg (liftedSite x.top) eq)
      rw [←he]
      exact fixed_door_site hn hx e door hR (he.symm ▸ hc.2 j hjk hjg) (hLaunch door)
  · by_cases hR : rightNeighbor e=liftedSite x.top j
    · cases je : j with
      | zero =>
        have htop : rightNeighbor e=x.top := by simpa only [je,liftedSite_zero] using hR
        have hLR : (step x.config e x.top).leader=false := by
          simpa only [je,liftedSite_zero] using L j hδj (by omega)
        rw [liftedSite_zero]
        exact incoming_top_site hn hx e htop (hpay htop (by omega)) hLR
      | succ q =>
        have hE : e=liftedSite x.top q := by
          apply FreshSeparation.succ_inj
          simpa only [je,liftedSite_succ] using hR
        have hh := L j hδj (by omega)
        rw [hE,je] at hh
        rw [hE]
        exact (ordinary_site hn hx q (by omega) hh).1
    · have hjk : k≤j := by
        apply Nat.le_of_not_gt
        exact fun hh => hR (cleared hh)
      simpa [step,Ne.symm he,Ne.symm hR] using hc.2 j hjk hjg

#print axioms suffix_keep

structure RevState (p c n : Nat) where
  physical : WindowA0ClosedEntry.State p c n
  left : Nat
  launched : Bool

def nominate {p c n : Nat} (z : RevState p c n) : Fin n :=
  incoming (WindowA0ClosedEntry.cut z.physical).top (z.left-1)

noncomputable def revNext {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (z : RevState p c n) (e : Fin n) : RevState p c n := by
  classical
  exact ⟨WindowA0ClosedEntry.next S z.physical e,
    z.left-(if e=nominate z then 1 else 0)-topShift z.physical e,
    z.launched || decide (freshDoor z.physical e)⟩

def done {p c n : Nat} (z : RevState p c n) : Prop :=
  WindowA0Ledger.done z.physical.tag ∨ z.launched=true ∨ z.left=0

def Good {p c n : Nat} (z₀ : Config p c n) (S : WindowA0Ledger.Scope n)
    (J : Fin n) (H : Nat) (z : RevState p c n) : Prop :=
  WindowA0ClosedEntry.Admitted z₀ S J H z.physical ∧
    (WindowA0Ledger.done z.physical.tag ∨ z.launched=true ∨
      UFreeSuffix (WindowA0ClosedEntry.cut z.physical) z.left)

theorem rev_keep {p c n : Nat} {z₀ : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat) (z : RevState p c n)
    (e : Fin n) (h : Good z₀ S J H z) (hs : ¬done z) :
    Good z₀ S J H (revNext S z e) := by
  have HG := WindowA0ClosedEntry.close hn S J H z.physical e h.1
  refine ⟨HG,?_⟩
  by_cases hG : WindowA0Ledger.done (WindowA0ClosedEntry.next S z.physical e).tag
  · exact .inl hG
  classical
  by_cases hL : freshDoor z.physical e
  · exact .inr (.inl (by simp [revNext,hL]))
  have old := h.1.resolve_left (fun hp => hs (.inl hp))
  have new := HG.resolve_left hG
  have hC := (h.2.resolve_left (fun hp => hs (.inl hp))).resolve_left (fun hp => hs (.inr (.inl hp)))
  have hN := cut_keep_fields S z.physical e old.2.1.2.1 hG
  refine .inr (.inr (suffix_keep hn _ _ e z.left (topShift z.physical e) old.1 new.1
    (by apply Nat.pos_of_ne_zero; exact fun hh => hs (.inr (.inr hh))) hC
    (by unfold topShift; split <;> omega) hN.1 hN.2.1 hN.2.2 ?_ ?_))
  · intro he hδ
    have he' : e=z.physical.tag.iSlot := FreshSeparation.succ_inj he
    apply Bool.eq_false_iff.mpr
    intro hp
    have hM : WindowFourHeadTrace.moves z.physical.tag.ledger e z.physical.tag.iSlot := ⟨he',hp⟩
    simp [topShift,hM] at hδ
  · intro he hd
    have hr : rightNeighbor e=J := by
      rw [he,←liftedSite_succ,show (WindowA0ClosedEntry.cut z.physical).gap-1+1=
        (WindowA0ClosedEntry.cut z.physical).gap by have := old.1.gapPos; omega]
      exact old.1.fixedRight
    have hE : e=z.physical.tag.jSlot := FreshSeparation.succ_inj (hr.trans old.2.2.symm)
    apply hL
    refine ⟨hE,?_⟩
    simpa [hr,WindowA0ClosedEntry.cut] using hd

theorem rev_charge {p c n : Nat} (S : WindowA0Ledger.Scope n) (z : RevState p c n)
    (e : Fin n) (h : ¬done z) :
    (revNext S z e).left+(if e=nominate z then 1 else 0)≤z.left := by
  have hP : 0<z.left := Nat.pos_of_ne_zero (fun hh => h (.inr (.inr hh)))
  simp only [revNext]
  split <;> omega

theorem expected_reverse {p c n : Nat} {z₀ : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat)
    (z : WindowA0ClosedEntry.State p c n)
    (hz : WindowA0ClosedEntry.Admitted z₀ S J H z) :
    IIDExpectedHittingTimeAtMost (revNext S) done (⟨z,z.gap,false⟩ : RevState p c n)
      (n*H) := by
  by_cases hD : WindowA0Ledger.done z.tag
  · intro t
    rw [iidHitCost_of_target _ _ _ (show done (⟨z,z.gap,false⟩ : RevState p c n) from .inl hD)]
    exact Nat.zero_le _
  let init : RevState p c n := ⟨z,z.gap,false⟩
  have hg : Good z₀ S J H init := ⟨hz,.inr (.inr ⟨Nat.le_refl _,fun j ha hb =>
    (Nat.not_lt_of_ge ha hb).elim⟩)⟩
  have M := TripleControlled.mean_of_potential (revNext S) done (Good z₀ S J H)
    RevState.left (rev_keep hn S J H) (fun z _ hs => by
      let e := nominate z
      exact TripleControlled.progress_raw_drift z.left e _
        (by simpa only [e,if_true] using rev_charge S z e hs)
        (fun i => Nat.le_trans (Nat.le_add_right _ _) (rev_charge S z i hs))) init hg
  exact TripleRenewal.expected_mono M
    (Nat.mul_le_mul_left _ (hz.resolve_left hD).1.bounded)

theorem reverse_sound {p c n : Nat} {z₀ : Config p c n} {S : WindowA0Ledger.Scope n}
    {J : Fin n} {H : Nat} {z : RevState p c n} (hz : Good z₀ S J H z) (hd : done z) :
    WindowA0Ledger.done z.physical.tag ∨ z.launched=true ∨
      UFreeSuffix (WindowA0ClosedEntry.cut z.physical) 0 := by
  rcases hd with h|h|h
  · exact .inl h
  · exact .inr (.inl h)
  · rcases hz.2 with ht|ht|hf
    · exact .inl ht
    · exact .inr (.inl ht)
    · exact .inr (.inr (h ▸ hf))

#print axioms rev_keep
#print axioms expected_reverse
#print axioms reverse_sound
end L4.WindowA0ReverseSweep
