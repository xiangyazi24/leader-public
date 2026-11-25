import Leader.L4.TriplePhase
import Leader.L4.WindowLocalNative

/-! Sealed-sector phase ticks on the actual (unconditionally advanced)
physical tape. Events outside the sector do not terminate its observer. -/
namespace L4.WindowSealed
open TriplePhase

private theorem hold_stutter {p c n d : Nat} (x y : Config p c n) (s : Fin n)
    (ph : Phase) (h : ph.Holds x s d)
    (hs : ∀ j, j ≤ d → y (liftedSite s j) = x (liftedSite s j)) :
    ph.Holds y s d := by
  have hr (q : Nat) (h : TriplePrep.ReturnFront x s d q) :
      TriplePrep.ReturnFront y s d q :=
    ⟨h.le, fun j hj => hs j hj ▸ h.empty j hj,
      fun j hj => hs j hj ▸ h.binary j hj, hs q h.le ▸ h.one,
      fun j hj => hs j (by have := h.le; omega) ▸ h.before j hj⟩
  have h0 : y s = x s := by simpa [liftedSite_zero] using hs 0 (Nat.zero_le d)
  cases ph with
  | ready => exact hr 0 h
  | returning k q => exact ⟨hr _ h.1,h0 ▸ h.2⟩
  | forward k q =>
      let h : SealedFront x s d q k := h
      exact ⟨h.within,⟨hs q h.within ▸ h.trail.signal,hs q h.within ▸ h.trail.bullet,
        fun j hj => hs j (by have := h.within; omega) ▸ h.trail.swept j hj⟩,
        fun j hj => hs j hj ▸ h.unique j hj,fun j hj => hs j hj ▸ h.binary j hj,
        h0 ▸ h.shield⟩

private theorem right_ne {n : Nat} (hn : 4 ≤ n) (e : Fin n) : rightNeighbor e ≠ e := by
  intro h
  have hh : liftedSite e 1 = liftedSite e 0 := by
    simpa [liftedSite_succ,liftedSite_zero] using h
  have := liftedSite_inj e (by omega : 1<n) (by omega : 0<n) hh
  omega

/-- The old native global stop predicate is false *on touching marks*
when the two endpoints survive. It is unrestricted on all other marks.
This local case split transfers the exact TriplePhase table, without
replacing the physical mark or invoking global no-event geometry. -/
theorem phase_tick_of_living_endpoints {p c n d : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (s e : Fin n) (bd : d+1<n)
    (hm : MCOV x) (hc : COV x) (hF : FirstMark x s d)
    (hS : (x s).leader = true) (hT : (x (liftedSite s (d+1))).leader = true)
    (hS' : (step x e s).leader = true) (hT' : (step x e (liftedSite s (d+1))).leader = true)
    (ph : Phase) (h : ph.Holds x s d) :
    (ph.tick s d e).Holds (step x e) s d := by
  have leaderEvent (ha : (x (rightNeighbor e)).leader = true)
      (hb : (step x e (rightNeighbor e)).leader = true) :
      TripleResidual.event x e = false := by
    have hd : TripleResidual.death x e = false := by
      apply Bool.eq_false_iff.mpr
      intro hD
      have := (TripleResidual.death_iff_leader_loss x e (right_ne hn e) hc ha).mp hD
      simp [hb] at this
    have hp : geometricPay (x e) (x (rightNeighbor e)) = false := by
      apply Bool.eq_false_iff.mpr
      intro hp
      have hh := TaggedTrace.geometricPay_responder_nonleader _ _ hp
      simp [step,right_ne hn e,hh] at hb
    simp [TripleResidual.event,hd,RankPhysical.retirement,hp]
  have internalEvent (j : Nat) (hj : j < d) (he : e = liftedSite s j) :
      TripleResidual.event x e = false := by
    subst e
    have hMark : (x (liftedSite s j)).mark = false := Bool.eq_false_iff.mpr (hF.before j hj)
    have hv := (coveredOrdinary hc ((covered_noRoot_iff hm).mpr hMark)).2.2.1
    have hp : geometricPay (x (liftedSite s j)) (x (rightNeighbor (liftedSite s j))) = false := by
      apply Bool.eq_false_iff.mpr
      intro hp
      have hh := RearTrace.paid_was_marked hm (liftedSite s j) hp
      simp [hMark] at hh
    simp [TripleResidual.event,TripleResidual.death,hv,RankPhysical.retirement,hp]
  have initiated (j : Nat) (hj : j ≤ d) (he : e = liftedSite s j) :
      TripleResidual.event x e = false := by
    by_cases hh : j < d
    · exact internalEvent j hh he
    · have : j=d := by omega
      subst j
      subst e
      rw [liftedSite_succ] at hT hT'
      exact leaderEvent hT hT'
  by_cases hit : ∃ j, j ≤ d ∧ (e = liftedSite s j ∨ rightNeighbor e = liftedSite s j)
  · obtain ⟨j,hj,he | he⟩ := hit
    · exact phase_tick_literal hn x s e bd hm hc hF hS hT ph h (initiated j hj he)
    · have hE : TripleResidual.event x e = false := by
        cases j with
        | zero =>
          simp only [liftedSite_zero] at he
          apply leaderEvent
          · rwa [he]
          · rwa [he]
        | succ j =>
          rw [liftedSite_succ] at he
          exact internalEvent j (by omega) (FreshSeparation.succ_inj he)
      exact phase_tick_literal hn x s e bd hm hc hF hS hT ph h hE
  · have vanish (j : Nat) (hj : j ≤ d) :
        e ≠ liftedSite s j ∧ rightNeighbor e ≠ liftedSite s j :=
      ⟨fun he => hit ⟨j,hj,.inl he⟩,fun he => hit ⟨j,hj,.inr he⟩⟩
    have hs (j : Nat) (hj : j ≤ d) : step x e (liftedSite s j) = x (liftedSite s j) := by
      simp [step,(vanish j hj).1.symm,(vanish j hj).2.symm]
    have h0 : e ≠ s ∧ rightNeighbor e ≠ s := by
      simpa [liftedSite_zero] using vanish 0 (Nat.zero_le d)
    have hh : ph.tick s d e = ph := by
      cases ph with
      | ready => simp [Phase.tick,h0.1,h0.2]
      | forward k q =>
        have h : SealedFront x s d q k := h
        simp [Phase.tick,(vanish q h.within).1]
      | returning k q =>
        have H : TriplePrep.ReturnFront x s d (q+1) ∧ (x s).shield = k.shield := h
        simp [Phase.tick,(vanish q (by have := H.1.le; omega)).1]
    rw [hh]
    exact hold_stutter x (step x e) s ph h hs

open SevenTagCharge WindowLocal in
/-- A keep mark preserves the named sector and advances its sealed
phase exactly. No restriction on rank changes or deaths outside it. -/
theorem certified_tick_keep {p c n d : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (z : Ledger p c n)
    (group cert : List (Fin n)) (target : Option (Fin n)) (e l r s t : Fin n)
    (bd : d+1<n) (hValid : Valid z x) (hSubset : cert ⊆ group)
    (hl : l ∈ cert) (hr : r ∈ cert)
    (hSec : CertifiedSector z l r s t d) (hKeep : route group cert target z e = Event.keep)
    (ph : Phase) (h : ph.Holds z.config (rightNeighbor s) d) :
    CertifiedSector (advance z e) l r s t d ∧
      (ph.tick (rightNeighbor s) d e).Holds (advance z e).config (rightNeighbor s) d := by
  have hSec' := certifiedSector_keep hn x z group cert target e l r s t d
    hValid hSubset hl hr hSec hKeep
  refine ⟨hSec', phase_tick_of_living_endpoints hn z.config (rightNeighbor s) e bd
    hValid.markCover hValid.sourceCover hSec.gap hSec.left_live.2 ?_ hSec'.left_live.2 ?_ ph h⟩
  · rw [hSec.terminal_site]
    exact hSec.right_live.2
  · rw [hSec.terminal_site]
    exact hSec'.right_live.2

open SevenTagCharge WindowLocal in
/-- Two adjacent sealed sectors consume the same literal old mark.
Allows the closing endpoint to equal the first (rank two). -/
theorem certified_twin_tick_keep {p c n a b : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (z : Ledger p c n)
    (group cert : List (Fin n)) (target : Option (Fin n)) (e l m r s t u : Fin n)
    (ha : a+1<n) (hb : b+1<n) (hValid : Valid z x) (hSubset : cert ⊆ group)
    (hl : l ∈ cert) (hm : m ∈ cert) (hr : r ∈ cert)
    (left : CertifiedSector z l m s t a) (right : CertifiedSector z m r t u b)
    (hKeep : route group cert target z e = Event.keep)
    (lp rp : Phase) (hL : lp.Holds z.config (rightNeighbor s) a)
    (hR : rp.Holds z.config (rightNeighbor t) b) :
    (CertifiedSector (advance z e) l m s t a ∧
      (lp.tick (rightNeighbor s) a e).Holds (advance z e).config (rightNeighbor s) a) ∧
    (CertifiedSector (advance z e) m r t u b ∧
      (rp.tick (rightNeighbor t) b e).Holds (advance z e).config (rightNeighbor t) b) :=
  ⟨certified_tick_keep hn x z group cert target e l m s t ha hValid hSubset hl hm left hKeep lp hL,
    certified_tick_keep hn x z group cert target e m r t u hb hValid hSubset hm hr right hKeep rp hR⟩

end L4.WindowSealed
