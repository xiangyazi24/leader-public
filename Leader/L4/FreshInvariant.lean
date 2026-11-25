import Leader.L4.FreshTraceBridge
import Leader.L4.FreshRows
import Leader.L4.TaggedGeometry

namespace L4

/-- A provenance certificate for a fresh live bullet: the same firing site
remains a living, shielded leader; its whole traversed arc is quiet; and
no incoming mark lies strictly after the origin and through the carrier. -/
structure FreshArc {p c1 n : Nat} (x : Config p c1 n) (z : Fin n) (d : Nat) : Prop where
  lt : d < n
  leader : (x z).leader = true
  shield : (x z).shield = true
  marks : ∀ j : Nat, j < d → (x (liftedSite z j)).mark = false
  signals : ∀ j : Nat, j ≤ d → (x (liftedSite z j)).signal = .zero

private theorem rn_ne {n : Nat} (hn : 4 ≤ n) (i : Fin n) : rightNeighbor i ≠ i := by
  intro h
  apply Nat.one_ne_zero
  apply liftedSite_inj i (by omega : 1 < n) (by omega : 0 < n)
  simpa [liftedSite_succ, liftedSite_zero] using h

private theorem bond_before {n : Nat} (z : Fin n) :
    rightNeighbor (liftedSite z (n-1)) = z := by
  rw [← liftedSite_succ, show n-1+1=n by have := z.isLt; omega, liftedSite_full]

private theorem plus_eq_lifted {n : Nat} (z : Fin n) (j : Nat) :
    TaggedFront.plusOffset z j = liftedSite z j := rfl

/-- A surviving certificate implies the exact nearest-root peace
predicate used at the L4 entrance interface. -/
theorem rootPeacefulAt_of_freshArc {p c1 n d : Nat} {x : Config p c1 n} {z : Fin n}
    (h : FreshArc x z d) (hc : MCOV x) : RootPeacefulAt x (liftedSite z d) := by
  let i := liftedSite z (n-1)
  have hi : rightNeighbor i = z := bond_before z
  have hm := hc i (Or.inl (hi ▸ h.leader))
  refine ⟨i,d,?_⟩
  simp only [hi,plus_eq_lifted]
  exact ⟨h.lt,hm,h.leader,h.shield,True.intro,h.marks,h.signals⟩

private theorem ordinary_arc_row {p c1 : Nat} (u v : Site p c1)
    (hm : u.mark = false) (hr : v.residue = nextResidue u.residue) (hl : v.leader = false)
    (hz : u.signal = .zero)
    (hv : v.signal = .zero ∨ u.bullet ≠ .none) :
    (pairStep u v).1.signal = .zero ∧ (pairStep u v).2.signal = .zero ∧
    (pairStep u v).1.shield = u.shield ∧ (pairStep u v).1.leader = u.leader := by
  have hmat : materialize u v = u := by simp [materialize,hm,hr,hl,defect]
  have hs : (Signal.zero == Signal.zero) = true := rfl
  have hnn : (Bullet.none == Bullet.none) = true := rfl
  have hd : (Bullet.dummy == Bullet.none) = false := rfl
  have hh : (Bullet.live == Bullet.none) = false := rfl
  have hf : fireInitiator u = u := by simp [fireInitiator,hz,hs]
  have hfr : fireResponder v = v := by simp [fireResponder,hl]
  have hi : impact u v = (u,v) := by simp [impact,hl]
  unfold pairStep stepPrefix native
  rw [hmat,hf,hfr,hi]
  simp only [pinned,hl,hm,Bool.not_false,Bool.true_and, Bool.false_eq_true, if_false]
  rcases h : u.bullet with _|_|_
  · have hvz := hv.resolve_right (by simp [h])
    cases hL : u.leader <;> cases hu : u.stock <;> cases hV : v.stock <;>
      simp [followerBullet,h,hl,hm,payment,payer,hV,hu,hL,hz,hvz,
        Signal.max,hnn,patrolWrite,finishBirth,pinned]
  · cases hL : u.leader <;> cases hu : u.stock <;> cases hV : v.stock <;>
      simp [followerBullet,h,hl,hm,payment,payer,hV,hu,hL,hz,
        Signal.max,hd,patrolWrite,finishBirth,pinned]
  · cases hL : u.leader <;> cases hu : u.stock <;> cases hV : v.stock <;>
      simp [followerBullet,h,hl,hm,payment,payer,hV,hu,hL,hz,
        Signal.max,hh,patrolWrite,finishBirth,pinned]

private theorem root_incoming_preserve {p c1 : Nat} (u v : Site p c1)
    (hl : v.leader = true) (hs : v.shield = true) (hz : v.signal = .zero) :
    (pairStep u v).2.leader = true ∧ (pairStep u v).2.shield = true ∧
      (pairStep u v).2.signal = .zero := by
  have hfr : fireResponder v = v := by simp [fireResponder,hl,hz]
  unfold pairStep stepPrefix native
  rw [hfr]
  generalize fireInitiator (materialize u v) = a
  cases h : a.bullet <;> simp [impact,h,hl,hs,hz,followerBullet,payment,pinned,
    show (Bullet.none == Bullet.none) = true from rfl,
    show (Bullet.dummy == Bullet.none) = false from rfl,
    show (Bullet.live == Bullet.none) = false from rfl,
    patrolWrite,finishBirth]

private theorem cover_ordinary_fields {p c1 n : Nat} {x : Config p c1 n} (hc : MCOV x)
    (e : Fin n) (hm : (x e).mark = false) :
    (x (rightNeighbor e)).leader = false ∧
    (x (rightNeighbor e)).residue = nextResidue (x e).residue := by
  constructor
  · exact Bool.eq_false_iff.mpr (fun h => by have := hc e (Or.inl h); simp_all)
  · by_cases hh : (x (rightNeighbor e)).residue = nextResidue (x e).residue
    · exact hh
    · exfalso
      have hg := hc e (Or.inr hh)
      simp_all

private theorem open_noPay {p c1 n : Nat} {x : Config p c1 n} (hc : MCOV x)
    (e : Fin n) (hm : (x e).mark = false) :
    geometricPay (x e) (x (rightNeighbor e)) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hmarks := covered_pair_marks (x e) (x (rightNeighbor e)) (hc e)
  rw [if_pos h] at hmarks
  simp [hm] at hmarks

private theorem right_alive_noPay {p c1 : Nat} (u v : Site p c1)
    (h : (pairStep u v).2.leader = true) : geometricPay u v = false := by
  apply Bool.eq_false_iff.mpr
  intro hh
  have hg := (pair_geometric_fields u v).2.2
  rw [if_pos hh] at hg
  simp [h] at hg

private theorem row_left {p c1 n : Nat} (x : Config p c1 n) (e : Fin n) :
    step x e e = (pairStep (x e) (x (rightNeighbor e))).1 := by simp [step]

private theorem row_right {p c1 n : Nat} (hn : 4 ≤ n) (x : Config p c1 n) (e : Fin n) :
    step x e (rightNeighbor e) = (pairStep (x e) (x (rightNeighbor e))).2 := by
  simp [step,rn_ne hn e]

private theorem row_other {p c1 n : Nat} (x : Config p c1 n) (e i : Fin n)
    (a : i ≠ e) (b : i ≠ rightNeighbor e) : step x e i = x i := by
  simp [step,a,b]

private theorem mark_unchanged {p c1 n : Nat} (hn : 4 ≤ n) {x : Config p c1 n}
    (hc : MCOV x) (e i : Fin n)
    (h : geometricPay (x e) (x (rightNeighbor e)) = false) :
    (step x e i).mark = (x i).mark := by rw [covered_step_mark hn x hc]; simp [h]

/-- If the carrier is not the selected donor, its same-origin arc stays
quiet regardless of whether the old carrier bullet was retained. -/
theorem freshArc_stationary {p c1 n d : Nat} (hn : 4 ≤ n) {x : Config p c1 n}
    {z e : Fin n} (hc : MCOV x) (h : FreshArc x z d) (he : e ≠ liftedSite z d) :
    FreshArc (step x e) z d := by
  obtain ⟨q,hq,hqe⟩ := liftedSite_of_site z e
  have hqd : q ≠ d := fun eq => he (eq ▸ hqe.symm)
  have hz : (x z).signal = .zero := by simpa [liftedSite_zero] using h.signals 0 (Nat.zero_le d)
  by_cases hi : q < d
  · have hm := h.marks q hi
    rw [hqe] at hm
    have ⟨hl,hr⟩ := cover_ordinary_fields hc e hm
    have hsz := h.signals q (by omega)
    rw [hqe] at hsz
    have hnv : liftedSite z (q+1) = rightNeighbor e := by rw [liftedSite_succ,hqe]
    have hvz := h.signals (q+1) (by omega)
    rw [hnv] at hvz
    have H := ordinary_arc_row (x e) (x (rightNeighbor e)) hm hr hl hsz (Or.inl hvz)
    have hnp := open_noPay hc e hm
    have hvNe : z ≠ rightNeighbor e := by
      intro eq
      have hh : liftedSite z 0 = liftedSite z (q+1) := by rw [liftedSite_zero,hnv,← eq]
      have := liftedSite_inj z (by omega : 0 < n) (by have := h.lt; omega : q+1<n) hh
      omega
    refine ⟨h.lt, ?_, ?_, ?_, ?_⟩
    · by_cases hze : z = e
      · rw [hze,row_left,H.2.2.2,← hze]; exact h.leader
      · rw [row_other x e z hze hvNe]; exact h.leader
    · by_cases hze : z = e
      · rw [hze,row_left,H.2.2.1,← hze]; exact h.shield
      · rw [row_other x e z hze hvNe]; exact h.shield
    · intro j hj; rw [mark_unchanged hn hc e _ hnp]; exact h.marks j hj
    · intro j hj
      by_cases a : liftedSite z j = e
      · rw [a,row_left]; exact H.1
      · by_cases b : liftedSite z j = rightNeighbor e
        · rw [b,row_right hn]; exact H.2.1
        · rw [row_other x e _ a b]; exact h.signals j hj
  · have hnot (j : Nat) (hj : j ≤ d) : liftedSite z j ≠ e := by
      intro eq
      have hh := liftedSite_inj z (by have := h.lt; omega : j<n) hq (eq.trans hqe.symm)
      omega
    by_cases hw : q+1 = n
    · have hw' : rightNeighbor e = z := by rw [← hqe,← liftedSite_succ,hw,liftedSite_full]
      have H := root_incoming_preserve (x e) (x (rightNeighbor e))
        (hw'.symm ▸ h.leader) (hw'.symm ▸ h.shield) (hw'.symm ▸ hz)
      have hnP := right_alive_noPay (x e) (x (rightNeighbor e)) H.1
      refine ⟨h.lt, ?_, ?_, ?_, ?_⟩
      · rw [← hw', row_right hn]; exact H.1
      · rw [← hw', row_right hn]; exact H.2.1
      · intro j hj; rw [mark_unchanged hn hc e _ hnP]; exact h.marks j hj
      · intro j hj
        by_cases hh : liftedSite z j = rightNeighbor e
        · rw [hh,row_right hn]; exact H.2.2
        · rw [row_other x e _ (hnot j hj) hh]; exact h.signals j hj
    · have hnv : liftedSite z (q+1) = rightNeighbor e := by rw [liftedSite_succ,hqe]
      have hnot' (j : Nat) (hj : j ≤ d) : liftedSite z j ≠ rightNeighbor e := by
        intro eq
        have hh := liftedSite_inj z (by have := h.lt; omega : j<n) (by omega : q+1<n) (eq.trans hnv.symm)
        omega
      have H (j : Nat) (hj : j ≤ d) :
          step x e (liftedSite z j) = x (liftedSite z j) :=
        row_other x e _ (hnot j hj) (hnot' j hj)
      have H0 : step x e z = x z := by simpa [liftedSite_zero] using H 0 (Nat.zero_le d)
      refine ⟨h.lt,H0.symm ▸ h.leader,H0.symm ▸ h.shield, ?_, ?_⟩
      · intro j hj; rw [H j (by omega)]; exact h.marks j hj
      · intro j hj; rw [H j hj]; exact h.signals j hj

/-- A transported old fresh bullet extends its arc by one at the same
origin; it cannot wrap onto that still living origin. -/
theorem freshArc_transfer {p c1 n d : Nat} (hn : 4 ≤ n) {x : Config p c1 n}
    {z : Fin n} (hc : MCOV x) (h : FreshArc x z d)
    (ht : tagTransfer (x (liftedSite z d)) (x (rightNeighbor (liftedSite z d))) = true) :
    FreshArc (step x (liftedSite z d)) z (d+1) := by
  let e := liftedSite z d
  have ⟨hb,_,hl,hm,_,_⟩ := (tagTransfer_iff _ _).mp ht
  have hnv : liftedSite z (d+1) = rightNeighbor e := liftedSite_succ z d
  have hlt : d+1 < n := by
    by_cases hh : d+1 < n
    · exact hh
    · have eq : d+1=n := by have := h.lt; omega
      rw [eq,liftedSite_full] at hnv
      rw [← hnv,h.leader] at hl
      contradiction
  obtain ⟨_,hr⟩ := cover_ordinary_fields hc e hm
  have H := ordinary_arc_row (x e) (x (rightNeighbor e)) hm hr hl
    (h.signals d (Nat.le_refl _)) (Or.inr (by change (x (liftedSite z d)).bullet ≠ .none; rw [hb]; decide))
  have hp := open_noPay hc e hm
  have hzR : z ≠ rightNeighbor e := by intro he; rw [← he,h.leader] at hl; contradiction
  refine ⟨hlt, ?_, ?_, ?_, ?_⟩
  · by_cases hzE : z = e
    · change (step x e z).leader = true
      rw [hzE,row_left,H.2.2.2,← hzE]; exact h.leader
    · rw [row_other x e z hzE hzR]; exact h.leader
  · by_cases hzE : z = e
    · change (step x e z).shield = true
      rw [hzE,row_left,H.2.2.1,← hzE]; exact h.shield
    · rw [row_other x e z hzE hzR]; exact h.shield
  · intro j hj; rw [mark_unchanged hn hc e _ hp]
    by_cases hJ : j < d
    · exact h.marks j hJ
    · have hh : j=d := by omega
      rw [hh]; exact hm
  · intro j hj
    by_cases ha : liftedSite z j = e
    · rw [ha,row_left]; exact H.1
    · by_cases hh : liftedSite z j = rightNeighbor e
      · rw [hh,row_right hn]; exact H.2.1
      · have hJ : j ≤ d := by
          by_cases h' : j=d+1
          · exact False.elim (hh (h'.symm ▸ hnv))
          · omega
        rw [row_other x e _ ha hh]; exact h.signals j hJ

/-- N1 with signal TWO starts a zero-length arc, at the responding
living leader itself. -/
theorem freshArc_newN1 {p c1 n : Nat} (hn : 4 ≤ n) (x : Config p c1 n) (e : Fin n)
    (hl : (x (rightNeighbor e)).leader = true)
    (hs : (x (rightNeighbor e)).signal = .two) :
    FreshArc (step x e) (rightNeighbor e) 0 := by
  have H := freshN1_physical (x e) (x (rightNeighbor e)) hl hs
  rw [← row_right hn] at H
  refine ⟨by omega,H.1,H.2.1, ?_, ?_⟩
  · intro j hj; omega
  · intro j hj
    have h : j=0 := by omega
    rw [h,liftedSite_zero]; exact H.2.2

private theorem newN0_shield {p c1 : Nat} (u v : Site p c1)
    (hi : tagOverwrite u = true) (hl : v.leader = false)
    (hm : u.mark = false) (hd : defect u v = false) (hv : v.bullet = .none) :
    (pairStep u v).1.shield = true := by
  have hMat : materialize u v = u := by simp [materialize,hl,hm,hd]
  have hInit : fireInitiator u = { u with bullet := .live, shield := true, signal := .zero } := by
    simp [fireInitiator, show (u.leader && !(u.signal == .zero)) = true from hi]
  have hln : (Bullet.live == Bullet.none) = false := rfl
  have hnn : (Bullet.none == Bullet.none) = true := rfl
  unfold pairStep stepPrefix native
  rw [hMat,hInit]
  cases hU : u.leader <;> cases hu : u.stock <;> cases hV : v.stock <;>
    simp [fireResponder, impact, followerBullet, pinned, payment, payer, patrolWrite,
      finishBirth, hm, hl, hv, hln, hnn, hV, Signal.max]

/-- N0 followed by transport to an empty ordinary responder starts an
arc of length one, anchored at that initiating leader. -/
theorem freshArc_newN0 {p c1 n : Nat} (hn : 4 ≤ n) {x : Config p c1 n} (hc : MCOV x) (e : Fin n)
    (hi : tagOverwrite (x e) = true) (hl : (x (rightNeighbor e)).leader = false)
    (hm : (x e).mark = false) (hd : defect (x e) (x (rightNeighbor e)) = false)
    (hv : (x (rightNeighbor e)).bullet = .none) :
    FreshArc (step x e) e 1 := by
  have H := freshN0_signals (x e) (x (rightNeighbor e)) hi hl hm hd hv
  have ho : (x e).leader = true := by cases h : (x e).leader <;> simp_all [tagOverwrite]
  have hLeader := (pair_geometric_fields (x e) (x (rightNeighbor e))).2.1.trans ho
  have hPay := open_noPay hc e hm
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · rw [row_left]; exact hLeader
  · rw [row_left]; exact newN0_shield _ _ hi hl hm hd hv
  · intro j hj
    have he : j=0 := by omega
    rw [he,liftedSite_zero,mark_unchanged hn hc e e hPay]; exact hm
  · intro j hj
    by_cases he : j=0
    · rw [he,liftedSite_zero,row_left]; exact H.1
    · have hh : j = 0+1 := by omega
      rw [hh,liftedSite_succ,liftedSite_zero,row_right hn]; exact H.2

private theorem freshArc_of_rootPeacefulAt {p c1 n : Nat} {x : Config p c1 n} {b : Fin n}
    (h : RootPeacefulAt x b) : ∃ z d, FreshArc x z d ∧ liftedSite z d = b := by
  obtain ⟨i,d,h⟩ := h
  simp only [plus_eq_lifted] at h
  exact ⟨rightNeighbor i,d,⟨h.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.2.1,h.2.2.2.2.2.2⟩,
    h.2.2.2.2.1⟩

/-- The physical tag observer preserves the particular origin witness of
an existing fresh survivor. Only its offset can increase, by exactly one
when the current carrier is the selected donor. -/
theorem freshArc_of_survival {p c1 n d : Nat} (hn : 4 ≤ n)
    {x : Config p c1 n} {z e b : Fin n} (hc : MCOV x) (h : FreshArc x z d)
    (hs : TaggedTrace.carrierStep x e (some (liftedSite z d)) = some b) :
    let d' := if e = liftedSite z d then d+1 else d
    FreshArc (step x e) z d' ∧ liftedSite z d' = b := by
  by_cases he : e = liftedSite z d
  · subst e
    obtain ⟨hb,ht⟩ := TaggedTrace.carrierStep_selected_survives x (liftedSite z d) b hs
    rw [if_pos rfl]
    exact ⟨freshArc_transfer hn hc h ht,(liftedSite_succ z d).trans hb.symm⟩
  · rw [if_neg he]
    exact ⟨freshArc_stationary hn hc h he,
      (TaggedTrace.carrierStep_not_selected_stays x e _ b (Ne.symm he) hs).symm⟩

end L4

namespace L4

def RootIndependentFreshMaskStep : Prop :=
  ∀ {p c1 n : Nat} (x : Config p c1 n) (tagged : Fin n → Prop) (e : Fin n),
    2≤p → 12≤c1 → 4≤n → MCOV x → COV x →
    (∀ b, tagged b → (x b).bullet=.live) →
    freshAt x tagged → freshAt (step x e) (nextTagMask x tagged e)

/-- Ring lift of the one-mark creation/retention/transport partition. -/
theorem rootIndependentFreshMaskStep_of_local
    (leftNever : ∀ {p c1} (u v : Site p c1), (pairStep u v).1.bullet ≠ .live)
    (rightCases : ∀ {p c1} (u v : Site p c1), (pairStep u v).2.bullet = .live →
      freshResponder u v = true ∨ tagTransfer u v = true ∨ tagResident u v = true)
    :
    RootIndependentFreshMaskStep := by
  intro p c1 n x tagged e _ _ hn hm hc _ hf b hb hbTag
  have hcov' := (EntranceCover.cover_closed hn x e ⟨hm,hc⟩).1
  by_cases he : b = e
  · subst b
    rw [row_left] at hb
    exact False.elim (leftNever _ _ hb)
  · by_cases hR : b = rightNeighbor e
    · subst b
      rw [row_right hn] at hb
      let v := rightNeighbor e
      have H (z : Fin n) (d : Nat) (h : FreshArc (step x e) z d)
          (heq : liftedSite z d = v) : RootPeacefulAt (step x e) v :=
        heq ▸ rootPeacefulAt_of_freshArc h hcov'
      rcases rightCases (x e) (x v) hb with hNew | hMove | hStay
      · rcases (freshResponder_iff _ _).mp hNew with ⟨hl,hs⟩ | ⟨hi,hl,hm',hd,hb'⟩
        · exact H v 0 (freshArc_newN1 hn x e hl hs) (liftedSite_zero v)
        · exact H e 1 (freshArc_newN0 hn hm e hi hl hm' hd hb') (by
            simpa [liftedSite_zero] using (liftedSite_succ e 0))
      · have ht : ¬ tagged e := fun ht =>
          hbTag ((nextTagMask_responder_iff hn x tagged e).mpr (Or.inl ⟨ht,hMove⟩))
        have hb' := ((tagTransfer_iff _ _).mp hMove).1
        obtain ⟨z,d,h,heq⟩ := freshArc_of_rootPeacefulAt (hf e hb' ht)
        have ht' : tagTransfer (x (liftedSite z d))
            (x (rightNeighbor (liftedSite z d))) = true := by simpa [heq] using hMove
        have hh := freshArc_transfer hn hm h ht'
        rw [heq] at hh
        exact H z (d+1) hh (by rw [liftedSite_succ,heq])
      · have ht : ¬ tagged v := fun ht =>
          hbTag ((nextTagMask_responder_iff hn x tagged e).mpr (Or.inr ⟨ht,hStay⟩))
        have hb' := ((tagResident_iff _ _).mp hStay).1
        obtain ⟨z,d,h,heq⟩ := freshArc_of_rootPeacefulAt (hf v hb' ht)
        have hg : e ≠ liftedSite z d := by rw [heq]; exact (rn_ne hn e).symm
        exact H z d (freshArc_stationary hn hm h hg) heq
    · have ht : ¬ tagged b := fun hyp =>
        hbTag ((nextTagMask_offPair_iff x tagged e b he hR).mpr hyp)
      have hb' : (x b).bullet = .live := by
        rwa [row_other x e b he hR] at hb
      obtain ⟨z,d,h,heq⟩ := freshArc_of_rootPeacefulAt (hf b hb' ht)
      have hg : e ≠ liftedSite z d := by rw [heq]; exact Ne.symm he
      exact heq ▸ rootPeacefulAt_of_freshArc (freshArc_stationary hn hm h hg) hcov'

end L4

namespace L4

/-- No position strictly after the fresh origin and within its arc is a
leader. The mark-free condition plus MCOV excludes every such root. -/
theorem FreshArc.interior_not_leader {p c1 n d : Nat} {x : Config p c1 n} {z : Fin n}
    (h : FreshArc x z d) (hc : MCOV x) (j : Nat) (hj : 0 < j) (hjd : j ≤ d) :
    (x (liftedSite z j)).leader = false := by
  cases j with
  | zero => omega
  | succ j =>
    rw [liftedSite_succ]
    exact (cover_ordinary_fields hc _ (h.marks j (by omega))).1

end L4

namespace L4

private theorem pair_bullets {p c1 : Nat} (u v : Site p c1) :
    let a := native (materialize u v) v
    (pairStep u v).1.bullet = a.1.bullet ∧
    ((pairStep u v).2.bullet = .live → a.2.bullet = .live) := by
  let a := native (materialize u v) v
  have hp (x y : Site p c1) :
      (payment x y).1.bullet = x.bullet ∧ (payment x y).2.bullet = y.bullet := by
    unfold payment; split
    · exact ⟨rfl,rfl⟩
    · split
      · exact ⟨rfl,rfl⟩
      · split <;> exact ⟨rfl,rfl⟩
  have hs (l r : Site p c1) (t : Patrol (2*c1)) :
      (finishBirth t.fire (patrolWrite l r t).1 (patrolWrite l r t).2).1.bullet = l.bullet ∧
      ((finishBirth t.fire (patrolWrite l r t).1 (patrolWrite l r t).2).2.bullet = .live →
        r.bullet = .live) := by
    unfold finishBirth
    split <;> simp [patrolWrite]
  exact ⟨(hs _ _ _).1.trans (hp a.1 a.2).1,fun h =>
    (hp a.1 a.2).2.symm ▸ (hs _ _ _).2 h⟩

/-- The selected initiator never retains a live bullet after N2/N4. -/
theorem pair_left_not_live {p c1 : Nat} (u v : Site p c1) :
    (pairStep u v).1.bullet ≠ .live := by
  have h := (pair_bullets u v).1
  rw [h]
  unfold native
  generalize fireInitiator (materialize u v) = a
  generalize fireResponder v = b
  cases hb : b.leader <;> cases hh : b.shield <;> cases hm : a.mark <;> cases hu : a.bullet <;>
    simp [impact,followerBullet,pinned,hb,hh,hm,hu,
      show (Bullet.none == Bullet.none) = true from rfl,
      show (Bullet.dummy == Bullet.none) = false from rfl,
      show (Bullet.live == Bullet.none) = false from rfl] <;>
    try (split <;> rfl)

end L4

namespace L4

private theorem leader_native_bullet {p c1 : Nat} (u v : Site p c1)
    (h : v.leader = true) :
    (native (materialize u v) v).2.bullet = (fireResponder v).bullet := by
  unfold native
  have hl : (fireResponder v).leader = true := by cases hs : v.signal <;> simp [fireResponder,h,hs]
  generalize fireInitiator (materialize u v) = a
  generalize fireResponder v = b at hl ⊢
  cases hs : b.shield <;> cases ha : a.bullet <;>
    simp [impact, followerBullet, hl, hs, ha,
      show (Bullet.dummy == Bullet.live) = false from rfl,
      show (Bullet.live == Bullet.live) = true from rfl,
      show (Bullet.none == Bullet.none) = true from rfl,
      show (Bullet.dummy == Bullet.none) = false from rfl,
      show (Bullet.live == Bullet.none) = false from rfl]

private theorem follower_native_bullet {p c1 : Nat} (u v : Site p c1)
    (h : v.leader = false) :
    let a := fireInitiator (materialize u v)
    (native (materialize u v) v).2.bullet = .live →
      v.bullet = .live ∨
      (v.bullet = .none ∧ a.bullet = .live ∧ a.mark = false) := by
  unfold native
  have hv : fireResponder v = v := by simp [fireResponder,h]
  rw [hv]
  generalize fireInitiator (materialize u v) = a
  dsimp only
  cases ha : a.mark <;> cases hA : a.bullet <;> cases hB : v.bullet <;>
    simp [impact,followerBullet,pinned,h,ha,hA,hB,
      show (Bullet.none == Bullet.none) = true from rfl,
      show (Bullet.dummy == Bullet.none) = false from rfl,
      show (Bullet.live == Bullet.none) = false from rfl]

/-- Exhaustive ancestry of a live responder: a fresh firing, a physically
transferred old donor, or the old resident that survived unchanged in identity. -/
theorem pair_right_live_cases {p c1 : Nat} (u v : Site p c1)
    (h : (pairStep u v).2.bullet = .live) :
      freshResponder u v = true ∨ tagTransfer u v = true ∨ tagResident u v = true := by
  have hn := (pair_bullets u v).2 h
  by_cases hl : v.leader = true
  · have hb := (leader_native_bullet u v hl).symm.trans hn
    cases hs : v.signal with
    | zero =>
      simp [fireResponder,hl,hs] at hb
      exact Or.inr (Or.inr ((tagResident_iff _ _).mpr ⟨hb,by
        simp [tagOverwrite,hs,show (Signal.zero == Signal.zero) = true from rfl],h⟩))
    | one => simp [fireResponder,hl,hs] at hb
    | two => exact Or.inl ((freshResponder_iff _ _).mpr (Or.inl ⟨hl,hs⟩))
  · have hl' := Bool.eq_false_iff.mpr hl
    rcases follower_native_bullet u v hl' hn with hb | ⟨hb,ha,hm⟩
    · exact Or.inr (Or.inr ((tagResident_iff _ _).mpr ⟨hb,by simp [tagOverwrite,hl'],h⟩))
    · have hmat : (materialize u v).mark = false := by
        unfold fireInitiator at hm
        split at hm <;> exact hm
      have hm' : u.mark = false := by
        by_cases hm1 : u.mark = true
        · simp [materialize,hm1] at hmat
        · exact Bool.eq_false_iff.mpr hm1
      have hd : defect u v = false := by
        by_cases hd1 : defect u v = true
        · simp [materialize,hl',hm',hd1] at hmat
        · exact Bool.eq_false_iff.mpr hd1
      have hme : materialize u v = u := by simp [materialize,hl',hm',hd]
      rw [hme] at ha
      by_cases ho : tagOverwrite u = true
      · exact Or.inl ((freshResponder_iff _ _).mpr (Or.inr ⟨ho,hl',hm',hd,hb⟩))
      · have ho' := Bool.eq_false_iff.mpr ho
        have hfi : fireInitiator u = u := by
          unfold fireInitiator
          rw [show (u.leader && !(u.signal == .zero)) = false from ho']
          rfl
        rw [hfi] at ha
        exact Or.inr (Or.inl ((tagTransfer_iff _ _).mpr ⟨ha,ho',hl',hm',hd,hb⟩))

theorem rootIndependentFreshMaskStep : RootIndependentFreshMaskStep :=
  rootIndependentFreshMaskStep_of_local pair_left_not_live pair_right_live_cases

theorem freshMaskStep_of_local
    (leftNever : ∀ {p c1} (u v : Site p c1), (pairStep u v).1.bullet ≠ .live)
    (rightCases : ∀ {p c1} (u v : Site p c1), (pairStep u v).2.bullet=.live →
      freshResponder u v=true ∨ tagTransfer u v=true ∨ tagResident u v=true) :
    FreshMaskStep := by
  intro p c1 n x tagged e hp hc hn _ hm hC hL hF
  exact rootIndependentFreshMaskStep_of_local leftNever rightCases x tagged e hp hc hn hm hC hL hF

/-- On all covered traces, every live bullet not among the inherited tags
is peaceful, irrespective of the times or presence of the other tags. -/
theorem freshMaskStep_literal : FreshMaskStep :=
  freshMaskStep_of_local pair_left_not_live pair_right_live_cases

/-- The literal peace interface for the L4 entrance theorem, with no
additional hypotheses beyond the covered cut present in its statement. -/
theorem freshPeaceAfterExtinction_literal : FreshPeaceAfterExtinction :=
  freshPeaceAfterExtinction_of_maskStep freshMaskStep_literal

end L4

