import Leader.L4.RankFresh
import Leader.L4.SupplierPause

/-! # The protected separator on the actual stopped successor tracker -/

namespace L4.RankSupplier

def Protected {p c n : Nat} (v : Fin n) (s : Obs p c n) : Prop :=
  Live v s ∧ RankFresh.Corridor s.config v s.donor

/-- The supplier is still living and shielded immediately after each
live premark, including the victim-birth or retirement service. -/
theorem protected_supplier_on_mark {p c n : Nat} (hn : 4 ≤ n)
    (v e : Fin n) (s : Obs p c n) (h : Protected v s) :
    ((step s.config e) v).leader = true ∧ ((step s.config e) v).shield = true ∧
       ((step s.config e) v).signal ≠ .one :=
  RankFresh.corridor_supplier_step hn s.config v e h.1.2.1 h.2

theorem protected_step {p c n : Nat} (hn : 4 ≤ n) (v e : Fin n)
    (s : Obs p c n) (h : Protected v s) (hs : (advance v s e).stopped = false) :
    Protected v (advance v s e) := by
  have hl := live_step hn v e s h.1 hs
  have he := (liveAdvance_fields v e s h.1.1 hs).1
  have hp := protected_supplier_on_mark hn v e s h
  have hf := RankFresh.corridor_separator_step hn s.config v e h.1.2.1 h.2
  rw [← he] at hf hp
  obtain ⟨j,hj,hF,hclean⟩ := hf
  exact ⟨hl, ⟨hl.2.2.2.2.1,hl.2.2.2.2.2,hl.2.2.2.1,hp.1,hp.2.1,
    ⟨j,Nat.le_trans hj (donor_mono_step v e s),hF,hclean⟩⟩⟩

theorem protected_track {p c n : Nat} (hn : 4 ≤ n) (v : Fin n)
    (s : Obs p c n) (w : List (Fin n)) (h : Protected v s)
    (hs : (track v s w).stopped = false) :
    Protected v (track v s w) := by
  induction w generalizing s with
  | nil => exact h
  | cons e w ih =>
    let t := advance v s e
    have ht : t.stopped = false := by
      cases hT : t.stopped
      · rfl
      · change (track v t w).stopped = false at hs
        rw [stopped_stays v t w hT,hT] at hs
        contradiction
    exact ih t (protected_step hn v e s h ht) hs

/-- Initialize the repaired separator after a physical kill with no
merger. The caller supplies the actual source of that killing bullet,
its clean strict prefix, and the source's shield on the killing mark.
The old donor, not the new ghost predecessor, receives signal two. -/
theorem protected_after_kill_prefix {p c n d : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (v : Fin n) (hm : MCOV x) (hc : COV x)
    (hF : FirstMark x v d) (hcap : d+1<n) (hL : (x v).leader = true)
    (hOld : (x (liftedSite v (d+1))).leader = true)
    (hKill : (step x (liftedSite v d) (liftedSite v (d+1))).leader = false)
    (hShield : (step x (liftedSite v d) v).shield = true)
    (hQuiet : ∀ i : Nat, i<d → (x (liftedSite v i)).signal ≠ .one)
    (hNoRetire : RankPhysical.retirement x (liftedSite v d) = false) :
    let e := liftedSite v d
    let pay := geometricPay (x e) (x (rightNeighbor e))
    Protected v (init (step x e) (d+pay.toNat)) := by
  let a := liftedSite v
  let e := a d
  let y := step x e
  let pay := geometricPay (x e) (x (rightNeighbor e))
  have he : rightNeighbor e = a (d+1) := (liftedSite_succ v d).symm
  have hne : a (d+1) ≠ e := fun hh =>
    (by omega : d+1 ≠ d) (liftedSite_inj v hcap (by omega) hh)
  have hL' : (y v).leader = true := by
    by_cases h : d=0
    · have hE : e = v := by change liftedSite v d = v; simp [h,liftedSite_zero]
      simpa [y,step,hE] using (pair_geometric_fields (x v) (x (rightNeighbor v))).2.1.trans hL
    · have he' : v ≠ e := by
        intro hh
        have heq : a 0 = a d := (liftedSite_zero v).trans hh
        have := liftedSite_inj v (by omega : 0<n) (by omega : d<n) heq
        omega
      have he'' : v ≠ rightNeighbor e := by
        intro hh
        have heq : a 0 = a (d+1) := (liftedSite_zero v).trans (hh.trans he)
        have := liftedSite_inj v (by omega : 0<n) hcap heq
        omega
      simpa [y,step,he',he''] using hL
  have hRet : (geometricPay (x e) (x (rightNeighbor e)) && (x (rightNeighbor e)).mark) = false :=
    hNoRetire
  have hStep := firstMark_after_supplier_step hn x v e hm hF hcap hL hL' hRet
  have hStep' : FirstMark y v (d+pay.toNat) ∧ d+pay.toNat+1<n := by
    change FirstMark y v (d+((e == a d) && pay).toNat) ∧
      d+((e == a d) && pay).toNat+1<n at hStep
    simpa only [show e = a d from rfl,beq_self_eq_true,Bool.true_and] using hStep
  have hGhost : (y (a (d+pay.toNat+1))).leader = false := by
    by_cases hp : pay = true
    · have hCap : d+2<n := by
        have hh := hStep'.2
        rw [hp] at hh
        exact hh
      have he' : a (d+2) ≠ e := fun hh =>
        (by omega : d+2 ≠ d) (liftedSite_inj v hCap (by omega) hh)
      have he'' : a (d+2) ≠ rightNeighbor e := by
        rw [he]; intro hh
        exact (by omega : d+2 ≠ d+1) (liftedSite_inj v hCap hcap hh)
      have hNot : (x (a (d+2))).leader = false := by
        apply Bool.eq_false_iff.mpr
        intro hh
        have hh' : (x (rightNeighbor e)).mark = true := hm _ (Or.inl
          (by rw [he,← liftedSite_succ]; exact hh))
        change (pay && (x (rightNeighbor e)).mark) = false at hRet
        simp [hp,hh'] at hRet
      rw [hp]
      simpa [y,step,he',he''] using hNot
    · have hpf := Bool.eq_false_iff.mpr hp
      rw [hpf]
      exact hKill
  have hOff : (x (rightNeighbor e)).source = .off := by
    cases hh : (x (rightNeighbor e)).source
    · rfl
    all_goals
      exfalso
      have hx := hc e (by rw [hh]; intro h; contradiction)
      rw [he] at hx
      exact Bool.noConfusion (hx.1.symm.trans hOld)
  have hKillPair : (pairStep (x e) (x (rightNeighbor e))).2.leader = false := by
    change (step x e (a (d+1))).leader = false at hKill
    rw [← he] at hKill
    have hh : rightNeighbor e ≠ e := he.symm ▸ hne
    simpa [step,hh] using hKill
  have hTwo : (y e).signal = .two := by
    have hh := (RankFresh.covered_kill_feedback (x e) (x (rightNeighbor e))
      (he.symm ▸ hOld) hOff hKillPair).1
    simpa [y,step] using hh
  have hSep : ∃ j : Nat, j≤d+pay.toNat ∧ RankFresh.Frontier (y (a j)) ∧
      ∀ i : Nat, i≤j → (y (a i)).signal ≠ .one := by
    refine ⟨d,by omega,Or.inl hTwo,?_⟩
    intro i hi
    by_cases hi' : i=d
    · subst i; change (y e).signal ≠ .one
      rw [hTwo]; decide
    · have hX : a i ≠ e := fun hh => hi' (liftedSite_inj v (by omega) (by omega) hh)
      have hY : a i ≠ rightNeighbor e := by
        rw [he]; intro hh
        have := liftedSite_inj v (by omega : i<n) hcap hh
        omega
      simpa [y,step,hX,hY] using hQuiet i (by omega)
  have hm' := mcov_step hn x hm e
  exact ⟨live_init y v hm' hL' hGhost hStep'.1 hStep'.2,
    ⟨hStep'.1,hStep'.2,hGhost,hL',hShield,hSep⟩⟩

theorem fresh_firing_shields {p c : Nat} (u v : Site p c) (h : tagOverwrite u = true) :
    (pairStep u v).1.leader = u.leader ∧ (pairStep u v).1.shield = true := by
  let a := fireInitiator (materialize u v)
  let b := fireResponder v
  let t := impact a b
  let w := followerBullet (pinned t.1 t.2) t.1 t.2
  have hA : a.leader = u.leader ∧ a.shield = true := by
    have hM : (materialize u v).leader = u.leader ∧
        (materialize u v).signal = u.signal := by
      unfold materialize
      split <;> exact ⟨rfl,rfl⟩
    have hTrue : ((materialize u v).leader && !((materialize u v).signal == .zero)) = true := by
      rw [hM.1,hM.2]
      exact h
    dsimp [a]
    unfold fireInitiator
    rw [if_pos hTrue]
    exact ⟨hM.1,rfl⟩
  have hT : t.1.leader = u.leader ∧ t.1.shield = true := by
    dsimp only [t]
    unfold impact
    split
    · split <;> exact hA
    · exact hA
  have hW : w.1.leader = u.leader ∧ w.1.shield = true := by
    dsimp only [w]
    unfold followerBullet
    split
    · split <;> exact hT
    · exact hT
  have hpre : (stepPrefix u v).1.leader = u.leader ∧ (stepPrefix u v).1.shield = true := by
    let emitted := if w.2.leader then Signal.one
      else if pinned t.1 t.2 then Signal.two else w.2.signal
    change (payment { w.1 with signal := w.1.signal.max emitted } w.2).1.leader = u.leader ∧
      (payment { w.1 with signal := w.1.signal.max emitted } w.2).1.shield = true
    unfold payment
    split
    · exact hW
    · split
      · exact hW
      · split <;> exact hW
  unfold pairStep
  generalize hX : stepPrefix u v = q at hpre ⊢
  cases q with
  | mk l r =>
    dsimp [patrolWrite,finishBirth] at *
    split <;> exact hpre

/-- At a covered peaceful restart, every actual nonretiring kill
initializes a protected fixed-supplier stage, whether its attack was a
fresh N0 or a physically older bullet from a shielded source. -/
theorem peaceful_kill_starts_protected {p c n : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (e : Fin n) (hQuiet : QuietEntrance x)
    (hOld : (x (rightNeighbor e)).leader = true)
    (hKill : (step x e (rightNeighbor e)).leader = false)
    (hNoRetire : RankPhysical.retirement x e = false) :
    ∃ v : Fin n, ∃ d : Nat, e = liftedSite v d ∧
      Protected v (init (step x e) (d+(geometricPay (x e) (x (rightNeighbor e))).toNat)) := by
  have hne : rightNeighbor e ≠ e := by
    intro he
    have he' : liftedSite e 1 = liftedSite e 0 := by
      simpa [liftedSite_succ,liftedSite_zero] using he
    have := liftedSite_inj e (by omega : 1<n) (by omega : 0<n) he'
    omega
  have hk := (TenureOrigins.covered_ring_leader_loss_iff x e hne hQuiet.2.1 hOld).mp hKill
  by_cases hFire : tagOverwrite (x e) = true
  · have hl : (x e).leader = true := by
      have h := hFire
      simp only [tagOverwrite,Bool.and_eq_true] at h
      exact h.1
    have h0 : FirstMark x e 0 := by
      refine ⟨by omega,?_,by omega⟩
      rw [liftedSite_zero]
      exact hQuiet.1 e (Or.inl hOld)
    have he : liftedSite e (0+1) = rightNeighbor e := by rw [liftedSite_succ,liftedSite_zero]
    have hs : (step x e e).shield = true := by simp [step,(fresh_firing_shields _ _ hFire).2]
    refine ⟨e,0,(liftedSite_zero e).symm,?_⟩
    simpa only [liftedSite_zero] using
      protected_after_kill_prefix hn x e hQuiet.1 hQuiet.2.1 h0 (by omega) hl
        (he.symm ▸ hOld) (by simpa [liftedSite_zero,he] using hKill)
        (by simpa only [liftedSite_zero] using hs) (by omega)
        (by simpa only [liftedSite_zero] using hNoRetire)
  · have hlive : (x e).bullet = .live := by
      have h := hk.2.1
      have hh : ((x e).leader && !((x e).signal == .zero)) ≠ true := hFire
      simpa only [fireInitiator,if_neg hh] using h
    obtain ⟨incoming,d,hd,hm,hL,hShield,he,hNoMark,hS⟩ := hQuiet.2.2.2 e hlive
    let v := rightNeighbor incoming
    have he' : liftedSite v d = e := he
    have htarget : liftedSite v (d+1) = rightNeighbor e := by rw [liftedSite_succ,he']
    have hF : FirstMark x v d := by
      refine ⟨hd,?_,?_⟩
      · rw [he']; exact hQuiet.1 e (Or.inl hOld)
      · intro j hj ht
        have hh := hNoMark j hj
        change (x (liftedSite v j)).mark = false at hh
        rw [hh] at ht
        contradiction
    have hGap : d+1<n := by
      by_cases hg : d+1<n
      · exact hg
      · exfalso
        have hn' : d+1=n := by omega
        have hEq : rightNeighbor e = v := by rw [← htarget, hn', liftedSite_full]
        have hzero : (x v).signal = .zero := by
          have hh := hS 0 (by omega)
          change (x (liftedSite v 0)).signal = .zero at hh
          simpa [liftedSite_zero] using hh
        have hy := (RankFresh.supplier_incoming (x e) (x (rightNeighbor e)) hOld
          (hEq.symm ▸ hShield)
          (by rw [hEq,hzero]; decide)).1
        have hno : (step x e (rightNeighbor e)).leader = true := by simp [step,hne,hy]
        exact Bool.noConfusion (hno.symm.trans hKill)
    have hs : (step x e v).shield = true := by
      by_cases heq : v = e
      · simp [step,heq,(RankFresh.outgoing_leader_shield (x e) (x (rightNeighbor e))
          (heq ▸ hShield)).2]
      · have hdne : v ≠ rightNeighbor e := by
          intro hh
          have ht : liftedSite v 0 = liftedSite v (d+1) :=
             (liftedSite_zero v).trans (hh.trans htarget.symm)
          have := liftedSite_inj v (by omega : 0<n) hGap ht
          omega
        simpa [step,heq,hdne] using hShield
    refine ⟨v,d,he'.symm,?_⟩
    have hh := protected_after_kill_prefix hn x v hQuiet.1 hQuiet.2.1 hF hGap hL
      (htarget.symm ▸ hOld) (by rw [he',htarget]; exact hKill)
      (by rwa [he']) (fun i hi => by
        have hez := hS i (by omega)
        change (x (liftedSite v i)).signal = .zero at hez
        rw [hez]; decide)
      (by rwa [he'])
    simpa only [he'] using hh

end L4.RankSupplier

