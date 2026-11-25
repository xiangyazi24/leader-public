import Leader.L4.RankFresh
import Leader.L4.TenureOrigins
import Leader.L4.RankPhysical

/-! Literal source initialization and paid-move epoch reset.
No claim about authentication of a complete return is assumed here. -/
namespace L4.FreshTimerEpoch

/-- From OFF at a pinned ghost, every old rail pair launches Ui, enters
I1, and cannot set the birth latch on this interaction. -/
theorem patrol_off_launch {Q : Nat} (l r : Rail) :
    let t := patrol true true false (.off : Source Q) l r
    t.source = .i1 ∧ t.left = .ui ∧ t.fire = false := by
  cases l <;> cases r <;> exact ⟨rfl,rfl,rfl⟩

/-- At the former head a paid shift disables PG. A non-OFF controller
always emits X at that former head; the later move groups cannot erase
this particular X on the same raw mark. -/
theorem patrol_paid_reset {Q : Nat} (s : Source Q) (l r : Rail) :
    let t := patrol false false false s l r
    t.source = .off ∧ t.fire = false ∧ (s ≠ .off → t.right = .x) := by
  have hpayload (l r : Rail) :
      (move false ⟨(.off : Source Q),l,r,false⟩).source = .off ∧
        (move false ⟨(.off : Source Q),l,r,false⟩).fire = false := by
    cases l <;> cases r <;> exact ⟨rfl,rfl⟩
  have hMove (l : Rail) : (move false ⟨(.off : Source Q),l,.x,false⟩).right = .x := by
    cases l <;> rfl
  have hPrep (l r : Rail) :
      launch (arrivals false false false ⟨(.off : Source Q),l,r,false⟩) =
        ⟨(.off : Source Q),l,r,false⟩ := by
    cases l <;> rfl
  have hbeq (t : Source Q) : (t == .off) = true ↔ t = .off := by
    cases t <;> (try change true = true ↔ _) <;> (try change false = true ↔ _) <;> simp
  by_cases ho : s = .off
  · subst s
    unfold patrol sourceGuard
    dsimp only
    rw [show ((Source.off : Source Q) == .off) = true from rfl]
    change (move false (launch (arrivals false false false ⟨.off,l,r,false⟩))).source = .off ∧
      (move false (launch (arrivals false false false ⟨.off,l,r,false⟩))).fire = false ∧
      ((.off : Source Q) ≠ .off →
        (move false (launch (arrivals false false false ⟨.off,l,r,false⟩))).right = .x)
    rw [hPrep]
    exact ⟨(hpayload l r).1,(hpayload l r).2,fun hn => (hn rfl).elim⟩
  · have he : (s == .off) = false := Bool.eq_false_iff.mpr (fun hh => ho ((hbeq s).mp hh))
    unfold patrol sourceGuard
    dsimp only
    rw [he]
    change (move false (launch (arrivals false false false ⟨.off,l,.x,false⟩))).source = .off ∧
      (move false (launch (arrivals false false false ⟨.off,l,.x,false⟩))).fire = false ∧
      (s ≠ .off →
        (move false (launch (arrivals false false false ⟨.off,l,.x,false⟩))).right = .x)
    rw [hPrep]
    exact ⟨(hpayload l .x).1,(hpayload l .x).2,fun _ => hMove l⟩

private theorem prefix_source {p c : Nat} (u v : Site p c) :
    (stepPrefix u v).2.source = v.source := by
  unfold stepPrefix native
  generalize hgen : impact (fireInitiator (materialize u v)) (fireResponder v) = a
  rcases a with ⟨al,ar⟩
  have hp (a b : Site p c) : (payment a b).2.source = b.source := by
    unfold payment
    split
    · rfl
    · split
      · rfl
      · split <;> rfl
  have hf (g : Bool) (a b : Site p c) : (followerBullet g a b).2.source = b.source := by
    unfold followerBullet
    split
    · split <;> rfl
    · rfl
  have hi (a b : Site p c) : (impact a b).2.source = b.source := by
    unfold impact
    split
    · split <;> rfl
    · rfl
  have hv : (fireResponder v).source = v.source := by
    unfold fireResponder
    split
    · cases v.signal <;> rfl
    · rfl
  have hh := congrArg (fun ab => ab.2.source) hgen
  exact (hp _ _).trans ((hf _ _ _).trans (hh.symm.trans ((hi _ _).trans hv)))

private theorem native_mark {p c : Nat} (u v : Site p c) :
    (native u v).1.mark = u.mark := by
  have ha : (fireInitiator u).mark = u.mark := by unfold fireInitiator; split <;> rfl
  unfold native
  generalize fireInitiator u = a at ha ⊢
  generalize fireResponder v = b
  have hi : (impact a b).1.mark = a.mark := by unfold impact; split <;> rfl
  generalize impact a b = ab at hi ⊢
  rcases ab with ⟨al,ar⟩
  have hf (g : Bool) : (followerBullet g al ar).1.mark = al.mark := by
    unfold followerBullet
    split
    · split <;> rfl
    · rfl
  exact (hf _).trans (hi.trans ha)

/-- Local OFF-launch condition after normalization/native/payment. -/
theorem pair_off_launch {p c : Nat} (u v : Site p c)
    (hm : (stepPrefix u v).1.mark = true)
    (hl : (stepPrefix u v).2.leader = false)
    (ho : v.source = .off) :
    (pairStep u v).2.source = .i1 ∧ (pairStep u v).1.rail = .ui ∧
      (pairStep u v).2.leader = false := by
  have hs := (prefix_source u v).trans ho
  unfold pairStep
  generalize stepPrefix u v = ab at hm hl hs ⊢
  rcases ab with ⟨a,b⟩
  dsimp only at hm hl hs ⊢
  have hh := patrol_off_launch (Q := 2*c) a.rail b.rail
  have hh' :
      (patrol true true false (.off : Source (2*c)) a.rail b.rail).source = .i1 ∧
      (patrol true true false (.off : Source (2*c)) a.rail b.rail).left = .ui ∧
      (patrol true true false (.off : Source (2*c)) a.rail b.rail).fire = false := hh
  simp [patrolWrite,finishBirth,pinned,hm,hl,hs,hh'.1,hh'.2.1,hh'.2.2]

/-- A genuine unpaid N2 death on a covered old leader is already the
fresh initialization launch. It cannot birth on this mark. -/
theorem unpaid_kill_launch {p c : Nat} (u v : Site p c)
    (hk : TenureOrigins.nativeKill u v) (ho : v.source = .off)
    (hp : geometricPay u v = false) :
    (pairStep u v).2.source = .i1 ∧ (pairStep u v).1.rail = .ui ∧
      (pairStep u v).2.leader = false := by
  have hmat : (materialize u v).mark = true := by simp [materialize,hk.1]
  let ab := native (materialize u v) v
  have hm : ab.1.mark = true := (native_mark _ _).trans hmat
  have hL : ab.2.leader = false := (TenureOrigins.native_loses_leader_iff u v hk.1).mpr hk
  have hP : payer ab.1 = false := by
    change (!ab.2.leader && ab.1.mark && payer ab.1) = false at hp
    simpa [hm,hL] using hp
  apply pair_off_launch u v _ _ ho
  · change (payment ab.1 ab.2).1.mark = true
    simp [payment,hm,hL,hP]
  · change (payment ab.1 ab.2).2.leader = false
    simp [payment,hm,hL,hP]

/-- Any literal P3, including one sharing an actual native death,
closes the old head's timer and cannot commit P5 at that head.
An active old source leaves a break at the vacated head. -/
theorem paid_pair_reset {p c : Nat} (u v : Site p c)
    (hp : geometricPay u v = true) :
    (pairStep u v).2.source = .off ∧ (pairStep u v).2.leader = false ∧
      (v.source ≠ .off → (pairStep u v).2.rail = .x) := by
  let ab := native (materialize u v) v
  change (!ab.2.leader && ab.1.mark && payer ab.1) = true at hp
  simp only [Bool.and_eq_true,Bool.not_eq_true'] at hp
  have hm : (stepPrefix u v).1.mark = false := by
    change (payment ab.1 ab.2).1.mark = false
    simp [payment,hp.1.1,hp.1.2,hp.2]
  have hl : (stepPrefix u v).2.leader = false := by
    change (payment ab.1 ab.2).2.leader = false
    simp [payment,hp.1.1,hp.1.2,hp.2]
  have hs := prefix_source u v
  unfold pairStep
  generalize stepPrefix u v = aff at hm hl hs ⊢
  rcases aff with ⟨a,b⟩
  dsimp only at hm hl hs ⊢
  have hh := patrol_paid_reset b.source a.rail b.rail
  have hh' :
      (patrol false false false b.source a.rail b.rail).source = .off ∧
      (patrol false false false b.source a.rail b.rail).fire = false ∧
      (b.source ≠ .off → (patrol false false false b.source a.rail b.rail).right = .x) := hh
  simpa [patrolWrite,finishBirth,pinned,hm,hl,hs] using And.intro
    (show (patrol false false false v.source a.rail b.rail).source = .off by simpa [hs] using hh'.1)
    (show v.source ≠ .off → (patrol false false false v.source a.rail b.rail).right = .x by
      simpa [hs] using hh'.2.2)

private theorem native_ghost {p c : Nat} (u v : Site p c)
    (h : v.leader = false) : (native u v).2.leader = false := by
  have hv : fireResponder v = v := by simp [fireResponder,h]
  unfold native
  rw [hv]
  generalize fireInitiator u = a
  have hi : impact a v = (a,v) := by simp [impact,h]
  rw [hi]
  dsimp only
  unfold followerBullet
  split
  · split <;> exact h
  · exact h

/-- First unpaid incoming service at a newly landed, OFF, marked ghost
launches initialization, even when its two rail slots were dirty. -/
theorem unpaid_ghost_launch {p c : Nat} (u v : Site p c)
    (hm : u.mark = true) (hl : v.leader = false) (ho : v.source = .off)
    (hp : geometricPay u v = false) :
    (pairStep u v).2.source = .i1 ∧ (pairStep u v).1.rail = .ui ∧
      (pairStep u v).2.leader = false := by
  have hmat : (materialize u v).mark = true := by simp [materialize,hm]
  let ab := native (materialize u v) v
  have hm' : ab.1.mark = true := (native_mark _ _).trans hmat
  have hl' : ab.2.leader = false := native_ghost _ _ hl
  have hP : payer ab.1 = false := by
    change (!ab.2.leader && ab.1.mark && payer ab.1) = false at hp
    simpa [hm',hl'] using hp
  apply pair_off_launch u v _ _ ho
  · change (payment ab.1 ab.2).1.mark = true
    simp [payment,hm',hl',hP]
  · change (payment ab.1 ab.2).2.leader = false
    simp [payment,hm',hl',hP]

private theorem right_ne {n : Nat} (hn : 4 ≤ n) (e : Fin n) : rightNeighbor e ≠ e := by
  intro h
  have he : liftedSite e 1 = liftedSite e 0 := by simpa [liftedSite_succ,liftedSite_zero] using h
  have hc := liftedSite_inj e (by omega : 1<n) (by omega : 0<n) he
  omega

private theorem double_right_ne {n : Nat} (hn : 4 ≤ n) (e : Fin n) :
    rightNeighbor (rightNeighbor e) ≠ e := by
  intro h
  have he : liftedSite e 2 = liftedSite e 0 := by simpa [liftedSite_succ,liftedSite_zero] using h
  have hc := liftedSite_inj e (by omega : 2<n) (by omega : 0<n) he
  omega

/-- On a nonmerging P3, the new head's source is OFF and its leader
bit is false. The physical interaction does not write that site:
COV/MCOV guarantee these bytes on the ordinary premark landing site. -/
theorem paid_landing_off {p c n : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (e : Fin n) (hm : MCOV x) (hc : COV x)
    (hp : geometricPay (x e) (x (rightNeighbor e)) = true)
    (hr : RankPhysical.retirement x e = false) :
    let w := rightNeighbor (rightNeighbor e)
    (step x e w).source = .off ∧ (step x e w).leader = false ∧
      (step x e (rightNeighbor e)).mark = true := by
  let z := rightNeighbor e
  let w := rightNeighbor z
  have hOld : (x z).mark = false := by
    unfold RankPhysical.retirement at hr
    simpa [hp,z] using hr
  have hOff : (x w).source = .off := by
    by_cases h : (x w).source = .off
    · exact h
    · have hh := (hc z h).2
      rw [hOld] at hh
      contradiction
  have hL : (x w).leader = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have hh := hm z (Or.inl h)
    rw [hOld] at hh
    contradiction
  have hStay : step x e w = x w := by
    have hne : w ≠ e := double_right_ne hn e
    have hnz : w ≠ z := right_ne hn z
    simp [step,hne,show w ≠ rightNeighbor e from hnz]
  have hM : (step x e z).mark = true := by
    rw [covered_step_mark hn x hm]
    simp [hp,z,right_ne hn e]
  exact ⟨(congrArg Site.source hStay).trans hOff,(congrArg Site.leader hStay).trans hL,hM⟩

/-- The separating Ui front advances across every inherited bit in an
ordinary pair. Only T or X remains behind it; an old Di or Dc is not
allowed to pass through the front. -/
theorem ui_crosses_dirty {Q : Nat} (l : Rail) :
    let t := patrol false false false (.off : Source Q) l .ui
    t.left = .ui ∧ t.right = (if l == .x then .x else .t) ∧
      t.source = .off ∧ t.fire = false := by
  cases l <;> exact ⟨rfl,rfl,rfl,rfl⟩

/-- At a fixed upstream root the designated Ui turns without moving
through the root; it is now the matching Di return. -/
theorem ui_turns_at_root {Q : Nat} (l : Rail) :
    let t := patrol true false true (.off : Source Q) l .ui
    t.right = .di ∧ t.source = .off ∧ t.fire = false := by
  cases l <;> exact ⟨rfl,rfl,rfl⟩

theorem di_clean_return {Q : Nat} (r : Rail) (h : r = .e ∨ r = .t) :
    let t := patrol false false false (.off : Source Q) .di r
    t.left = .e ∧ t.right = .di ∧ t.source = .off ∧ t.fire = false := by
  rcases h with rfl|rfl <;> exact ⟨rfl,rfl,rfl,rfl⟩

/-- A break may destroy a genuine return, but does not fabricate one. -/
theorem di_meets_break {Q : Nat} :
    let t := patrol false false false (.off : Source Q) .di .x
    t.left = .e ∧ t.right = .x ∧ t.source = .off ∧ t.fire = false :=
  ⟨rfl,rfl,rfl,rfl⟩

/-- A1 accepts Di and immediately launches count zero on the same
service. The prerequisite that Di is the current genuine return belongs
to the epoch-global front/clearance invariant. -/
theorem a1_accepts_and_launches {Q : Nat} (hQ : 0 < Q) (r : Rail) :
    let t := patrol true true false (.i1 : Source Q) .di r
    t.source = .await ⟨0,hQ⟩ ∧ t.left = .uc ∧ t.fire = false := by
  have hc : firstCount Q = .count ⟨0,hQ⟩ := by simp [firstCount,hQ]
  cases r <;> simp [patrol,sourceGuard,arrivals,launch,turn,move,hc,
    show ((Source.i1 : Source Q) == .off) = false from rfl,
    show ((Source.i1 : Source Q) == .i1) = true from rfl,
    show (Rail.di == Rail.x) = false from rfl,
    show (Rail.di == Rail.di) = true from rfl]

end L4.FreshTimerEpoch
