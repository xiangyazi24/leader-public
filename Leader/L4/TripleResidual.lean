import Leader.L4.RankPhysical
import Leader.L4.TenureOrigins
import Leader.L4.RankSupplier

/-! Literal endpoint of the triple trial: stop on the first actual
native death anywhere or the first root retirement. -/
namespace L4.TripleResidual

structure Obs (p c n : Nat) where
  config : Config p c n
  stopped : Bool

def init {p c n : Nat} (x : Config p c n) : Obs p c n := ⟨x,false⟩

def death {p c n : Nat} (x : Config p c n) (e : Fin n) : Bool :=
  let a := x e
  let b := x (rightNeighbor e)
  b.leader && ((fireInitiator a).bullet == .live) && !(fireResponder b).shield

theorem death_iff_nativeKill {p c n : Nat} (x : Config p c n) (e : Fin n) :
    death x e = true ↔ TenureOrigins.nativeKill (x e) (x (rightNeighbor e)) := by
  have hb (b : Bullet) : (b == .live) = true ↔ b = .live := by cases b <;> decide
  simp [death,TenureOrigins.nativeKill,Bool.and_eq_true,hb,and_assoc]

def event {p c n : Nat} (x : Config p c n) (e : Fin n) : Bool :=
  death x e || RankPhysical.retirement x e

def advance {p c n : Nat} (s : Obs p c n) (e : Fin n) : Obs p c n :=
  if s.stopped then s else ⟨step s.config e,event s.config e⟩

def track {p c n : Nat} (s : Obs p c n) (w : List (Fin n)) : Obs p c n :=
  w.foldl advance s

/-- The first two successor gaps are ambient, not merely relative to
a named subset. At rank two the second successor is the first root
after exactly one lap. -/
structure Start {p c n : Nat} (x : Config p c n) (v : Fin n) (a b : Nat) : Prop where
  first_leader : (x v).leader = true
  second_leader : (x (liftedSite v (a+1))).leader = true
  third_leader : (x (liftedSite (liftedSite v (a+1)) (b+1))).leader = true
  first_gap : FirstMark x v a
  second_gap : FirstMark x (liftedSite v (a+1)) b
  at_least_two : a+1 < n
  arity : a+b+2 < n ∨ (a+b+2 = n ∧ RankPhysical.rank x = 2)

theorem event_iff_death_or_retirement {p c n : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (e : Fin n) (hm : MCOV x) :
    event x e = true ↔ TenureOrigins.nativeKill (x e) (x (rightNeighbor e)) ∨
      RankPhysical.rank (step x e) < RankPhysical.rank x := by
  simp [event, Bool.or_eq_true, death_iff_nativeKill,
    RankPhysical.retirement_iff_rank_drop hn x e hm]

/-- A selected live impact is an actual death on a covered old leader,
not simply an increase in an auxiliary danger flag. -/
theorem death_iff_leader_loss {p c n : Nat}
    (x : Config p c n) (e : Fin n) (he : rightNeighbor e ≠ e)
    (h : COV x) (hl : (x (rightNeighbor e)).leader = true) :
    death x e = true ↔ ((step x e) (rightNeighbor e)).leader = false := by
  rw [death_iff_nativeKill, TenureOrigins.covered_ring_leader_loss_iff x e he h hl]

/-- Useful exact one-edge restriction: a poised live donor (including
an adjacent N0 launch) kills a responding leader when N1 sees one,
or when it sees zero and the leader was already unshielded. In
particular a responder holding two is not covered by this claim. -/
theorem vulnerable_mark_stops {p c n : Nat} (x : Config p c n) (e : Fin n)
    (hL : (x (rightNeighbor e)).leader = true)
    (hB : (fireInitiator (x e)).bullet = .live)
    (hV : (x (rightNeighbor e)).signal = .one ∨
      ((x (rightNeighbor e)).signal = .zero ∧ (x (rightNeighbor e)).shield = false)) :
    (advance (init x) e).stopped = true := by
  have hS : (fireResponder (x (rightNeighbor e))).shield = false := by
    rcases hV with h | ⟨h,hs⟩
    · simp [fireResponder,hL,h]
    · simp [fireResponder,hL,h,hs]
  have hD := (death_iff_nativeKill x e).mpr ⟨hL,hB,hS⟩
  simp [advance,init,event,hD]

theorem poised_live {p c : Nat} (u : Site p c)
    (h : u.bullet = .live ∨ (u.leader = true ∧ u.signal ≠ .zero)) :
    (fireInitiator u).bullet = .live := by
  rcases h with h | ⟨hL,hS⟩
  · unfold fireInitiator; split <;> first | rfl | exact h
  · cases s : u.signal
    · exact (hS s).elim
    · simp [fireInitiator,hL,s,show (Signal.one == Signal.zero) = false from rfl]
    · simp [fireInitiator,hL,s,show (Signal.two == Signal.zero) = false from rfl]

/-- Effective edge in the controlled comparison; it is not substituted
for the physical scheduler in the residual clock statement. -/
def controlledEdge {n : Nat} (ready : Bool) (left right raw : Fin n) : Fin n :=
  if ready && raw == right then left else raw

theorem controlled_ready_fibers {n : Nat} (left right raw : Fin n)
    (_h : left ≠ right) :
    (controlledEdge true left right raw = left ↔ raw = left ∨ raw = right) ∧
      (∀ e, e ≠ left → (controlledEdge true left right raw = e ↔ raw = e ∧ e ≠ right)) := by
  unfold controlledEdge
  simp only [Bool.true_and,beq_iff_eq]
  by_cases hr : raw = right
  · subst raw
    refine ⟨by simp,?_⟩
    intro e he
    simp [Ne.symm he]; exact Eq.symm
  · refine ⟨by simp [hr],?_⟩
    intro e _
    by_cases hE : raw = e
    · subst e; simp [hr]
    · simp [hr,hE]

/-- In the one-edge target sector the relevant controlled left hit is
already terminal if the attacker is poised and the target is not in a
live shield phase (zero signal unshielded, or one-signal dummy firing). -/
theorem controlled_vulnerable_mark_stops {p c n : Nat}
    (x : Config p c n) (left right raw : Fin n)
    (hL : (x (rightNeighbor left)).leader = true)
    (hB : (x left).bullet = .live ∨ ((x left).leader = true ∧ (x left).signal ≠ .zero))
    (hV : (x (rightNeighbor left)).signal = .one ∨
      ((x (rightNeighbor left)).signal = .zero ∧ (x (rightNeighbor left)).shield = false))
    (hF : raw = left ∨ raw = right) (h : left ≠ right) :
    (advance (init x) (controlledEdge true left right raw)).stopped = true := by
  rw [(controlled_ready_fibers left right raw h).1.mpr hF]
  exact vulnerable_mark_stops x left hL (poised_live _ hB) hV

private theorem right_ne {n : Nat} (hn : 4 ≤ n) (e : Fin n) : rightNeighbor e ≠ e := by
  intro h
  have he : liftedSite e 1 = liftedSite e 0 := by
    simpa [liftedSite_succ,liftedSite_zero] using h
  have he' := liftedSite_inj e (by omega : 1<n) (by omega : 0<n) he
  omega

theorem no_event_preserves_leader {p c n : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (e v : Fin n) (hc : COV x)
    (h : event x e = false) (hL : (x v).leader = true) :
    (step x e v).leader = true := by
  by_cases hv : v = e
  · subst v
    simpa [step] using (pair_geometric_fields (x e) (x (rightNeighbor e))).2.1.trans hL
  · by_cases hr : v = rightNeighbor e
    · subst v
      have hD : death x e = false := (Bool.or_eq_false_iff.mp h).1
      cases hh : (step x e (rightNeighbor e)).leader
      · exfalso
        exact (Bool.eq_false_iff.mp hD) ((death_iff_leader_loss x e (right_ne hn e) hc hL).mpr hh)
      · rfl
    · simpa [step,hv,hr] using hL

theorem no_event_rank_unchanged {p c n : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (e : Fin n) (hm : MCOV x) (h : event x e = false) :
    RankPhysical.rank (step x e) = RankPhysical.rank x := by
  have hr : RankPhysical.retirement x e = false := (Bool.or_eq_false_iff.mp h).2
  have hs := RankPhysical.rank_step hn x e hm
  simpa [hr] using hs

/-- Actual covered service cannot insert a root in an open sector between
two surviving consecutive leaders. Both endpoints keep their sites. -/
theorem no_event_sector {p c n d : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (e v : Fin n) (hm : MCOV x) (hc : COV x)
    (h : event x e = false) (hS : (x v).leader = true)
    (hT : (x (liftedSite v (d+1))).leader = true)
    (hF : FirstMark x v d) (hD : d+1<n) :
    FirstMark (step x e) v d := by
  have hr : RankPhysical.retirement x e = false := (Bool.or_eq_false_iff.mp h).2
  have hh := RankSupplier.firstMark_after_supplier_step hn x v e hm hF hD hS
    (no_event_preserves_leader hn x e v hc h hS) hr
  have hG : ((e == liftedSite v d) &&
      geometricPay (x e) (x (rightNeighbor e))) = false := by
    apply Bool.eq_false_iff.mpr
    intro hp
    simp only [Bool.and_eq_true] at hp
    obtain ⟨he,hpay⟩ := hp
    have he' := beq_iff_eq.mp he
    have hL := no_event_preserves_leader hn x e (liftedSite v (d+1)) hc h hT
    rw [liftedSite_succ,← he'] at hL
    have hV := TaggedTrace.geometricPay_responder_nonleader _ _ hpay
    have ho : (step x e (rightNeighbor e)).leader = false := by
      simpa [step,right_ne hn e] using hV
    rw [hL] at ho
    contradiction
  simp only [hG,Bool.toNat_false,Nat.add_zero] at hh
  exact hh.1

theorem no_event_preserves_start {p c n a b : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (e v : Fin n) (hm : MCOV x) (hc : COV x)
    (h : event x e = false) (hs : Start x v a b) :
    Start (step x e) v a b := by
  have hB : b+1<n := by
    rcases hs.arity with ha | ⟨ha,_⟩ <;> omega
  refine ⟨no_event_preserves_leader hn x e _ hc h hs.first_leader,
    no_event_preserves_leader hn x e _ hc h hs.second_leader,
    no_event_preserves_leader hn x e _ hc h hs.third_leader,
    no_event_sector hn x e _ hm hc h hs.first_leader hs.second_leader hs.first_gap hs.at_least_two,
    no_event_sector hn x e _ hm hc h hs.second_leader hs.third_leader hs.second_gap hB,
    hs.at_least_two,?_⟩
  rw [no_event_rank_unchanged hn x e hm h]
  exact hs.arity

private theorem ordinary_prefix_suffix {p c : Nat} (u v : Site p c)
    (hM : (stepPrefix u v).1.mark = false)
    (hL : (stepPrefix u v).2.leader = false) :
    (pairStep u v).1.bullet = (stepPrefix u v).1.bullet ∧
      (pairStep u v).2.bullet = (stepPrefix u v).2.bullet ∧
      (pairStep u v).1.signal = (stepPrefix u v).1.signal ∧
      (pairStep u v).2.signal = (stepPrefix u v).2.signal := by
  unfold pairStep
  generalize stepPrefix u v = ab at hM hL ⊢
  rcases ab with ⟨a,b⟩
  dsimp only at hM hL ⊢
  simp [patrolWrite, finishBirth,pinned,hM,hL]

private theorem pay_payload {p c : Nat} (a b : Site p c)
    (hm : a.mark = false) (hl : b.leader = false) :
    (payment a b).1.mark = false ∧ (payment a b).2.leader = false ∧
    (payment a b).1.bullet = a.bullet ∧ (payment a b).2.bullet = b.bullet ∧
    (payment a b).1.signal = a.signal ∧ (payment a b).2.signal = b.signal := by
  unfold payment
  simp only [hl,Bool.false_eq_true,if_false,hm,Bool.not_false,Bool.true_and,Bool.false_and]
  split
  · exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  · exact ⟨hm,hl,rfl,rfl,rfl,rfl⟩

/-- Ordinary N4 clears the destination even in a collision, in which
case the physical resident continues the proof-front sweep. -/
theorem ordinary_front_step {p c : Nat} (u v : Site p c)
    (hm : u.mark = false) (hr : v.residue = nextResidue u.residue)
    (hl : v.leader = false)
    (hN : u.signal = .zero) (hF : u.bullet ≠ .none) :
    (pairStep u v).1.bullet = .none ∧
      (pairStep u v).2.bullet = (if v.bullet == .none then u.bullet else v.bullet) ∧
      (pairStep u v).1.signal = .zero ∧ (pairStep u v).2.signal = .zero := by
  have ht : (stepPrefix u v).1.mark = false ∧ (stepPrefix u v).2.leader = false ∧
      (stepPrefix u v).1.bullet = .none ∧
      (stepPrefix u v).2.bullet = (if v.bullet == .none then u.bullet else v.bullet) ∧
      (stepPrefix u v).1.signal = .zero ∧ (stepPrefix u v).2.signal = .zero := by
    have hmat : materialize u v = u := by simp [materialize,defect,hm,hr,hl]
    have hinit : fireInitiator u = u := by
      simp [fireInitiator,hN,show (Signal.zero == Signal.zero) = true from rfl]
    have hresp : fireResponder v = v := by simp [fireResponder,hl]
    have himp : impact u v = (u,v) := by simp [impact,hl]
    have hb : (u.bullet == .none) = false := by
      cases hb' : u.bullet
      · contradiction
      · rfl
      · rfl
    unfold stepPrefix native
    rw [hmat,hinit,hresp,himp]
    simp only [pinned,hl,hm,Bool.not_false,Bool.true_and,Bool.false_eq_true,if_false,
      followerBullet,hb,if_true,hN,Signal.max]
    exact pay_payload _ _ rfl rfl
  have hs := ordinary_prefix_suffix u v ht.1 ht.2.1
  exact ⟨hs.1.trans ht.2.2.1,hs.2.1.trans ht.2.2.2.1,
    hs.2.2.1.trans ht.2.2.2.2.1,hs.2.2.2.trans ht.2.2.2.2.2⟩

/-- A return step copies one backward through an ordinary zero-signal
and empty sender. Only the donor signal changes. -/
theorem ordinary_return_step {p c : Nat} (u v : Site p c)
    (hm : u.mark = false) (hr : v.residue = nextResidue u.residue)
    (hl : v.leader = false) (hu : u.signal = .zero) (hv : v.signal = .one)
    (hb : u.bullet = .none) :
    (pairStep u v).1.signal = .one ∧
      (pairStep u v).2.signal = .one ∧
      (pairStep u v).1.bullet = .none ∧ (pairStep u v).2.bullet = v.bullet := by
  have ht : (stepPrefix u v).1.mark = false ∧ (stepPrefix u v).2.leader = false ∧
      (stepPrefix u v).1.bullet = .none ∧ (stepPrefix u v).2.bullet = v.bullet ∧
      (stepPrefix u v).1.signal = .one ∧ (stepPrefix u v).2.signal = .one := by
    have hmat : materialize u v = u := by simp [materialize,defect,hm,hr,hl]
    have hinit : fireInitiator u = u := by
      simp [fireInitiator,hu,show (Signal.zero == Signal.zero) = true from rfl]
    have hresp : fireResponder v = v := by simp [fireResponder,hl]
    have hImp : impact u v = (u,v) := by simp [impact,hl]
    unfold stepPrefix native
    rw [hmat,hinit,hresp,hImp]
    have hh := pay_payload {u with signal := .one} v hm hl
    simpa [pinned,hm,hl,hb,hu,hv,followerBullet,Signal.max,
      show (Bullet.none == Bullet.none) = true from rfl] using
        (show (payment {u with signal := .one} v).1.mark = false ∧
          (payment {u with signal := .one} v).2.leader = false ∧
          (payment {u with signal := .one} v).1.bullet = .none ∧
          (payment {u with signal := .one} v).2.bullet = v.bullet ∧
          (payment {u with signal := .one} v).1.signal = .one ∧
          (payment {u with signal := .one} v).2.signal = .one from
            ⟨hh.1,hh.2.1,hh.2.2.1.trans hb,hh.2.2.2.1,hh.2.2.2.2.1,hh.2.2.2.2.2.trans hv⟩)
  have hs := ordinary_prefix_suffix u v ht.1 ht.2.1
  exact ⟨hs.2.2.1.trans ht.2.2.2.2.1,hs.2.2.2.trans ht.2.2.2.2.2,
    hs.1.trans ht.2.2.1,hs.2.1.trans ht.2.2.2.1⟩

/-- The n=6 distinction between consecutive leaders and
consecutive root identities. Initial conditions use the exact tape. -/
def hiddenGhost6 : Config 5 12 6 := fun i =>
  { residue := if i.val = 1 ∨ i.val = 4 then 1 else if i.val = 5 then 2 else 0
    mark := i.val == 5 || i.val == 1 || i.val == 2
    leader := i.val == 0 || i.val == 3
    bullet := .none
    shield := i.val == 0 || i.val == 3
    signal := if i.val = 0 then .one else .zero
    stock := false
    source := .off
    rail := .e }

theorem hiddenGhost6_replay :
    (∀ i : Fin 6, (hiddenGhost6 i).leader = true ↔ i = 0 ∨ i = 3) ∧
    (hiddenGhost6 1).mark = true ∧
    (step hiddenGhost6 0 1).bullet = .live ∧
    (step hiddenGhost6 0 1).stock = true ∧
    (run hiddenGhost6 [0,1] 1).bullet = .none ∧
    (run hiddenGhost6 [0,1] 1).signal = .two ∧
    (run hiddenGhost6 [0,1] 0).leader = true ∧
    (run hiddenGhost6 [0,1] 3).leader = true ∧
    RankPhysical.retirement (step hiddenGhost6 0) 1 = true := by decide

/-- Still open: build the literal controlled zero/one-signal clock and
its restart argument. This endpoint is on the original IID scheduler;
an edge redirection used inside a comparison is not the transition. -/
def ConcreteTripleClock : Prop :=
  ∃ A : Nat, ∀ {p c n : Nat} (x : Config p c n) (v : Fin n) (a b : Nat),
    2 ≤ p → 12 ≤ c → 4 ≤ n → QuietEntrance x →
    Start x v a b →
    IIDExpectedHittingTimeAtMost advance (fun s => s.stopped = true)
      (init x) (A*n^2)

/-- The coefficient with the two *physical* distances.
The shape witness indexes incoming bonds, so those distances are a+1,b+1. -/
def ConcreteTripleSharpClock : Prop :=
  ∀ {p c n : Nat} (x : Config p c n) (v : Fin n) (a b : Nat),
    2 ≤ p → 12 ≤ c → 4 ≤ n → QuietEntrance x →
    Start x v a b →
    IIDExpectedHittingTimeAtMost advance (fun s => s.stopped = true)
      (init x) (4096*n*(a+b+2))

theorem concreteTripleClock_of_sharp (h : ConcreteTripleSharpClock) :
    ConcreteTripleClock := by
  refine ⟨4096,?_⟩
  intro p c n x v a b hp hc hn hQ hS t
  have hD : a+b+2 ≤ n := by rcases hS.arity with hr | ⟨hr,_⟩ <;> omega
  have hbound : 4096*n*(a+b+2) ≤ 4096*n^2 := by
    calc
      _ ≤ 4096*n*n := Nat.mul_le_mul_left _ hD
      _ = _ := by rw [Nat.pow_two,Nat.mul_assoc]
  exact Nat.le_trans (h x v a b hp hc hn hQ hS t) (Nat.mul_le_mul_right _ hbound)

end L4.TripleResidual
