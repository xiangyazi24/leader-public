import Leader.L4.WindowA0RoutedRelease
import Leader.L4.WindowA0Ledger
import Leader.L4.WindowA0StockDrain
import Leader.L4.RestartGeometry

namespace L4.WindowA0GapOne
open FixedResidual WindowA0ReleaseCredit TripleRenewal

def ask {n : Nat} (i : Fin n) (k : Fin 3) : Fin n :=
  if k.val=0 then GGStage.incoming i 0 else i

abbrev State (p c n : Nat) := WindowA0Ledger.State p c n × Phase

/-- The probability monitor always executes the actual scoped raw mark.
It credits a designated exit first, before classifying guard competitors. -/
def next {p c n : Nat} (S : WindowA0Ledger.Scope n) (i : Fin n)
    (z : State p c n) (e : Fin n) : State p c n :=
  let y := WindowA0Ledger.next S z.1 e
  (y, match z.2 with
    | .success => .success
    | .failed => .failed
    | .waiting k =>
      if y.reason.isSome then .success
      else if e=ask i k then
        if k.val=0 then .waiting 1 else .success
      else if e ∈ labelsAt i then .failed else .waiting k)

theorem ask_mem {n : Nat} (hn : 4≤n) (i : Fin n) (k : Fin 3) :
    ask i k ∈ labelsAt i := by
  unfold ask
  split
  · exact (script_labels_mem hn i).1
  · exact (script_labels_mem hn i).2.1

def frame {p c n : Nat} (hn : 4≤n) (S : WindowA0Ledger.Scope n)
    (i : Fin n) (z : State p c n) (k : Fin 3) (hz : z.2=.waiting k) :
    Frame (next S i) Prod.snd (labelsAt i) z k := by
  refine ⟨ask i k,ask_mem hn i k,?_,?_⟩
  · have hmax : 6 * score (.waiting k) ≤ 216 := by
      have H : k.val+1≤3 := by have := k.isLt; omega
      simpa [score,Nat.pow_succ,Nat.mul_comm] using
        Nat.pow_le_pow_right (by decide : 0<6) H
    by_cases he : (WindowA0Ledger.next S z.1 (ask i k)).reason.isSome=true
    · simpa [next,hz,he,score] using hmax
    · by_cases hk : k.val=0
      · simp [next,hz,he,hk,score]
      · simpa [next,hz,he,hk,score] using hmax
  · intro e hOut
    have he : e≠ask i k := fun h => hOut (h ▸ ask_mem hn i k)
    by_cases h : (WindowA0Ledger.next S z.1 e).reason.isSome=true <;>
      simp [next,hz,h,he,hOut]

theorem short_release_mass {p c n : Nat} (hn : 4≤n) (S : WindowA0Ledger.Scope n)
    (i : Fin n) (z : WindowA0Ledger.State p c n) (t : Nat) :
    216 * terminalMass (next S i) (fun y => done y.2) (fun y => y.2=.failed) t (z,.waiting 0)
      ≤ 215*n^t := by
  have H := finite_credit (next S i) Prod.snd (labelsAt i) (by simp) (fun _ => True)
    (fun _ _ _ _ _ => trivial) (fun y k _ => frame hn S i y k) t (z,.waiting 0) trivial
  change _ + 1*n^t ≤ 216*n^t at H
  rw [Nat.one_mul] at H
  omega

/-- The second request accepts the current leg, and on a nonterminal
acceptance launches the next leg on the exact same physical pair. -/
theorem accept_init {p c : Nat} (u v : Site p c)
    (hc : 0<2*c) (hm : u.mark=true) (hL : u.leader=false)
    (hR : v.leader=false) (hs : u.stock=false) (hr : u.rail=.di) (hq : v.source=.i1) :
    (pairStep u v).1.rail=.uc ∧
    (pairStep u v).2.source=.await ⟨0,hc⟩ ∧ (pairStep u v).2.leader=false := by
  have H := WindowA0Release.release_door_row u v (.init : Trip (2*c)) hm hL hR hs hr hq
  simpa [waitingFor,inward,door_init_accept hc] using H

theorem accept_count {p c : Nat} (u v : Site p c) (k : Fin (2*c))
    (hk : k.val+1<2*c) (hm : u.mark=true) (hL : u.leader=false)
    (hR : v.leader=false) (hs : u.stock=false) (hr : u.rail=.dc) (hq : v.source=.await k) :
    (pairStep u v).1.rail=.uc ∧
    (pairStep u v).2.source=.await ⟨k.val+1,hk⟩ ∧ (pairStep u v).2.leader=false := by
  have H := WindowA0Release.release_door_row u v (.count k) hm hL hR hs hr hq
  simpa [waitingFor,inward,door_count_accept k hk] using H

theorem accept_final {p c : Nat} (u v : Site p c) (k : Fin (2*c))
    (hk : ¬k.val+1<2*c) (hm : u.mark=true) (hL : u.leader=false)
    (hR : v.leader=false) (hs : u.stock=false) (hr : u.rail=.dc) (hq : v.source=.await k) :
    (pairStep u v).1.rail=.e ∧
    (pairStep u v).2.source=.off ∧ (pairStep u v).2.leader=true := by
  have H := WindowA0Release.release_door_row u v (.count k) hm hL hR hs hr hq
  simpa [waitingFor,inward,door_terminal_accept k hk] using H

/-- Unpaid first request turns the authentic gap-one worker. It may
already give a tracked birth; otherwise the same physical socket
still has its mark and its empty donor byte for the second request. -/
theorem turn_unpaid {p c : Nat} (a b : Site p c) (q : Trip (2*c))
    (ha : a.mark=true) (hLa : a.leader=false) (hSa : a.stock=false)
    (hb : b.mark=true) (hLb : b.leader=false) (hSb : b.stock=false)
    (hr : b.rail=outward q) :
    let z := (pairStep a b).2
    z.leader=true ∨ (z.leader=false ∧ z.mark=true ∧ z.stock=false ∧ z.rail=inward q) := by
  let z := (pairStep a b).2
  by_cases hl : z.leader=true
  · exact Or.inl hl
  · have hPay : geometricPay a b=false := by
      apply Bool.eq_false_iff.mpr
      intro h
      have H := RearTrace.geometricPay_ready _ _ h
      simp [payer,hLa,hSa] at H
    have hMark := covered_pair_marks a b (fun _ => ha)
    rw [if_neg (show geometricPay a b ≠ true by simp [hPay])] at hMark
    have hTurn := (WindowA0Release.pinned_turn_row a b q ha hLa hLb hSa hr).1
    have hs := (RearFrontStock.marked_right_stock a b ha).trans hSb
    refine Or.inr ⟨Bool.eq_false_iff.mpr hl,?_,hs,hTurn⟩
    exact hMark.2.trans hb

/-- Exact first-hit transfer with no hidden leader/payer assumption:
a paid gap-one predecessor mark is a retirement; otherwise the
unpaid row arms the matching second service or births the top. -/
theorem paid_or_turn {p c : Nat} (a b : Site p c) (q : Trip (2*c))
    (ha : a.mark=true) (hLa : a.leader=false)
    (hb : b.mark=true) (hLb : b.leader=false) (hSb : b.stock=false)
    (hr : b.rail=outward q) :
    (geometricPay a b=true ∧ b.mark=true) ∨
      (let z := (pairStep a b).2
       z.leader=true ∨ (z.leader=false ∧ z.mark=true ∧ z.stock=false ∧ z.rail=inward q)) := by
  by_cases hp : geometricPay a b=true
  · exact .inl ⟨hp,hb⟩
  · have hs : a.stock=false := by
      apply Bool.eq_false_iff.mpr
      intro h
      exact hp (WindowA0StockDrain.marked_ghost_stock_pays a b ha hLb h)
    exact .inr (turn_unpaid a b q ha hLa hs hb hLb hSb hr)

def farLeft {n : Nat} (i : Fin n) : Fin n := liftedSite i (n-2)

theorem guards_eq {n : Nat} (i : Fin n) :
    labelsAt i = WindowA0Return.guardLabels (farLeft i) := by
  simp [labelsAt,WindowA0Return.guardLabels,List.range_succ, farLeft,
    RestartGeometry.lift_add]

theorem two_labels {n : Nat} (hn : 4≤n) (i : Fin n) :
    ask i 0=liftedSite (farLeft i) 1 ∧ ask i 1=liftedSite (farLeft i) 2 := by
  constructor
  · simp [ask,farLeft,GGStage.incoming,RestartGeometry.lift_add,
      show n-2+1=0+n-1 by omega]
  · simp [ask,farLeft,RestartGeometry.lift_add,show n-2+2=n by omega,liftedSite_full]

/-- Outside labels preserve every socket needed for either live phase,
although the actual scoped ledger still executes the physical mark. -/
theorem off_guard_frame {p c n : Nat} (S : WindowA0Ledger.Scope n) (i : Fin n)
    (z : State p c n) (e : Fin n) (h : e ∉ labelsAt i) :
    WindowA0Release.Agree (farLeft i) (next S i z e).1.ledger.config z.1.ledger.config := by
  change WindowA0Release.Agree (farLeft i)
    (WindowA0Ledger.next S z.1 e).ledger.config z.1.ledger.config
  rw [WindowA0Ledger.physical_step]
  rw [guards_eq] at h
  exact WindowA0Release.outside_agrees z.1.ledger.config _ e h

private theorem ring_distinct {n : Nat} (hn : 4≤n) (e : Fin n) : rightNeighbor e≠e := by
  intro h
  have he : liftedSite e 1=liftedSite e 0 := by simpa [liftedSite_succ,liftedSite_zero] using h
  have := liftedSite_inj e (show 1<n by omega) (show 0<n by omega) he
  omega

open SevenTagCharge WindowLocal WindowA0Route in
theorem selected_birth_exits {p c n : Nat} (hn : 4≤n) (S : WindowA0Ledger.Scope n)
    (x : WindowA0Ledger.State p c n) (e a : Fin n) (hr : x.reason=none)
    (hm : MCOV x.ledger.config) (hc : COV x.ledger.config) (hs : x.ledger.slots e=some a)
    (hBirth : birthAt x.ledger.config e=true)
    (ha : a=S.iTag ∨ a=S.jTag) :
    WindowA0Ledger.done (WindowA0Ledger.next S x e) := by
  have H := target_birth_result hn S.group [] x.ledger e a hm hc hs hBirth
  apply (WindowA0Ledger.physical_exit_iff S x e hr).mpr
  intro hk
  have h := (keep_iff S.group S.iTag S.jTag x.ledger e).mp hk
  rcases ha with hh|hh
  · rw [hh,h.1] at H
    cases H.1
  · rw [hh,h.2] at H
    cases H.1

/-- A stock-free living predecessor is still a payer. It cannot
occur on a retained first gap-one request: the paid marked target
would retire its selected incoming tag. -/
theorem marked_leader_pays {p c : Nat} (a b : Site p c)
    (hm : a.mark=true) (hL : a.leader=true) (hg : b.leader=false) :
    geometricPay a b=true := by
  have mat : materialize a b=a := by cases a; simp_all [materialize]
  have ha : (fireInitiator a).mark=true ∧ (fireInitiator a).leader=true := by
    unfold fireInitiator
    split <;> exact ⟨hm,hL⟩
  unfold geometricPay native
  rw [mat,show fireResponder b=b by simp [fireResponder,hg]]
  have imp (q : Site p c) : impact q b=(q,b) := by simp [impact,hg]
  rw [imp]
  generalize fireInitiator a = q at ha ⊢
  simp only [pinned,ha.1,hg,Bool.not_false,Bool.and_true]
  cases hb : !(q.bullet == .none) <;> simp [followerBullet,hb,ha.1,hg,payer,ha.2]

/-- A genuine gap-one entry has a marked predecessor and an
empty marked worker, with the selected original tags at the two doors.
If the first request does not exit, the same two authenticated slots
are retained and the literal worker is now inward. -/
theorem first_request_authenticates {p c n : Nat} (hn : 4≤n) (S : WindowA0Ledger.Scope n)
    (x : WindowA0Ledger.State p c n) (i : Fin n) (q : Trip (2*c))
    (hI : x.iSlot=GGStage.incoming i 0) (hJ : x.jSlot=i) (hr : x.reason=none)
    (hm : MCOV x.ledger.config) (hc : COV x.ledger.config)
    (ht : SevenTagCharge.Covers x.ledger.config x.ledger.slots)
    (hi : x.ledger.slots x.iSlot=some S.iTag) (hj : x.ledger.slots x.jSlot=some S.jTag)
    (hg : (x.ledger.config i).leader=false)
    (hs : (x.ledger.config i).stock=false) (hu : (x.ledger.config i).rail=outward q)
    (hNo : ¬ WindowA0Ledger.done (WindowA0Ledger.next S x x.iSlot)) :
    let y := WindowA0Ledger.next S x x.iSlot
    y.iSlot=x.iSlot ∧ y.jSlot=x.jSlot ∧
      (y.ledger.config i).leader=false ∧ (y.ledger.config i).mark=true ∧
      (y.ledger.config i).stock=false ∧ (y.ledger.config i).rail=inward q ∧
      y.ledger.config (rightNeighbor i)=x.ledger.config (rightNeighbor i) := by
  let e := x.iSlot
  let X := x.ledger.config
  let y := WindowA0Ledger.next S x e
  have he : rightNeighbor e=i := by change rightNeighbor x.iSlot=i; rw [hI,GGStage.incoming_right,liftedSite_zero]
  have hmarkI : (X e).mark=true := by simpa [e,X,hi] using (ht e).symm
  have hmarkJ : (X i).mark=true := by
    have H := (ht x.jSlot).symm
    rw [hj,hJ] at H
    exact H
  have hkeep : WindowA0Route.routeTwo S.group S.iTag S.jTag x.ledger e=.keep := by
    apply Classical.byContradiction
    exact fun h => hNo ((WindowA0Ledger.physical_exit_iff S x e hr).mpr h)
  have hLoss := WindowA0Route.empty_group_loss_of_two_keep x.ledger S.group S.iTag S.jTag e hkeep
  have hret := WindowScopedSupplier.tracked_no_retirement_of_group_keep S.group x.ledger e
    S.iTag S.iIn hi hLoss
  have hpay : geometricPay (X e) (X (rightNeighbor e))=false := by
    change (geometricPay (X e) (X (rightNeighbor e)) && (X (rightNeighbor e)).mark)=false at hret
    rwa [he,hmarkJ,Bool.and_true,←he] at hret
  have heq : step X e i=(pairStep (X e) (X i)).2 := by
    rw [←he]
    simp [step,ring_distinct hn e]
  have hL : (y.ledger.config i).leader=false := by
    apply Bool.eq_false_iff.mpr
    intro H
    have hb : WindowLocal.birthAt X e=true := by
      change (y.ledger.config i).leader=true at H
      have Hy : y.ledger.config=step X e := congrArg SevenTagCharge.Ledger.config
        (WindowA0Ledger.physical_step S x e)
      rw [Hy] at H
      change (X i).leader=false at hg
      simp [WindowLocal.birthAt,he,hg,H]
    exact hNo (selected_birth_exits hn S x e S.iTag hr hm hc hi hb (.inl rfl))
  have hl : (X e).leader=false := by
    apply Bool.eq_false_iff.mpr
    intro hL
    have hP := marked_leader_pays (X e) (X i) hmarkI hL hg
    rw [he,hP] at hpay
    contradiction
  have hrow := paid_or_turn (X e) (X i) q hmarkI hl hmarkJ hg hs hu
  have H := hrow.resolve_left (fun H => by
    have hh := hpay
    rw [he,H.1] at hh
    cases hh)
  have hy : y.ledger.config=step X e := congrArg SevenTagCharge.Ledger.config
    (WindowA0Ledger.physical_step S x e)
  have hrow := H.resolve_left (fun hh => by
    have T := hL
    rw [hy,heq,hh] at T
    cases T)
  have fresh : rightNeighbor i≠e := by
    intro bad
    have h2 : liftedSite e 2=liftedSite e 0 := by
      rw [show (2:Nat)=1+1 from rfl,liftedSite_succ,liftedSite_succ,liftedSite_zero,he,bad]
    have := liftedSite_inj e (show 2<n by omega) (show 0<n by omega) h2
    omega
  change geometricPay (x.ledger.config x.iSlot) (x.ledger.config (rightNeighbor x.iSlot))=false at hpay
  refine ⟨?_,?_,hL,?_,?_,?_,?_⟩
  · change y.iSlot=x.iSlot
    have nh : ¬WindowFourHeadTrace.moves x.ledger x.iSlot x.iSlot := fun H => by
      have G : geometricPay (x.ledger.config x.iSlot) (x.ledger.config (rightNeighbor x.iSlot))=true := H.2
      rw [hpay] at G
      cases G
    simp only [y,e,WindowA0Ledger.next,hr,show WindowA0Route.routeTwo S.group S.iTag S.jTag x.ledger x.iSlot=.keep from hkeep,
      if_true,WindowFourHeadTrace.landing,if_neg nh]
  · change y.jSlot=x.jSlot
    have nh : ¬WindowFourHeadTrace.moves x.ledger x.iSlot x.jSlot := fun H => by
      have G : geometricPay (x.ledger.config x.iSlot) (x.ledger.config (rightNeighbor x.iSlot))=true := H.2
      rw [hpay] at G
      cases G
    simp only [y,e,WindowA0Ledger.next,hr,show WindowA0Route.routeTwo S.group S.iTag S.jTag x.ledger x.iSlot=.keep from hkeep,
      if_true,WindowFourHeadTrace.landing,if_neg nh]
  · rw [hy,heq]; exact hrow.2.1
  · rw [hy,heq]; exact hrow.2.2.1
  · rw [hy,heq]; exact hrow.2.2.2
  · rw [hy]; simp [step,he,fresh,ring_distinct hn i,X]

/-- The second guard request is literally the door pair. Its FIRE bit
implies the scoped J-birth exit, while a continuing request retains the
new same-mark outward launch given by the serviceDoor table. -/
theorem second_request_authenticates {p c n : Nat} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (x : WindowA0Ledger.State p c n) (i : Fin n) (q : Trip (2*c))
    (hr : x.reason=none) (hm : MCOV x.ledger.config) (hc : COV x.ledger.config)
    (hj : x.ledger.slots i=some S.jTag) (hM : (x.ledger.config i).mark=true)
    (hI : (x.ledger.config i).leader=false) (hJ : (x.ledger.config (rightNeighbor i)).leader=false)
    (hS : (x.ledger.config i).stock=false) (hR : (x.ledger.config i).rail=inward q)
    (hW : (x.ledger.config (rightNeighbor i)).source=waitingFor q) :
    let y := WindowA0Ledger.next S x i
    let a := serviceDoor (waitingFor q) (inward q)
    (y.ledger.config i).rail=a.left ∧
      (y.ledger.config (rightNeighbor i)).source=(if a.fire then .off else a.source) ∧
      (y.ledger.config (rightNeighbor i)).leader=a.fire ∧
      (a.fire=true → WindowA0Ledger.done y) := by
  let X := x.ledger.config
  let y := WindowA0Ledger.next S x i
  let a := serviceDoor (waitingFor q) (inward q)
  have hy : y.ledger.config=step X i := congrArg SevenTagCharge.Ledger.config
    (WindowA0Ledger.physical_step S x i)
  have H := WindowA0Release.release_door_row (X i) (X (rightNeighbor i)) q hM hI hJ hS hR hW
  have yL : (y.ledger.config (rightNeighbor i)).leader=a.fire := by
    rw [hy]
    simpa [step,ring_distinct hn i] using H.2.2
  refine ⟨?_,?_,yL,?_⟩
  · change (y.ledger.config i).rail=a.left
    rw [hy]; simpa [step] using H.1
  · change (y.ledger.config (rightNeighbor i)).source=(if a.fire then .off else a.source)
    rw [hy]; simpa [step,ring_distinct hn i] using H.2.1
  · intro hf
    change a.fire=true at hf
    have H' := yL
    rw [hy,hf] at H'
    have hb : WindowLocal.birthAt X i=true := by
      change (X (rightNeighbor i)).leader=false at hJ
      simp [WindowLocal.birthAt,hJ,H']
    exact selected_birth_exits hn S x i S.jTag hr hm hc hj hb (.inr rfl)

end L4.WindowA0GapOne
