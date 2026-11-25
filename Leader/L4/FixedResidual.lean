import Leader.L4.GGTiming
import Leader.L4.Barrier
import Leader.L4.TaggedGeometry

/-! Literal fixed-corridor transitions. Rail slots are indexed from the
upstream top to the downstream door. The two ports may share a physical
mark in the sole-root case; the projections do not require distinctness. -/
namespace L4.FixedResidual
open L4

inductive Trip (Q : Nat) where
  | init
  | count (k : Fin Q)

def waitingFor {Q : Nat} : Trip Q → Source Q
  | .init => .i1
  | .count k => .await k

def outward {Q : Nat} : Trip Q → Rail
  | .init => .ui
  | .count _ => .uc

def inward {Q : Nat} : Trip Q → Rail
  | .init => .di
  | .count _ => .dc

def topRail : Rail → Rail
  | .ui => .di
  | .uc => .dc
  | .t => .e
  | r => r

private theorem arrival_right {Q : Nat} (r g l : Bool) (a : Patrol Q) :
    (arrivals r g l a).right = a.right := by
  unfold arrivals
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split
        · split <;> rfl
        · split
          · rfl
          · split <;> rfl

private theorem launch_right {Q : Nat} (a : Patrol Q) :
    (launch a).right = a.right := by
  unfold launch
  split <;> rfl

/-- A fixed root's top projection is independent of its source and left
rail, so its potentially concurrent own patrol does not alter this turn.
The selected top service must still be in the covered static geometry. -/
theorem top_exact {Q : Nat} (g l : Bool) (s : Source Q) (a b : Rail)
    (h : g = true ∨ s = .off) :
    (patrol true g l s a b).right = topRail b := by
  have hS : (sourceGuard g (⟨s,a,b,false⟩ : Patrol Q)).right = b := by
    rcases h with hg | hs
    · subst g
      unfold sourceGuard
      simp only [Bool.not_true,Bool.false_eq_true,if_false]
      split <;> rfl
    · subst s
      cases g <;> rfl
  unfold patrol
  rw [show ∀ z : Patrol Q, move true z = z from fun _ => rfl]
  have hT (z : Patrol Q) : (turn true z).right = topRail z.right := by
    cases hr : z.right <;> simp [turn,topRail,hr]
  rw [hT,launch_right,arrival_right,hS]

/-- An ordinary responder cannot inject X or a worker; its source is OFF.
Its full timer row reduces to the literal M rules. -/
theorem body_exact {Q : Nat} (a b : Rail) :
    patrol false false false (Source.off : Source Q) a b =
      move false ⟨.off,a,b,false⟩ := by
  cases a <;> cases b <;> rfl

/-- Clean outward progress on an ordinary bond; this is a single hit. -/
theorem body_outward {Q : Nat} (q : Trip Q) :
    patrol false false false (.off : Source Q) .e (outward q) =
      ⟨.off,outward q,.t,false⟩ := by
  cases q <;> rfl

/-- Clean return progress on an ordinary bond; no allocation or reset. -/
theorem body_return {Q : Nat} (q : Trip Q) :
    patrol false false false (.off : Source Q) (inward q) .t =
      ⟨.off,.e,inward q,false⟩ := by
  cases q <;> rfl

def serviceDoor {Q : Nat} (s : Source Q) (a : Rail) : Patrol Q :=
  patrol true true false s a .e

private def eraseRight {Q : Nat} (z : Patrol Q) : Patrol Q :=
  { z with right := .e }

private theorem erase_turn {Q : Nat} (z : Patrol Q) :
    eraseRight (turn true z) = eraseRight z := by
  cases hr : z.right <;> simp [turn,eraseRight,hr]

private theorem erase_launch {Q : Nat} (z : Patrol Q) :
    eraseRight (launch z) = launch (eraseRight z) := by
  unfold launch
  simp only [eraseRight]
  split <;> rfl

private theorem erase_arrivals {Q : Nat} (r g l : Bool) (z : Patrol Q) :
    eraseRight (arrivals r g l z) = arrivals r g l (eraseRight z) := by
  unfold arrivals
  simp only [eraseRight]
  split
  · rename_i hz
    simp only [hz,if_true]
  · rename_i hz
    simp only [Bool.false_eq_true,hz,if_false]
    split
    · rename_i hx
      simp only [hx,if_true]
    · rename_i hx
      simp only [Bool.false_eq_true,hx,if_false]
      split
      · rename_i hy
        simp only [hy,if_true]
      · rename_i hy
        simp only [Bool.false_eq_true,hy,if_false]
        split
        · split <;> rfl
        · split
          · rename_i hw
            simp only [hw,if_true]
          · rename_i hw
            simp only [Bool.false_eq_true,hw,if_false]
            split
            · rename_i ht
              simp only [ht,if_true]
            · rename_i ht
              simp only [Bool.false_eq_true,ht,if_false]

private theorem erase_guard {Q : Nat} (z : Patrol Q) :
    eraseRight (sourceGuard true z) = sourceGuard true (eraseRight z) := by
  unfold sourceGuard
  simp only [eraseRight,Bool.not_true,Bool.false_eq_true,if_false]
  split
  · rename_i hz
    simp only [hz,if_true]
  · rename_i hz
    simp only [Bool.false_eq_true,hz,if_false]

/-- The door projection ignores the source site's outgoing rail.
Consequently a simultaneous top turn at the same physical bond is
consistent with this projection. -/
theorem door_exact {Q : Nat} (s : Source Q) (a b : Rail) :
    let x := patrol true true false s a b
    let y := serviceDoor s a
    x.source = y.source ∧ x.left = y.left ∧ x.fire = y.fire := by
  have he : eraseRight (patrol true true false s a b) =
      eraseRight (serviceDoor s a) := by
    unfold patrol serviceDoor
    simp only [patrol]
    change eraseRight (turn true _) = eraseRight (turn true _)
    rw [erase_turn,erase_turn,erase_launch,erase_launch,erase_arrivals,erase_arrivals,
      erase_guard,erase_guard]
    rfl
  refine ⟨?_,?_,?_⟩
  · have h := congrArg Patrol.source he
    exact h
  · have h := congrArg Patrol.left he
    exact h
  · have h := congrArg Patrol.fire he
    exact h

/-- A completed outward launch is I1/Ui immediately, not a terminal I0
cut after the selected door service. -/
theorem door_init {Q : Nat} :
    serviceDoor (Source.off : Source Q) .e = ⟨.i1,.ui,.e,false⟩ := rfl

theorem door_wait_trail {Q : Nat} (q : Trip Q) :
    serviceDoor (waitingFor q) .t = ⟨waitingFor q,.t,.e,false⟩ := by
  cases q <;> rfl

theorem door_wait_outward {Q : Nat} (q : Trip Q) :
    serviceDoor (waitingFor q) (outward q) =
      ⟨waitingFor q,outward q,.e,false⟩ := by
  cases q <;> rfl

/-- INIT acceptance launches count zero immediately in the same row. -/
theorem door_init_accept {Q : Nat} (h : 0 < Q) :
    serviceDoor (.i1 : Source Q) .di = ⟨.await ⟨0,h⟩,.uc,.e,false⟩ := by
  simp [serviceDoor,patrol,sourceGuard,arrivals,firstCount,h,launch,turn,move]
  rfl

/-- Nonterminal COUNT acceptance launches the next count immediately. -/
theorem door_count_accept {Q : Nat} (k : Fin Q) (h : k.val+1 < Q) :
    serviceDoor (.await k) .dc = ⟨.await ⟨k.val+1,h⟩,.uc,.e,false⟩ := by
  have h₁ : (Source.await k == Source.off) = false := rfl
  have h₂ : (Source.await k == Source.i1) = false := rfl
  have h₃ : (Rail.dc == Rail.x) = false := rfl
  have h₄ : (Rail.dc == Rail.di) = false := rfl
  simp [serviceDoor,patrol,sourceGuard,arrivals,h,launch,turn,move,h₁,h₂,h₃,h₄]

/-- Terminal acceptance sets FIRE, leaves OFF and does not launch. -/
theorem door_terminal_accept {Q : Nat} (k : Fin Q) (h : ¬ k.val+1 < Q) :
    serviceDoor (.await k) .dc = ⟨.off,.e,.e,true⟩ := by
  have h₁ : (Source.await k == Source.off) = false := rfl
  have h₂ : (Source.await k == Source.i1) = false := rfl
  have h₃ : (Rail.dc == Rail.x) = false := rfl
  have h₄ : (Rail.dc == Rail.di) = false := rfl
  simp [serviceDoor,patrol,sourceGuard,arrivals,h,launch,turn,move,h₁,h₂,h₃,h₄]

/-- Only one nontrail, nonempty worker separates the empty prefix and
the trail suffix. The same shape describes the two directions. -/
def railShape (k : Nat) (worker : Rail) (i : Nat) : Rail :=
  if i < k then .e else if i = k then worker else .t

def bodyAt {Q : Nat} (r : Nat → Rail) (i : Nat) : Patrol Q :=
  patrol false false false .off (r i) (r (i+1))

/-- On the canonical outward route, precisely the body edge to the left
of the worker changes the rail; every other ordinary edge stutters. -/
theorem clean_outward_body {Q : Nat} (q : Trip Q) (k i : Nat) :
    bodyAt (Q := Q) (railShape k (outward q)) i =
      if i+1 = k then ⟨.off,outward q,.t,false⟩
      else ⟨.off,railShape k (outward q) i,railShape k (outward q) (i+1),false⟩ := by
  by_cases hp : i+1 = k
  · have hi : i < k := by omega
    subst k
    simp [bodyAt,railShape,hi,body_outward]
  · by_cases he : i < k
    · have hE : i+1 < k := by omega
      cases q <;> simp [bodyAt,railShape,he,hE,hp] <;> rfl
    · by_cases hk : i = k
      · cases q <;> simp [bodyAt,railShape,hk,outward,show ¬ k+1 < k by omega] <;> rfl
      · have hi : ¬ i+1 < k := by omega
        cases q <;> simp [bodyAt,railShape,he,hi,hp,hk] <;> rfl

/-- On the canonical return route, precisely the edge initiated by the
worker changes an ordinary pair. No unsupported trail can detach. -/
theorem clean_return_body {Q : Nat} (q : Trip Q) (k i : Nat) :
    bodyAt (Q := Q) (railShape k (inward q)) i =
      if i = k then ⟨.off,.e,inward q,false⟩
      else ⟨.off,railShape k (inward q) i,railShape k (inward q) (i+1),false⟩ := by
  by_cases hp : i = k
  · simp [bodyAt,railShape,hp,body_return,show ¬ k+1 < k by omega]
  · by_cases he : i+1 = k
    · have hi : i < k := by omega
      cases q <;> simp [bodyAt,railShape,hi,he,hp,inward] <;> rfl
    · by_cases hE : i < k
      · have hi : i+1 < k := by omega
        cases q <;> simp [bodyAt,railShape,hE,hi,hp] <;> rfl
      · have hi : ¬ i+1 < k := by omega
        cases q <;> simp [bodyAt,railShape,hE,hi,he,hp] <;> rfl

/-- At the top only the outward worker at offset zero changes direction. -/
theorem clean_outward_top {Q : Nat} (q : Trip Q) (k : Nat) :
    topRail (railShape k (outward q) 0) =
      if k = 0 then inward q else railShape k (outward q) 0 := by
  cases k <;> cases q <;> rfl

theorem clean_return_top {Q : Nat} (q : Trip Q) (k : Nat) :
    topRail (railShape k (inward q) 0) = railShape k (inward q) 0 := by
  cases k <;> cases q <;> rfl

/-- The door cannot relaunch a canonical outward worker. The initial
door worker may still be at the door, or a trail is at the door. -/
theorem clean_outward_door {Q : Nat} (q : Trip Q) (k d : Nat) (h : k ≤ d) :
    serviceDoor (waitingFor q) (railShape k (outward q) d) =
      ⟨waitingFor q,railShape k (outward q) d,.e,false⟩ := by
  have hn : ¬ d < k := by omega
  by_cases he : d = k
  · simp [railShape,he,door_wait_outward]
  · simp [railShape,hn,he,door_wait_trail]

theorem clean_return_before_door {Q : Nat} (q : Trip Q) (k d : Nat) (h : k < d) :
    serviceDoor (waitingFor q) (railShape k (inward q) d) =
      ⟨waitingFor q,railShape k (inward q) d,.e,false⟩ := by
  have hn : ¬ d < k := by omega
  have he : d ≠ k := by omega
  simp [railShape,hn,he,door_wait_trail]

/-- The clean single-trip hit budget: left moves, turn, right moves, door. -/
def tripHits (door worker : Nat) (returningPhase : Bool) : Nat :=
  if returningPhase then door-worker+1 else worker+1+door+1

theorem clean_trip_clock (d k : Nat) (hk : k ≤ d) :
    (0 < k → tripHits d (k-1) false + 1 = tripHits d k false) ∧
    (tripHits d 0 true + 1 = tripHits d 0 false) ∧
    (k < d → tripHits d (k+1) true + 1 = tripHits d k true) ∧
    tripHits d d true = 1 ∧ tripHits d d false = 2*(d+1) := by
  have _ := hk
  simp only [tripHits,Bool.false_eq_true,if_false,if_true]
  omega

/-- Native/payment prefix never writes a rail or the responder's controller.
This removes the need to assume a matching native microstate in the fixed-corridor
projection. -/
theorem prefix_ports {p c : Nat} (u v : Site p c) :
    (stepPrefix u v).1.rail = u.rail ∧ (stepPrefix u v).2.rail = v.rail ∧
      (stepPrefix u v).2.source = v.source := by
  let a := fireInitiator (materialize u v)
  let b := fireResponder v
  let t := impact a b
  let w := followerBullet (pinned t.1 t.2) t.1 t.2
  have hM : (materialize u v).rail = u.rail := by
    unfold materialize
    split <;> rfl
  have hA : a.rail = u.rail := by
    dsimp [a]
    unfold fireInitiator
    split <;> exact hM
  have hB : b.rail = v.rail ∧ b.source = v.source := by
    dsimp [b]
    unfold fireResponder
    split
    · cases v.signal <;> exact ⟨rfl,rfl⟩
    · exact ⟨rfl,rfl⟩
  have hI : t.1.rail = u.rail ∧ t.2.rail = v.rail ∧ t.2.source = v.source := by
    dsimp only [t]
    unfold impact
    split
    · split <;> exact ⟨hA,hB.1,hB.2⟩
    · exact ⟨hA,hB.1,hB.2⟩
  have hW : w.1.rail = u.rail ∧ w.2.rail = v.rail ∧ w.2.source = v.source := by
    dsimp only [w]
    unfold followerBullet
    split
    · split <;> exact hI
    · exact hI
  let emitted := if w.2.leader then Signal.one
    else if pinned t.1 t.2 then Signal.two else w.2.signal
  let m := { w.1 with signal := w.1.signal.max emitted }
  change (payment m w.2).1.rail = u.rail ∧ (payment m w.2).2.rail = v.rail ∧
    (payment m w.2).2.source = v.source
  unfold payment
  split
  · exact hW
  · split
    · exact hW
    · split <;> exact hW

def selectedPatrol {p c : Nat} (u v : Site p c) : Patrol (2*c) :=
  let w := stepPrefix u v
  patrol (w.2.leader || w.1.mark) (pinned w.1 w.2) w.2.leader
    v.source u.rail v.rail

/-- The actual physical row agrees with the selected fixed-corridor port operation,
apart from P5's explicit responder-controller reset. -/
theorem pair_ports {p c : Nat} (u v : Site p c) :
    let t := selectedPatrol u v
    let w := stepPrefix u v
    (pairStep u v).1.rail = t.left ∧ (pairStep u v).2.rail = t.right ∧
      (pairStep u v).2.source = (if t.fire && pinned w.1 w.2 then .off else t.source) := by
  have hp := prefix_ports u v
  unfold pairStep selectedPatrol
  generalize hq : stepPrefix u v = q at hp ⊢
  cases q with
  | mk a b =>
    obtain ⟨h₁,h₂,h₃⟩ := hp
    dsimp at h₁ h₂ h₃
    dsimp only [patrolWrite,finishBirth]
    rw [h₁,h₂,h₃]
    simp only [pinned]
    by_cases h : ((patrol (b.leader || a.mark) (!b.leader && a.mark)
      b.leader v.source u.rail v.rail).fire && (!b.leader && a.mark)) = true <;> simp [h]

open TaggedTail

private theorem sum_cons {n : Nat} (f : Fin (n+1) → Nat) :
    sumEdge f = f 0 + sumEdge (fun e : Fin n => f e.succ) := by
  simp [sumEdge,List.ofFn_succ]

private theorem sum_monotone {n : Nat} (f g : Fin n → Nat)
    (h : ∀ e, f e ≤ g e) : sumEdge f ≤ sumEdge g := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    rw [sum_cons f,sum_cons g]
    exact Nat.add_le_add (h 0) (ih _ _ (fun e => h e.succ))

private theorem sum_add {n : Nat} (f g : Fin n → Nat) :
    sumEdge (fun e => f e + g e) = sumEdge f + sumEdge g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sum_cons,sum_cons f,sum_cons g,ih]; omega

private theorem sum_mul {n : Nat} (f : Fin n → Nat) (a : Nat) :
    sumEdge (fun e => a * f e) = a * sumEdge f := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sum_cons,sum_cons f,ih,Nat.mul_add]

private theorem sum_const (n a : Nat) : sumEdge (fun _ : Fin n => a) = n*a := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sum_cons,ih,Nat.succ_mul,Nat.add_comm]

private theorem sum_one_at {n : Nat} (i : Fin n) :
    sumEdge (fun e => if e = i then 1 else 0) = 1 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [sum_cons]
      have hz : (fun e : Fin n => if e.succ = (0 : Fin (n+1)) then 1 else 0) =
          (fun _ : Fin n => 0) := by funext e; simp [Fin.succ_ne_zero]
      rw [hz,sum_const]
      simp
    · rw [sum_cons,if_neg (Ne.symm (Fin.succ_ne_zero j))]
      have hh : (fun e : Fin n => if e.succ = j.succ then 1 else 0) =
          (fun e : Fin n => if e = j then 1 else 0) := by funext e; simp
      rw [hh,ih,Nat.zero_add]

/-- A purely pathwise countdown in nominated marks. Nonnominated marks
are always executed, so a certificate may decrease also on those marks.
The budget and nomination may read the entire past and need not be local. -/
structure Countdown {α : Type} {n : Nat} (next : α → Fin n → α)
    (target : α → Prop) (start : α) where
  budget : List (Fin n) → Nat
  nominate : List (Fin n) → Fin n
  decrease : ∀ w, ¬ target (GGTiming.runMarks next start w) → ∀ e,
    budget (w ++ [e]) + (if e = nominate w then 1 else 0) ≤ budget w

/-- An adaptive countdown of B nominated hits yields mean at most n*B
on the actual IID physical marks. This also certifies every truncation,
and makes no assertion of independence of consecutive chosen edges. -/
theorem expected_of_countdown {α : Type} {n : Nat} (next : α → Fin n → α)
    (target : α → Prop) (start : α) (q : Countdown next target start) :
    IIDExpectedHittingTimeAtMost next target start (n*q.budget []) := by
  classical
  have h (t : Nat) (w : List (Fin n)) :
      iidHitCost next target t (GGTiming.runMarks next start w) ≤
        (n*q.budget w)*n^t := by
    induction t generalizing w with
    | zero => simp [iidHitCost]
    | succ t ih =>
      by_cases ht : target (GGTiming.runMarks next start w)
      · rw [iidHitCost_of_target _ _ _ ht]
        exact Nat.zero_le _
      · rw [iidHitCost,if_neg ht]
        change n^(t+1) + sumEdge (fun e : Fin n => iidHitCost next target t
          (next (GGTiming.runMarks next start w) e)) ≤ _
        have hb := sum_monotone
          (fun e => q.budget (w++[e]) + if e = q.nominate w then 1 else 0)
          (fun _ => q.budget w) (q.decrease w ht)
        rw [sum_add,sum_one_at,sum_const] at hb
        have hc (e : Fin n) := ih (w++[e])
        simp only [GGTiming.runMarks_append,GGTiming.runMarks] at hc
        have hs := sum_monotone _ _ (fun e => hc e)
        have hsum :
            sumEdge (fun e : Fin n => (n*q.budget (w++[e]))*n^t) =
              n^(t+1) * sumEdge (fun e : Fin n => q.budget (w++[e])) := by
          rw [← sum_mul]
          apply congrArg sumEdge
          funext e
          rw [Nat.pow_succ]
          ac_rfl
        have hfin := Nat.mul_le_mul_left (n^(t+1)) hb
        rw [Nat.mul_add,Nat.mul_one] at hfin
        calc
          _ ≤ n^(t+1) + sumEdge (fun e : Fin n => (n*q.budget (w++[e]))*n^t) :=
            Nat.add_le_add_left hs _
          _ = n^(t+1) * sumEdge (fun e : Fin n => q.budget (w++[e])) + n^(t+1) := by
            rw [hsum,Nat.add_comm]
          _ ≤ n^(t+1)*(n*q.budget w) := hfin
          _ = _ := Nat.mul_comm _ _
  intro t
  exact h t []

/-- The fixed-geometry stop tests the original top, and the original
source as the first ghost after it. Topology and leader status are real
physical fields; rail and source residual bytes are unrestricted. -/
def FixedLive {p c n : Nat} (up top : Fin n) (d : Nat) (topLiving : Bool)
    (x : Config p c n) : Prop :=
  (x up).mark = true ∧ (x top).leader = topLiving ∧ FirstMark x top d ∧
    (x (liftedSite top (d+1))).leader = false

/-- Exact remaining dirty-route certificate in the distinct-endpoint
rank≥2 application. The budget includes normalization and the clean
batches. A stronger designated stop only reduces the waiting time.
The sole-root alias needs a separate combined top-and-door route and is
not required for this bounded-rank ingredient. -/
def ConcreteFixedResidualClock : Prop :=
  ∀ {p c n : Nat} (x : Config p c n) (up top : Fin n) (d : Nat) (topLiving : Bool),
    4 ≤ n → 0 < c → rightNeighbor up = top → d+1 < n →
    MCOV x → COV x → FixedLive up top d topLiving x →
    ∃ clock : Countdown step (fun y => ¬ FixedLive up top d topLiving y) x,
      clock.budget [] ≤ 32 * (2*c+1) * (d+2)

/-- The raw-mark cost bound follows from the residual clock certificate
without a stochastic stopping-time or independence gap. -/
theorem fixedResidual_expected_of_clock (cert : ConcreteFixedResidualClock)
    {p c n : Nat} (x : Config p c n) (up top : Fin n) (d : Nat) (topLiving : Bool)
    (hn : 4 ≤ n) (hc : 0 < c) (hu : rightNeighbor up = top) (hd : d+1 < n)
    (hm : MCOV x) (hs : COV x) (h : FixedLive up top d topLiving x) :
    IIDExpectedHittingTimeAtMost step (fun y => ¬ FixedLive up top d topLiving y) x
      (n * (32*(2*c+1)*(d+2))) := by
  obtain ⟨clock,hb⟩ := cert x up top d topLiving hn hc hu hd hm hs h
  intro t
  exact Nat.le_trans (expected_of_countdown _ _ _ clock t)
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hb))

end L4.FixedResidual
