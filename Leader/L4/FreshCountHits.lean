import Leader.L4.FreshEpochAuthentication
import Leader.L4.RankRace

/-! Canonical COUNT after authenticated A1. The terminal service is
charged to the returning worker, not to the next launch sharing it. -/
namespace L4.FreshCountHits
open FreshEpochAuthentication

inductive Direction where | outward | inward
  deriving DecidableEq

def worker : Direction → Rail
  | .outward => .uc
  | .inward => .dc

def shape {h : Nat} (way : Direction) (j : Fin h) : Fin h → Rail :=
  fun i => if i=j then worker way else if i.val<j.val then .e else .t

/-- Sites remaining before the head's next acceptance. The top turn
and door acceptance each cost one hit, even when the gap has length 1. -/
def remaining {h : Nat} (way : Direction) (j : Fin h) : Nat :=
  match way with
  | .outward => h+j.val+1
  | .inward => h-j.val

theorem remaining_launch {h : Nat} (j : Fin h) (hj : j.val+1=h) :
    remaining .outward j = 2*h := by simp [remaining]; omega

theorem body_outward {Q h : Nat} (a b : Fin h) (hA : a.val+1=b.val) :
    body (Q:=Q) (shape .outward b) a b = shape .outward a := by
  have hab : a ≠ b := fun hh => by have hh' := congrArg Fin.val hh; omega
  have h1 : shape .outward b a = .e := by simp [shape,hab,show a.val<b.val by omega]
  have h2 : shape .outward b b = .uc := by simp [shape,worker]
  funext i
  unfold body
  rw [h1,h2]
  have hh : (Piece (Q:=Q) .e .uc).left = .uc ∧ (Piece (Q:=Q) .e .uc).right = .t := ⟨rfl,rfl⟩
  simp only [hh.1,hh.2]
  by_cases hi : i=a
  · subst i; simp [put,hab,shape,worker]
  · by_cases hi' : i=b
    · subst i; simp [put,hi,shape,show ¬b.val<a.val by omega]
    · have hi0 : i.val ≠ a.val := fun hh => hi (Fin.ext hh)
      have hi1 : i.val ≠ b.val := fun hh => hi' (Fin.ext hh)
      have he : i.val<b.val ↔ i.val<a.val := by omega
      simp [put,shape,hi,hi',he]

theorem body_inward {Q h : Nat} (a b : Fin h) (hA : a.val+1=b.val) :
    body (Q:=Q) (shape .inward a) a b = shape .inward b := by
  have hab : a ≠ b := fun hh => by have hh' := congrArg Fin.val hh; omega
  have h1 : shape .inward a a = .dc := by simp [shape,worker]
  have h2 : shape .inward a b = .t := by simp [shape,Ne.symm hab,show ¬b.val<a.val by omega]
  funext i
  unfold body
  rw [h1,h2]
  have hh : (Piece (Q:=Q) .dc .t).left = .e ∧ (Piece (Q:=Q) .dc .t).right = .dc := ⟨rfl,rfl⟩
  simp only [hh.1,hh.2]
  by_cases hi : i=a
  · subst i; simp [put,hab,shape,show a.val<b.val by omega]
  · by_cases hi' : i=b
    · subst i; simp [put,shape,worker]
    · have hi0 : i.val ≠ a.val := fun hh => hi (Fin.ext hh)
      have hi1 : i.val ≠ b.val := fun hh => hi' (Fin.ext hh)
      have he : i.val<b.val ↔ i.val<a.val := by omega
      simp [put,shape,hi,hi',he]

theorem body_idle {Q h : Nat} (way : Direction) (a b j : Fin h) (hA : a.val+1=b.val)
    (hn : match way with | .outward => b ≠ j | .inward => a ≠ j) :
    body (Q:=Q) (shape way j) a b = shape way j := by
  let r := shape way j
  have hne : a ≠ b := fun hh => by have hh' := congrArg Fin.val hh; omega
  have hpair : (Piece (Q:=Q) (r a) (r b)).left = r a ∧ (Piece (Q:=Q) (r a) (r b)).right = r b := by
    by_cases ha : a=j
    · subst j
      cases way
      · have hb : r b = .t := by simp [r,shape,Ne.symm hne,show ¬b.val<a.val by omega]
        rw [show r a = .uc by simp [r,shape,worker],hb]
        exact ⟨rfl,rfl⟩
      · exact False.elim (hn rfl)
    · by_cases hb : b=j
      · subst j
        cases way
        · exact False.elim (hn rfl)
        · have he : r a = .e := by simp [r,shape,hne,show a.val<b.val by omega]
          rw [he,show r b=.dc by simp [r,shape,worker]]
          exact ⟨rfl,rfl⟩
      · have ha' : a.val≠j.val := fun hh => ha (Fin.ext hh)
        have hb' : b.val≠j.val := fun hh => hb (Fin.ext hh)
        by_cases hj : b.val<j.val
        · have hr : r a=.e ∧ r b=.e := by simp [r,shape,ha,hb,hj,show a.val<j.val by omega]
          rw [hr.1,hr.2]
          exact ⟨rfl,rfl⟩
        · have hr : r a=.t ∧ r b=.t := by simp [r,shape,ha,hb,hj,show ¬a.val<j.val by omega]
          rw [hr.1,hr.2]
          exact ⟨rfl,rfl⟩
  change body (Q:=Q) r a b = r
  unfold body
  simp only [hpair.1,hpair.2]
  funext i
  by_cases ia : i=a <;> by_cases ib : i=b <;> simp [put,ia,ib,hne]

theorem top_turn {Q h : Nat} (j : Fin h) (l : Rail) :
    top (Q:=Q) (shape .outward j) j l = shape .inward j := by
  have hW : (patrol true false true (.off : Source Q) l .uc).right = .dc := by
    cases l <;> rfl
  funext i
  by_cases h : i=j
  · subst i; simp [top,put,shape,worker,hW]
  · simp [top,put,shape,h]

theorem top_idle {Q h : Nat} (way : Direction) (z j : Fin h)
    (hz : z.val=0) (l : Rail)
    (hn : way=.inward ∨ z≠j) :
    top (Q:=Q) (shape way j) z l = shape way j := by
  have hW : (patrol true false true (.off : Source Q) l (shape way j z)).right =
      shape way j z := by
    by_cases hZ : z=j
    · subst z
      have he : way=.inward := hn.resolve_right (fun h => h rfl)
      subst way
      have hh : shape .inward j j = .dc := by simp [shape,worker]
      rw [hh]
      cases l <;> rfl
    · have hVal : z.val ≠ j.val := fun he => hZ (Fin.ext he)
      have hh : shape way j z = .e := by simp [shape,hZ,show z.val<j.val by omega]
      rw [hh]; exact top_empty l
  funext i
  unfold top
  rw [hW]
  by_cases hi : i=z <;> simp [put,hi]

def countDoor {Q h : Nat} (r : Fin h → Rail) (d : Fin h) (k : Fin Q)
    (outside : Rail) : Patrol Q := patrol true true false (.await k) (r d) outside

theorem door_holds {Q h : Nat} (way : Direction) (d j : Fin h) (hd : d.val+1=h)
    (k : Fin Q) (outside : Rail) (hn : way=.outward ∨ d≠j) :
    let t := countDoor (shape way j) d k outside
    t.left = shape way j d ∧ t.source = .await k ∧ t.fire = false := by
  have hRail : shape way j d = .uc ∨ shape way j d = .t := by
    by_cases he : d=j
    · subst d
      have hW : way=.outward := hn.resolve_right (fun hh => hh rfl)
      subst way
      exact Or.inl (by simp [shape,worker])
    · have hp : d.val≠j.val := fun hh => he (Fin.ext hh)
      exact Or.inr (by simp [shape,he,show ¬d.val<j.val by have := j.isLt; omega])
  unfold countDoor
  rcases hRail with hh|hh <;> rw [hh] <;> cases outside <;> exact ⟨rfl,rfl,rfl⟩

/-- Accepting a nonterminal matching return shares L2's next launch.
On the terminal count the old controller becomes OFF and latches P5. -/
theorem door_accepts {Q h : Nat} (d : Fin h) (k : Fin Q) (outside : Rail) :
    let t := countDoor (shape .inward d) d k outside
    if hk : k.val+1<Q then
      t.left = .uc ∧ t.source = .await ⟨k.val+1,hk⟩ ∧ t.fire = false
    else t.left = .e ∧ t.source = .off ∧ t.fire = true := by
  have hRail : shape .inward d d = .dc := by simp [shape,worker]
  change (if hk : k.val+1<Q then _ else _)
  unfold countDoor
  rw [hRail]
  by_cases hk : k.val+1<Q
  · rw [dif_pos hk]
    cases outside <;> simp [patrol,sourceGuard,arrivals,launch,turn,move,hk,
      show ((Source.await k : Source Q) == .off) = false from rfl,
      show ((Source.await k : Source Q) == .i1) = false from rfl,
      show (Rail.dc == Rail.x) = false from rfl]
  · rw [dif_neg hk]
    cases outside <;> simp [patrol,sourceGuard,arrivals,launch,turn,move,hk,
      show ((Source.await k : Source Q) == .off) = false from rfl,
      show ((Source.await k : Source Q) == .i1) = false from rfl,
      show (Rail.dc == Rail.x) = false from rfl]

inductive Clock (Q h : Nat) where
  | active (count : Fin Q) (way : Direction) (front : Fin h)
  | done

def work {Q h : Nat} : Clock Q h → Nat
  | .done => 0
  | .active k w j => (Q-(k.val+1))*(2*h) + remaining w j

/-- Local bond numbers: before slot 0 is 0; the bond from slot i
to i+1 is i+1; after the last slot is h. -/
def needed {Q h : Nat} : Clock Q h → Option Nat
  | .done => none
  | .active _ .outward j => some j.val
  | .active _ .inward j => some (j.val+1)

def hit {Q h : Nat} (q : Clock Q h) (selected : Option Nat) : Nat :=
  if (needed q).isSome && needed q == selected then 1 else 0

-- Use a name outside Clock for the arithmetic recurrence below.

inductive MarkStep {Q h : Nat} : Clock Q h → Option Nat → Clock Q h → Prop
  | stay (s : Clock Q h) (e : Option Nat) : hit s e = 0 → MarkStep s e s
  | outward (k : Fin Q) (a b : Fin h) : a.val+1=b.val →
      MarkStep (.active k .outward b) (some b.val) (.active k .outward a)
  | turn (k : Fin Q) (z : Fin h) : z.val=0 →
      MarkStep (.active k .outward z) (some 0) (.active k .inward z)
  | inward (k : Fin Q) (a b : Fin h) : a.val+1=b.val →
      MarkStep (.active k .inward a) (some b.val) (.active k .inward b)
  | relaunch (k k' : Fin Q) (d : Fin h) : d.val+1=h → k.val+1=k'.val →
      MarkStep (.active k .inward d) (some h) (.active k' .outward d)
  | finish (k : Fin Q) (d : Fin h) : d.val+1=h → k.val+1=Q →
      MarkStep (.active k .inward d) (some h) .done

theorem work_step {Q h : Nat} {s t : Clock Q h} {e : Option Nat} (H : MarkStep s e t) :
    work t + hit s e = work s := by
  cases H with
  | stay _ _ hz => simp [hz]
  | outward k a b hb => simp [work,hit,needed,remaining]; omega
  | turn k z hz => simp [work,hit,needed,remaining,hz]; omega
  | inward k a b hb =>
    have ha := a.isLt
    have hc := b.isLt
    simp [work,hit,needed,remaining,hb]
    omega
  | relaunch k k' d hd hk =>
    have he : Q-(k.val+1) = Q-(k'.val+1)+1 := by have := k'.isLt; omega
    simp [work,hit,needed,remaining,hd,he,Nat.add_mul]
    omega
  | finish k d hd hk =>
    simp [work,hit,needed,remaining,hd,hk]
    omega

inductive MarkTape {Q h : Nat} : Clock Q h → List (Option Nat) → Clock Q h → Nat → Prop
  | nil (q : Clock Q h) : MarkTape q [] q 0
  | cons {s t q : Clock Q h} {e : Option Nat} {es : List (Option Nat)} {j : Nat}
      (hstep : MarkStep s e t) (hrest : MarkTape t es q j) :
      MarkTape s (e::es) q (hit s e+j)

theorem work_tape {Q h : Nat} {s t : Clock Q h} {es : List (Option Nat)} {j : Nat}
    (H : MarkTape s es t j) : work t+j = work s := by
  induction H with
  | nil => simp
  | cons hstep _ ih =>
    have hh := work_step hstep
    omega

/-- From the just-authenticated count-zero launch to the P5 latch,
there are exactly 2hQ *post-A1* nominated edge hits. The final door
service is included. Arbitrarily many nonnominated marks can stutter. -/
theorem count_tape_exact {Q h : Nat} (hQ : 0<Q) (door : Fin h)
    (hd : door.val+1=h) (es : List (Option Nat)) (j : Nat)
    (H : MarkTape (.active ⟨0,hQ⟩ .outward door) es .done j) :
    j = 2*h*Q := by
  have hh := work_tape H
  have hH : remaining .outward door = 2*h := remaining_launch door hd
  change j = _
  change 0+j = (Q-(0+1))*(2*h) + remaining .outward door at hh
  have hRound : Q-1+1=Q := by omega
  rw [hH,show 0+1=1 from rfl,Nat.zero_add] at hh
  calc
    j = (Q-1)*(2*h)+2*h := hh
    _ = (Q-1+1)*(2*h) := by rw [Nat.add_mul,Nat.one_mul]
    _ = 2*h*Q := by rw [hRound,Nat.mul_comm Q]

/-- Local command selected by the physical edge (exterior marks
stutter). Exterior rail values are carried only at the two endpoints. -/
inductive Command (h : Nat) where
  | exterior
  | top (z : Fin h) (atStart : z.val=0) (outside : Rail)
  | inner (a b : Fin h) (adj : a.val+1=b.val)
  | door (d : Fin h) (atEnd : d.val+1=h) (outside : Rail)

def selected {h : Nat} : Command h → Option Nat
  | .exterior => none
  | .top _ _ _ => some 0
  | .inner _ b _ => some b.val
  | .door _ _ _ => some h

structure Frame (Q h : Nat) where
  rails : Fin h → Rail
  controller : Source Q
  fired : Bool

def applyCommand {Q h : Nat} (k : Fin Q) (r : Fin h → Rail) (e : Command h) : Frame Q h :=
  match e with
  | .exterior => ⟨r,.await k,false⟩
  | .top z _ l => ⟨top (Q:=Q) r z l,.await k,false⟩
  | .inner a b _ => ⟨body (Q:=Q) r a b,.await k,false⟩
  | .door d _ l =>
    let f := countDoor r d k l
    ⟨put r d f.left,f.source,f.fire⟩

def Encodes {Q h : Nat} (f : Frame Q h) : Clock Q h → Prop
  | .active k w j => f.rails = shape w j ∧ f.controller = .await k ∧ f.fired = false
  | .done => f.fired = true

private theorem put_same {h : Nat} (r : Fin h → Rail) (d : Fin h) :
    put r d (r d) = r := by
  funext i; by_cases he : i=d <;> simp [put,he]

private theorem canonical_relaunch {h : Nat} (d : Fin h) :
    put (shape .inward d) d .uc = shape .outward d := by
  funext i
  by_cases hi : i=d <;> simp [put,shape,worker,hi]

/-- All actual local operations are either the unique nominated progress
or literal stutter, and the terminal latch is the done transition. -/
theorem canonical_step {Q h : Nat} (k : Fin Q) (w : Direction) (j : Fin h) (e : Command h) :
    ∃ s : Clock Q h, Encodes (applyCommand k (shape w j) e) s ∧
      MarkStep (.active k w j) (selected e) s := by
  cases e with
  | exterior =>
    refine ⟨.active k w j,⟨rfl,rfl,rfl⟩,MarkStep.stay _ _ ?_⟩
    cases w <;> rfl
  | top z hz outside =>
    cases w with
    | outward =>
      by_cases hzj : z=j
      · subst j
        exact ⟨.active k .inward z,⟨top_turn z outside,rfl,rfl⟩,MarkStep.turn k z hz⟩
      · have hj0 : j.val ≠ 0 := by
          intro hh
          exact hzj (Fin.ext (hz.trans hh.symm))
        refine ⟨.active k .outward j,⟨top_idle .outward z j hz outside (Or.inr hzj),rfl,rfl⟩,
          MarkStep.stay _ _ ?_⟩
        simp [hit,needed,selected,hj0]
    | inward =>
      refine ⟨.active k .inward j,⟨top_idle .inward z j hz outside (Or.inl rfl),rfl,rfl⟩,
        MarkStep.stay _ _ ?_⟩
      simp [hit,needed,selected]
  | inner a b hAB =>
    cases w with
    | outward =>
      by_cases hb : b=j
      · subst j
        exact ⟨.active k .outward a,⟨body_outward a b hAB,rfl,rfl⟩,MarkStep.outward k a b hAB⟩
      · have hb' : j.val≠b.val := fun he => hb (Fin.ext he.symm)
        refine ⟨.active k .outward j,⟨body_idle .outward a b j hAB hb,rfl,rfl⟩,
          MarkStep.stay _ _ ?_⟩
        simp [hit,needed,selected,hb']
    | inward =>
      by_cases ha : a=j
      · subst j
        exact ⟨.active k .inward b,⟨body_inward a b hAB,rfl,rfl⟩,MarkStep.inward k a b hAB⟩
      · have hb' : j.val+1≠b.val := by
          intro he
          exact ha (Fin.ext (by omega))
        refine ⟨.active k .inward j,⟨body_idle .inward a b j hAB ha,rfl,rfl⟩,
          MarkStep.stay _ _ ?_⟩
        simp [hit,needed,selected,hb']
  | door d hd outside =>
    have hold (g : Direction) (h : g=.outward ∨ d≠j) :
        Encodes (applyCommand k (shape g j) (.door d hd outside)) (.active k g j) := by
      obtain ⟨h1,h2,h3⟩ := door_holds g d j hd k outside h
      change put (shape g j) d (countDoor (shape g j) d k outside).left = shape g j ∧ _ ∧ _
      exact ⟨by rw [h1,put_same],h2,h3⟩
    cases w with
    | outward =>
      have hJ := j.isLt
      refine ⟨.active k .outward j,hold _ (Or.inl rfl),MarkStep.stay _ _ ?_⟩
      simp [hit,needed,selected,show j.val≠h by omega]
    | inward =>
      by_cases hdj : d=j
      · subst j
        have hAccept := door_accepts d k outside
        by_cases hK : k.val+1<Q
        · rw [dif_pos hK] at hAccept
          refine ⟨.active ⟨k.val+1,hK⟩ .outward d, ?_,MarkStep.relaunch k _ d hd rfl⟩
          change put (shape .inward d) d (countDoor (shape .inward d) d k outside).left =
            shape .outward d ∧ _ ∧ _
          exact ⟨by rw [hAccept.1,canonical_relaunch],hAccept.2.1,hAccept.2.2⟩
        · rw [dif_neg hK] at hAccept
          have hfinal : k.val+1=Q := by have := k.isLt; omega
          exact ⟨.done,hAccept.2.2,MarkStep.finish k d hd hfinal⟩
      · have hdj' : j.val+1≠h := fun he => hdj (Fin.ext (by omega))
        refine ⟨.active k .inward j,hold _ (Or.inr hdj),MarkStep.stay _ _ ?_⟩
        simp [hit,needed,selected,hdj']

/-- Count terminal P5 clears the source already written OFF by A2,
and cannot change the visible rail output. -/
theorem count_door_pair {p c h : Nat} (u v : Site p c) (w : Direction) (j d : Fin h)
    (hd : d.val+1=h) (k : Fin (2*c)) (hRail : u.rail=shape w j d)
    (hm : (stepPrefix u v).1.mark=true) (hl : (stepPrefix u v).2.leader=false)
    (hs : (stepPrefix u v).2.source=.await k)
    (hu' : (stepPrefix u v).1.rail=u.rail) (hv' : (stepPrefix u v).2.rail=v.rail) :
    let t := countDoor (shape w j) d k v.rail
    (pairStep u v).1.rail = t.left ∧
      (pairStep u v).2.source = t.source ∧ (pairStep u v).2.leader = t.fire := by
  let t := countDoor (shape w j) d k v.rail
  have hF : t.fire=true → t.source=.off := by
    by_cases h : w=.outward ∨ d≠j
    · have hh := (door_holds w d j hd k v.rail h).2.2
      intro hOn; change t.fire = false at hh
      simp [hOn] at hh
    · have hJ : d=j := by
        by_cases he : d=j
        · exact he
        · exact False.elim (h (Or.inr he))
      have hW : w=.inward := by
        cases w
        · exact False.elim (h (Or.inl rfl))
        · rfl
      subst w
      subst j
      have hAcc := door_accepts d k v.rail
      by_cases hK : k.val+1<2*c
      · rw [dif_pos hK] at hAcc
        intro hOn
        have hh : t.fire = false := hAcc.2.2
        simp [hOn] at hh
      · rw [dif_neg hK] at hAcc
        intro _
        exact hAcc.2.1
  change (pairStep u v).1.rail=t.left ∧ (pairStep u v).2.source=t.source ∧
    (pairStep u v).2.leader=t.fire
  unfold pairStep
  generalize stepPrefix u v = ab at hm hl hs hu' hv' ⊢
  rcases ab with ⟨a,b⟩
  dsimp only at hm hl hs hu' hv' ⊢
  have hP : patrol (b.leader || a.mark) (pinned a b) b.leader b.source a.rail b.rail = t := by
    simp [hm,hl,hs,hu',hv',hRail,t,countDoor,pinned]
  rw [hP]
  cases hOn : t.fire
  · simp [patrolWrite,finishBirth,pinned,hm,hl]
  · simp [patrolWrite,finishBirth,pinned,hm,hl,hF hOn]

private theorem no_pay_door_geometry {p c : Nat} (u v : Site p c)
    (hm : u.mark = true) (hl : v.leader = false)
    (hp : geometricPay u v = false) :
    (stepPrefix u v).1.mark=true ∧ (stepPrefix u v).2.leader=false := by
  let a := native (materialize u v) v
  have hmat : (materialize u v).mark = true := by simp [materialize,hm]
  have hM : a.1.mark = true := (native_preserves_mark _ _).trans hmat
  have hL : a.2.leader = false := old_follower_native _ _ hl
  have hP : payer a.1 = false := by
    change (!a.2.leader && a.1.mark && payer a.1) = false at hp
    simpa [hM,hL] using hp
  change (payment a.1 a.2).1.mark=true ∧ (payment a.1 a.2).2.leader=false
  simp [payment,hM,hL,hP]

def codeFromOffset (n d k : Nat) : Option Nat :=
  if k+1=n then some 0 else if k≤d then some (k+1) else none

def physicalFrame {p c n : Nat} (x : Config p c n) (y : Fin n) (d : Nat) : Frame (2*c) (d+1) :=
  ⟨railsAt x y d,(x (liftedSite y (d+1))).source,(x (liftedSite y (d+1))).leader⟩

private theorem distinct {n : Nat} (hn : 4 ≤ n) (e : Fin n) : rightNeighbor e ≠ e := by
  intro he
  have hh : liftedSite e 1 = liftedSite e 0 := by simpa [liftedSite_succ,liftedSite_zero] using he
  have hh' := liftedSite_inj e (by omega : 1<n) (by omega : 0<n) hh
  omega

/-- Exact physical COUNT projection for every ring service in a fixed
protected epoch. If the selected marked victim is paid, the epoch exits
instead and the asserted COUNT projection is not used on that mark. -/
theorem count_ring_projection {p c n d : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (y : Fin n) (k : Nat) (hkn : k<n)
    (hm : MCOV x) (hc : COV x) (H : RankFresh.Corridor x y d)
    (q : Fin (2*c)) (w : Direction) (j : Fin (d+1))
    (hS : (x (liftedSite y (d+1))).source = .await q)
    (hShape : railsAt x y d = shape w j)
    (hPay : k=d → geometricPay (x (liftedSite y k))
      (x (rightNeighbor (liftedSite y k))) = false) :
    ∃ e : Command (d+1), selected e=codeFromOffset n d k ∧
      physicalFrame (step x (liftedSite y k)) y d = applyCommand q (shape w j) e := by
  let e := liftedSite y k
  let b := rightNeighbor e
  let z := liftedSite y (d+1)
  let x' := step x e
  have hRe : liftedSite y (k+1) = b := liftedSite_succ _ _
  have hne := distinct hn e
  have stepL : x' e = (pairStep (x e) (x b)).1 := by simp [x',step,b]
  have stepR : x' b = (pairStep (x e) (x b)).2 := by simp [x',step,b,hne]
  have stepO (i) (ha : i ≠ e) (hb : i ≠ b) : x' i = x i := by simp [x',step,b,ha,hb]
  have hGap := H.gap
  have siteNe (a b : Nat) (ha : a<n) (hb : b<n) (hh : a≠b) :
      liftedSite y a ≠ liftedSite y b := fun he => hh (liftedSite_inj y ha hb he)
  have hKeep (hK : k≠d) : (x' z).source = .await q ∧ (x' z).leader = false := by
    have hz : z ≠ b := by
      intro hz
      have hh : rightNeighbor (liftedSite y d) = rightNeighbor e :=
        (liftedSite_succ y d).symm.trans hz
      have hf := congrArg RearTrace.predecessor hh
      simp only [RearTrace.predecessor_right] at hf
      exact hK (liftedSite_inj y (by omega) hkn hf).symm
    by_cases hz' : z=e
    · rw [hz',stepL,pair_left_source,(pair_geometric_fields (x e) (x b)).2.1,← hz']
      exact ⟨hS,H.ghost⟩
    · rw [stepO _ hz' hz]; exact ⟨hS,H.ghost⟩
  have frameEq (r : Fin (d+1) → Rail) (s : Source (2*c)) (f : Bool)
      (hRails : railsAt x' y d = r) (hs : (x' z).source=s) (hf : (x' z).leader=f) :
      physicalFrame x' y d = ⟨r,s,f⟩ := by
    change Frame.mk (railsAt x' y d) (x' z).source (x' z).leader = Frame.mk r s f
    rw [hRails,hs,hf]
  by_cases hk : k<d
  · have hM : (x e).mark = false := Bool.eq_false_iff.mpr (H.first.before k hk)
    have hL : (x b).leader = false := Bool.eq_false_iff.mpr (fun hh => H.first.before k hk (hm e (Or.inl hh)))
    have hR : (x b).residue = nextResidue (x e).residue := by
      by_cases h : (x b).residue = nextResidue (x e).residue
      · exact h
      · exact False.elim (H.first.before k hk (hm e (Or.inr h)))
    have hOff : (x b).source = .off := by
      by_cases h : (x b).source = .off
      · exact h
      · exact False.elim (H.first.before k hk (hc e h).2)
    obtain ⟨hu,hv,_⟩ := ordinary_pair_projects (x e) (x b) hM hR hL hOff
    let a₀ : Fin (d+1) := ⟨k,by omega⟩
    let b₀ : Fin (d+1) := ⟨k+1,by omega⟩
    have hCode : selected (.inner a₀ b₀ rfl) = codeFromOffset n d k := by
      simp [selected,codeFromOffset,b₀,show ¬ k+1=n by omega,show k≤d by omega]
    refine ⟨.inner a₀ b₀ rfl,hCode,?_⟩
    rw [← hShape]
    apply frameEq _ _ _ _ (hKeep (by omega)).1 (hKeep (by omega)).2
    funext i
    have hv' : liftedSite y b₀.val = b := hRe
    change (x' (liftedSite y i.val)).rail =
      put (put (railsAt x y d) a₀ (Piece (Q:=2*c)
        (x e).rail (x (liftedSite y (k+1))).rail).left)
        b₀ (Piece (Q:=2*c) (x e).rail (x (liftedSite y (k+1))).rail).right i
    rw [hRe]
    by_cases hi : i=b₀
    · subst i
      rw [hv',stepR,hv]
      simp [put]
    · by_cases hj : i=a₀
      · subst i
        rw [show liftedSite y a₀.val=e from rfl,stepL,hu]
        simp [put,hi]
      · have hia : i.val≠k := fun hh => hj (Fin.ext hh)
        have hib : i.val≠k+1 := fun hh => hi (Fin.ext hh)
        have hI := i.isLt
        have h1 := siteNe i.val k (by omega) hkn hia
        have h2 := siteNe i.val (k+1) (by omega) (by omega) hib
        rw [hRe] at h2
        rw [stepO _ h1 h2]
        simp [put,hi,hj,railsAt]
  · by_cases hd : k=d
    · let slot : Fin (d+1) := ⟨d,by omega⟩
      have hEb : e=liftedSite y d := congrArg (liftedSite y) hd
      have hzb : z=b := by rw [← hRe,hd]
      obtain ⟨hM,hL⟩ := no_pay_door_geometry (x e) (x b)
        (hEb.symm ▸ H.first.marked) (hzb ▸ H.ghost) (hPay hd)
      have hP := prefix_payload (x e) (x b)
      have hRail : (x e).rail = shape w j slot := by
        rw [← hShape]
        exact congrArg (fun i => (x i).rail) hEb
      have hProj := count_door_pair (x e) (x b) w j slot rfl q hRail
        hM hL (hP.2.2.trans (hzb ▸ hS)) hP.1 hP.2.1
      have hCode : selected (.door slot rfl (x b).rail) = codeFromOffset n d k := by
        simp [selected,codeFromOffset,hd,show ¬d+1=n by omega]
      refine ⟨.door slot rfl (x b).rail,hCode,?_⟩
      change physicalFrame x' y d = ⟨_,_,_⟩
      refine frameEq _ _ _ ?_ ?_ ?_
      · funext i
        by_cases hi : i=slot
        · subst i
          change (x' (liftedSite y d)).rail = _
          rw [← hEb,stepL,hProj.1]
          simp [put]
        · have hI := i.isLt
          have hni : i.val≠d := fun hh => hi (Fin.ext hh)
          have h1 := siteNe i.val k (by omega) hkn (by omega)
          have h2 := siteNe i.val (d+1) (by omega) (by omega) (by omega)
          change liftedSite y i.val ≠ z at h2
          rw [hzb] at h2
          change (x' (liftedSite y i.val)).rail = _
          rw [stepO _ h1 h2,← hShape]
          simp [put,hi,railsAt]
      · rw [hzb,stepR]; exact hProj.2.1
      · rw [hzb,stepR]; exact hProj.2.2
    · by_cases htop : k+1=n
      · let slot : Fin (d+1) := ⟨0,by omega⟩
        have hby : b=y := by rw [← hRe,htop,liftedSite_full]
        have hO : (x b).source = .off := by
          by_cases hs : (x b).source = .off
          · exact hs
          · have hl := (hc e hs).1
            change (x b).leader = false at hl
            rw [hby,H.leader] at hl
            contradiction
        have hK : ¬ TenureOrigins.nativeKill (x e) (x b) := by
          intro hKill
          have hl : (x b).leader = true := hby.symm ▸ H.leader
          have he := (TenureOrigins.covered_leader_loss_iff (x e) (x b) hl hO).mpr hKill
          have hAlive := (RankFresh.corridor_supplier_step hn x y e hm H).1
          change (x' y).leader=true at hAlive
          rw [← hby,stepR,he] at hAlive
          contradiction
        have hP := top_pair_projects (x e) (x b) (hby.symm ▸ H.leader) hO hK
        have hCode : selected (.top slot rfl (x e).rail) = codeFromOffset n d k := by
          simp [selected,codeFromOffset,htop]
        refine ⟨.top slot rfl (x e).rail,hCode,?_⟩
        rw [← hShape]
        apply frameEq _ _ _ _ (hKeep hd).1 (hKeep hd).2
        funext i
        by_cases hi : i=slot
        · subst i
          change (x' (liftedSite y 0)).rail = _
          rw [liftedSite_zero,← hby,stepR,hP.2.1]
          simp [top,put,railsAt,slot,liftedSite_zero,hby]
        · have hI := i.isLt
          have hi0 : i.val≠0 := fun hh => hi (Fin.ext hh)
          have h1 := siteNe i.val k (by omega) hkn (by omega)
          have h2 := siteNe i.val 0 (by omega) (by omega) hi0
          rw [liftedSite_zero] at h2
          have h2' : liftedSite y i.val ≠ b := fun hh => h2 (hh.trans hby)
          change (x' (liftedSite y i.val)).rail = _
          rw [stepO _ h1 h2']
          simp [top,put,hi,railsAt]
      · have hCode : selected (Command.exterior (h:=d+1)) = codeFromOffset n d k := by
          simp [selected,codeFromOffset,htop,show ¬k≤d by omega]
        refine ⟨.exterior,hCode,?_⟩
        rw [← hShape]
        apply frameEq _ _ _ _ (hKeep hd).1 (hKeep hd).2
        funext i
        have hI := i.isLt
        have h1 := siteNe i.val k (by omega) hkn (by omega)
        have h2 := siteNe i.val (k+1) (by omega) (by omega) (by omega)
        rw [hRe] at h2
        change (x' (liftedSite y i.val)).rail = _
        rw [stepO _ h1 h2]
        rfl

noncomputable def rawCode {n : Nat} (y : Fin n) (d : Nat) (e : Fin n) : Option Nat :=
  codeFromOffset n d (Classical.choose (liftedSite_of_site y e))

theorem rawCode_of_lift {n : Nat} (y : Fin n) (d k : Nat) (hk : k<n) :
    rawCode y d (liftedSite y k) = codeFromOffset n d k := by
  unfold rawCode
  let h := liftedSite_of_site y (liftedSite y k)
  have hJ := Classical.choose_spec h
  rw [liftedSite_inj y hJ.1 hk hJ.2]

def rawBond {n : Nat} (y : Fin n) (k : Nat) : Fin n :=
  if k=0 then RearTrace.predecessor y else liftedSite y (k-1)

def nominate {Q n h : Nat} (y : Fin n) (s : Clock Q h) : Option (Fin n) :=
  (needed s).map (rawBond y)

theorem rawCode_eq_some {n d : Nat} (y e : Fin n) (hD : d+1<n) (j : Nat)
    (hj : j≤d+1) : rawCode y d e = some j ↔ e=rawBond y j := by
  obtain ⟨k,hk,rfl⟩ := liftedSite_of_site y e
  rw [rawCode_of_lift y d k hk]
  have hp : liftedSite y (n-1) = RearTrace.predecessor y := by
    have hn : 0<n := Nat.zero_lt_of_lt y.isLt
    have hh : rightNeighbor (liftedSite y (n-1)) = y := by
      rw [← liftedSite_succ,show n-1+1=n by omega,liftedSite_full]
    simpa [RearTrace.predecessor_right] using congrArg RearTrace.predecessor hh
  by_cases hj0 : j=0
  · subst j
    have hI : liftedSite y k=RearTrace.predecessor y ↔ k=n-1 := by
      rw [← hp]
      exact ⟨liftedSite_inj y hk (by omega),fun he => congrArg (liftedSite y) he⟩
    by_cases htop : k+1=n
    · simp only [rawBond,codeFromOffset,htop,if_true]
      exact iff_true_intro (hI.mpr (by omega)) |>.symm
    · by_cases hO : k≤d <;>
        simp [rawBond,codeFromOffset,htop,hO,hI,show k≠n-1 by omega]
  · have hI : liftedSite y k=liftedSite y (j-1) ↔ k=j-1 :=
      ⟨liftedSite_inj y hk (by omega),fun he => congrArg (liftedSite y) he⟩
    by_cases htop : k+1=n
    · simp [rawBond,Ne.symm hj0,hj0,codeFromOffset,htop,hI,show k≠j-1 by omega]
    · by_cases hO : k≤d
      · have hr : k+1=j ↔ k=j-1 := by omega
        simp [rawBond,hj0,codeFromOffset,htop,hO,hr,hI]
      · simp [rawBond,hj0,codeFromOffset,htop,hO,hI,show k≠j-1 by omega]

/-- The hit charged in the abstract clock is equality with one nominated
raw ring edge, chosen from the pre-mark state only. -/
theorem hit_is_raw_nomination {Q n d : Nat} (y e : Fin n) (hd : d+1<n)
    (s : Clock Q (d+1)) :
    hit s (rawCode y d e) = if nominate y s=some e then 1 else 0 := by
  have hh (j : Nat) (hj : j≤d+1) :
      some j = rawCode y d e ↔ some (rawBond y j) = some e := by
    rw [Eq.comm,rawCode_eq_some y e hd j hj,Option.some.injEq,Eq.comm]
  cases s with
  | done => rfl
  | active q w j =>
    have hJ := j.isLt
    cases w
    · simp [hit,nominate,needed,hh j.val (by omega)]
    · simp [hit,nominate,needed,hh (j.val+1) (by omega)]

/-- Direct composition of the physical row bridge and canonical worker
induction. The source state is read from the actual selected endpoints. -/
theorem physical_count_step {p c n d : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (y e : Fin n) (hm : MCOV x) (hc : COV x)
    (H : RankFresh.Corridor x y d)
    (q : Fin (2*c)) (w : Direction) (j : Fin (d+1))
    (hF : Encodes (physicalFrame x y d) (.active q w j))
    (hPay : e=liftedSite y d → geometricPay (x e) (x (rightNeighbor e)) = false) :
    ∃ s : Clock (2*c) (d+1), Encodes (physicalFrame (step x e) y d) s ∧
      MarkStep (.active q w j) (rawCode y d e) s := by
  obtain ⟨k,hk,rfl⟩ := liftedSite_of_site y e
  obtain ⟨cmd,hCode,hFrame⟩ := count_ring_projection hn x y k hk hm hc H q w j hF.2.1 hF.1
    (fun h => hPay (congrArg (liftedSite y) h))
  obtain ⟨s,hEnc,hStep⟩ := canonical_step q w j cmd
  exact ⟨s,hFrame.symm ▸ hEnc,(hCode.trans (rawCode_of_lift y d k hk).symm) ▸ hStep⟩

/-- Clean A1 (from the I1 authentication theorem) is exactly the
initial active COUNT state, not an already charged outward move. -/
theorem clean_a1_encodes {p c n d : Nat} (x : Config p c n) (y : Fin n)
    (hQ : 0<2*c) (j : Fin (d+1)) (hj : j.val+1=d+1)
    (hc : COV x)
    (hs : (x (liftedSite y (d+1))).source = .await ⟨0,hQ⟩)
    (hr : railsAt x y d j = .uc)
    (he : ∀ i : Fin (d+1), i.val<j.val → railsAt x y d i = .e) :
    Encodes (physicalFrame x y d) (.active ⟨0,hQ⟩ .outward j) := by
  have hL : (x (liftedSite y (d+1))).leader=false := by
    have hn : (x (rightNeighbor (liftedSite y d))).source ≠ .off := by
      rw [← liftedSite_succ,hs]
      intro hh; contradiction
    rw [liftedSite_succ]
    exact (hc _ hn).1
  refine ⟨?_,hs,hL⟩
  funext i
  change railsAt x y d i = shape .outward j i
  by_cases hi : i=j
  · subst i
    simpa [shape,worker] using hr
  · have hne : i.val≠j.val := fun h => hi (Fin.ext h)
    have hlt : i.val<j.val := by have := i.isLt; omega
    simp [shape,hi,hlt,he i hlt]

def ValidCountWord {p c n : Nat} (x : Config p c n) (y : Fin n) (d : Nat) :
    List (Fin n) → Prop
  | [] => True
  | e::w => MCOV x ∧ COV x ∧ RankFresh.Corridor x y d ∧
      (e = liftedSite y d → geometricPay (x e) (x (rightNeighbor e)) = false) ∧
      ValidCountWord (step x e) y d w

/-- Physical input words with every selected door unpaid are admitted
through the terminal birth itself. A continued word cannot pass that
birth because a fresh-epoch corridor requires a ghost prestate. -/
theorem physical_count_word {p c n d : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (y : Fin n) (w : List (Fin n))
    (s : Clock (2*c) (d+1)) (hStart : Encodes (physicalFrame x y d) s)
    (hValid : ValidCountWord x y d w) :
    ∃ t j, MarkTape s (w.map (rawCode y d)) t j ∧
      Encodes (physicalFrame (run x w) y d) t := by
  induction w generalizing x s with
  | nil => exact ⟨s,0,MarkTape.nil s,hStart⟩
  | cons e w ih =>
    obtain ⟨hm,hc,hC,hP,hW⟩ := hValid
    cases s with
    | done =>
      have hh : (x (liftedSite y (d+1))).leader = true := hStart
      rw [hC.ghost] at hh
      contradiction
    | active k g j =>
      obtain ⟨s',hE,hStep⟩ := physical_count_step hn x y e hm hc hC k g j hStart hP
      obtain ⟨t,m,hTape,hEnc⟩ := ih (step x e) s' hE hW
      exact ⟨t,hit (.active k g j) (rawCode y d e)+m,MarkTape.cons hStep hTape,hEnc⟩

/-- An actual first victim birth after clean A1 requires exactly the
claimed number of nominated raw-edge hits along the corresponding
COUNT execution. -/
theorem physical_birth_exact {p c n d : Nat} (hn : 4 ≤ n) (hQ : 0<2*c)
    (x : Config p c n) (y : Fin n) (w : List (Fin n)) (j : Fin (d+1))
    (hj : j.val+1=d+1)
    (hStart : Encodes (physicalFrame x y d) (.active ⟨0,hQ⟩ .outward j))
    (hValid : ValidCountWord x y d w)
    (hBirth : ((run x w) (liftedSite y (d+1))).leader=true) :
    MarkTape (.active ⟨0,hQ⟩ .outward j) (w.map (rawCode y d)) .done (2*(d+1)*(2*c)) := by
  obtain ⟨t,m,hTape,hEnd⟩ := physical_count_word hn x y w _ hStart hValid
  cases t with
  | done =>
    have hh := count_tape_exact hQ j hj _ _ hTape
    exact hh ▸ hTape
  | active k g z =>
    have hf : ((run x w) (liftedSite y (d+1))).leader=false := hEnd.2.2
    rw [hf] at hBirth
    contradiction

/-- The actual clean first exit from I1 produces count zero; the same
A1 mark is an uncharged starting condition for the separate timer clock. -/
theorem a1_to_clock {p c n d : Nat} (hn : 4≤n) (hQ : 0<2*c)
    (x : Config p c n) (y e : Fin n) (hm : MCOV x) (hc : COV x)
    (hC : RankFresh.Corridor x y d)
    (hs : (x (liftedSite y (d+1))).source=.i1)
    (hp : e=liftedSite y d → geometricPay (x e) (x (rightNeighbor e))=false)
    (hAuth : Auth (railsAt x y d))
    (hOut : (step x e (liftedSite y (d+1))).source≠.i1) :
    ∃ j : Fin (d+1), j.val+1=d+1 ∧
      Encodes (physicalFrame (step x e) y d) (.active ⟨0,hQ⟩ .outward j) := by
  have hh := ring_auth_step hn hQ x y e hm hc hC hs hp hAuth
  rcases hh with he | ⟨j,hj,_,ha,hR,hE⟩
  · exact (hOut he.1).elim
  · have hc' := (EntranceCover.cover_closed hn x e ⟨hm,hc⟩).2
    exact ⟨j,hj,clean_a1_encodes (step x e) y hQ j hj hc' ha hR hE⟩

/-- Literal pending epoch after a nonmerging P3. Before the first
selected incoming service the OFF byte stays OFF, including when
the victim is the selected initiator. The first unpaid door service
starts genuine I1/Ui over arbitrary residual rails. -/
theorem pending_off_epoch_step {p c n d : Nat} (hn : 4≤n)
    (x : Config p c n) (y e : Fin n) (hC : RankFresh.Corridor x y d)
    (hOff : (x (liftedSite y (d+1))).source = .off)
    (hp : e=liftedSite y d → geometricPay (x e) (x (rightNeighbor e))=false) :
    if e=liftedSite y d then
      (step x e (liftedSite y (d+1))).source=.i1 ∧
        Auth (railsAt (step x e) y d) ∧
        (step x e (liftedSite y (d+1))).leader=false
    else (step x e (liftedSite y (d+1))).source=.off ∧
      (step x e (liftedSite y (d+1))).leader=false := by
  by_cases he : e=liftedSite y d
  · rw [if_pos he]
    have hz : rightNeighbor e=liftedSite y (d+1) := by rw [he,liftedSite_succ]
    have hPair := FreshTimerEpoch.unpaid_ghost_launch (x e) (x (rightNeighbor e))
      (he.symm ▸ hC.first.marked) (hz.symm ▸ hC.ghost) (hz.symm ▸ hOff) (hp he)
    refine ⟨?_,?_,?_⟩
    · rw [← hz]; simpa [step,distinct hn e] using hPair.1
    · let j : Fin (d+1) := ⟨d,Nat.lt_succ_self _⟩
      apply launch_authenticated _ j rfl
      change (step x e (liftedSite y d)).rail = .ui
      rw [← he]
      simpa [step] using hPair.2.1
    · rw [← hz]; simpa [step,distinct hn e] using hPair.2.2
  · rw [if_neg he]
    let z := liftedSite y (d+1)
    have hZ : z≠rightNeighbor e := by
      intro h
      have hh : rightNeighbor (liftedSite y d) = rightNeighbor e :=
        (liftedSite_succ y d).symm.trans h
      have hh' := congrArg RearTrace.predecessor hh
      simp only [RearTrace.predecessor_right] at hh'
      exact he hh'.symm
    change (step x e z).source=.off ∧ (step x e z).leader=false
    by_cases hz : z=e
    · rw [hz]
      have hL := (pair_geometric_fields (x e) (x (rightNeighbor e))).2.1
      simpa [step,pair_left_source,hL] using
        And.intro (show (x e).source=.off from hz ▸ hOff)
          (show (x e).leader=false from hz ▸ hC.ghost)
    · have hKeep : step x e z=x z := by simp [step,hz,hZ]
      rw [hKeep]
      exact ⟨hOff,hC.ghost⟩

/-- Actual unpaid death installs an already authenticated I1/Ui epoch.
Together with pending_off_epoch_step this covers both kinds of fresh
gap start used by the stopped victim observer. -/
theorem unpaid_death_auth_start {p c n d : Nat} (hn : 4≤n)
    (x : Config p c n) (y : Fin n)
    (hKill : TenureOrigins.nativeKill (x (liftedSite y d)) (x (liftedSite y (d+1))))
    (hc : COV x)
    (hNoPay : geometricPay (x (liftedSite y d)) (x (liftedSite y (d+1))) = false) :
    let e := liftedSite y d
    (step x e (liftedSite y (d+1))).source=.i1 ∧
      Auth (railsAt (step x e) y d) := by
  let e := liftedSite y d
  have hz : liftedSite y (d+1)=rightNeighbor e := liftedSite_succ _ _
  have ho : (x (liftedSite y (d+1))).source=.off := by
    by_cases h : (x (liftedSite y (d+1))).source=.off
    · exact h
    · have hh := (hc e (hz ▸ h)).1
      rw [← hz,hKill.1] at hh
      contradiction
  have hh := FreshTimerEpoch.unpaid_kill_launch (x e) (x (liftedSite y (d+1))) hKill ho hNoPay
  have hLeft : (step x e e).rail=.ui := by simpa [step,hz] using hh.2.1
  have hRight : (step x e (liftedSite y (d+1))).source=.i1 := by
    simpa [step,hz,distinct hn e] using hh.1
  refine ⟨hRight,?_⟩
  let j : Fin (d+1) := ⟨d,Nat.lt_succ_self _⟩
  exact launch_authenticated _ j rfl hLeft

def clockNext {Q h : Nat} (s : Clock Q h) (e : Option Nat) : Clock Q h :=
  if hit s e = 0 then s else
  match s with
  | .done => .done
  | .active k .outward j =>
    if j.val=0 then .active k .inward j
    else .active k .outward ⟨j.val-1,by have := j.isLt; omega⟩
  | .active k .inward j =>
    if hj : j.val+1<h then .active k .inward ⟨j.val+1,hj⟩
    else if hk : k.val+1<Q then .active ⟨k.val+1,hk⟩ .outward j else .done

theorem clockNext_eq {Q h : Nat} {s t : Clock Q h} {e : Option Nat}
    (H : MarkStep s e t) : clockNext s e=t := by
  cases H with
  | stay _ _ h => simp [clockNext,h]
  | outward _ a b h =>
    have hh : b.val-1=a.val := by omega
    simp [clockNext,hit,needed,show b.val≠0 by omega] <;> exact Fin.ext hh
  | turn _ _ h => simp [clockNext,hit,needed,h]
  | inward _ a b h =>
    have hb := b.isLt
    simp [clockNext,hit,needed,h] <;> exact Fin.ext h
  | relaunch k k' d hd hk =>
    have hh := k'.isLt
    simp [clockNext,hit,needed,hd,show k.val+1<Q by omega] <;> exact Fin.ext hk
  | finish k d hd hk => simp [clockNext,hit,needed,hd,hk]

noncomputable def rawNext {Q n d : Nat} (y : Fin n)
    (s : Clock Q (d+1)) (e : Fin n) : Clock Q (d+1) :=
  clockNext s (rawCode y d e)

theorem counted_tape {Q n d : Nat} (y : Fin n) (hh : d+1<n)
    (s t : Clock Q (d+1)) (w : List (Fin n)) (q hits misses : Nat)
    (hW : MarkTape s (w.map (rawCode y d)) t q) :
    let z := GGTiming.runMarks (RankRace.countStep (rawNext y) (nominate y))
      (s,hits,misses) w
    z.1=t ∧ z.2.1=hits+q := by
  induction w generalizing s hits misses q with
  | nil =>
    cases hW with
    | nil => exact ⟨rfl,(Nat.add_zero _).symm⟩
  | cons e w ih =>
    cases hW with
    | @cons _ t₀ _ _ _ k hS hRest =>
      have hStep : rawNext y s e=t₀ := clockNext_eq hS
      change (GGTiming.runMarks (RankRace.countStep (rawNext y) (nominate y))
        (RankRace.countStep (rawNext y) (nominate y) (s,hits,misses) e) w).1=t ∧ _
      have hn := hit_is_raw_nomination y e hh s
      by_cases he : nominate y s=some e
      · simp only [GGTiming.runMarks,RankRace.countStep,he,if_true,hStep]
        have hI := ih t₀ k (hits+1) misses hRest
        have hN : hit s (rawCode y d e)=1 := by simp [he] at hn; exact hn
        simp [hN,← Nat.add_assoc]
        exact hI
      · simp only [GGTiming.runMarks,RankRace.countStep,he,if_false,hStep]
        have hI := ih t₀ k hits (misses+1) hRest
        have hN : hit s (rawCode y d e)=0 := by simp [he] at hn; exact hn
        simp [hN]
        exact hI

def pushMark {n : Nat} (w : List (Fin n)) (e : Fin n) : List (Fin n) := w++[e]

private theorem word_clock_id {n : Nat} (a b : List (Fin n)) :
    GGTiming.runMarks pushMark a b = a++b := by
  induction b generalizing a with
  | nil => simp [GGTiming.runMarks]
  | cons e w ih => simpa [GGTiming.runMarks,pushMark,List.append_assoc] using ih (a++[e])

private theorem more_marks_more_hits {α : Type} {n : Nat} (next : α → Fin n → α)
    (nom : α → Option (Fin n)) (z : α × Nat × Nat) (w : List (Fin n)) :
    z.2.1 ≤ (GGTiming.runMarks (RankRace.countStep next nom) z w).2.1 := by
  induction w generalizing z with
  | nil => exact Nat.le_refl _
  | cons e w ih =>
    have hstep : z.2.1 ≤ (RankRace.countStep next nom z e).2.1 := by
      unfold RankRace.countStep
      split <;> simp
    exact Nat.le_trans hstep (ih _)

/-- Sticky witnessed birth of the same fixed unpaid victim, beginning
with the observed A1 state. Padding cannot credit an unrelated later birth. -/
noncomputable def postA1BirthScore {p c n : Nat} (x : Config p c n) (y : Fin n) (d : Nat)
    (w : List (Fin n)) : Nat := by
  classical
  exact if ∃ a b, w=a++b ∧ ValidCountWord x y d a ∧
     ((run x a) (liftedSite y (d+1))).leader=true then 1 else 0

theorem postA1_birth_le_timer_mass {p c n d : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (y : Fin n) (hD : d+1<n)
    (hQ : 0<2*c) (j : Fin (d+1)) (hj : j.val+1=d+1)
    (hStart : Encodes (physicalFrame x y d) (.active ⟨0,hQ⟩ .outward j))
    (T : Nat) :
    RankRenewal.endpointSum pushMark (postA1BirthScore x y d) T [] ≤
      RankRace.timerMass (rawNext y) (nominate y) (Clock.active ⟨0,hQ⟩ .outward j)
        T (4*(c*(d+1))) := by
  classical
  let start : Clock (2*c) (d+1) := .active ⟨0,hQ⟩ .outward j
  let next := RankRace.countStep (rawNext (Q:=2*c) (d:=d) y) (nominate y)
  let K := 4*(c*(d+1))
  let g := fun s : Clock (2*c) (d+1) × Nat × Nat => if K≤s.2.1 then 1 else 0
  change RankRenewal.endpointSum pushMark (postA1BirthScore x y d) T [] ≤
    RankRenewal.endpointSum next g T (start,0,0)
  apply RankRace.endpointSum_le_of_common_words pushMark next _ _ [] (start,0,0) _ T
  intro w
  rw [word_clock_id,List.nil_append]
  unfold postA1BirthScore
  split
  · rename_i he
    obtain ⟨a,b,hw,hA,hB⟩ := he
    have hTape := physical_birth_exact hn hQ x y a j hj hStart hA hB
    have hCnt := (counted_tape y hD start .done a (2*(d+1)*(2*c)) 0 0 hTape).2
    change (GGTiming.runMarks next (start,0,0) a).2.1=0+2*(d+1)*(2*c) at hCnt
    have hM := more_marks_more_hits (rawNext y) (nominate y)
      (GGTiming.runMarks next (start,0,0) a) b
    have hK : 0+2*(d+1)*(2*c)=K := by
      unfold K
      rw [Nat.zero_add]
      calc
        2*(d+1)*(2*c) = (2*2)*(c*(d+1)) := by ac_rfl
        _ = _ := rfl
    rw [hK] at hCnt
    rw [hw,GGTiming.runMarks_append]
    have hLe : K≤(GGTiming.runMarks next (GGTiming.runMarks next (start,0,0) a) b).2.1 :=
      hCnt ▸ hM
    simp [g,hLe]
  · exact Nat.zero_le _

/-- Exact finite endpoint estimate for the post-A1 early branch and
application of the sharp timer tail on the original raw alphabet. -/
theorem postA1_early_gap_tail {p c n d : Nat} (hn : 4≤n) (hc : 12≤c)
    (x : Config p c n) (y : Fin n) (hD : d+1<n)
    (hQ : 0<2*c) (j : Fin (d+1)) (hj : j.val+1=d+1)
    (hStart : Encodes (physicalFrame x y d) (.active ⟨0,hQ⟩ .outward j)) :
    let h := d+1
    let T := 2*n*(c*h)
    256^h * RankRenewal.endpointSum pushMark (postA1BirthScore x y d) T [] ≤ n^T := by
  have hh := postA1_birth_le_timer_mass hn x y hD hQ j hj hStart (2*n*(c*(d+1)))
  have ht := RankRace.sharp_timer_gap_tail (rawNext y) (nominate y)
    (Clock.active ⟨0,hQ⟩ .outward j) c (d+1) (by omega) hc
  exact Nat.le_trans (Nat.mul_le_mul_left _ hh) ht

private theorem sConst (n a : Nat) : TaggedTail.sumEdge (fun _ : Fin n => a)=n*a := by
  induction n with
  | zero => simp [TaggedTail.sumEdge]
  | succ n ih =>
    have hh : (List.ofFn (fun _ : Fin n => a)).sum=n*a := ih
    simp [TaggedTail.sumEdge,List.ofFn_succ,hh,Nat.succ_mul,Nat.add_comm]

private theorem sMono {n : Nat} {f g : Fin n→Nat} (h : ∀ e, f e≤g e) :
    TaggedTail.sumEdge f≤TaggedTail.sumEdge g := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    simp only [TaggedTail.sumEdge,List.ofFn_succ,List.sum_cons]
    exact Nat.add_le_add (h 0) (ih (fun i => h i.succ))

private theorem sScale {n : Nat} (a : Nat) (f : Fin n→Nat) :
    TaggedTail.sumEdge (fun e => a*f e)=a*TaggedTail.sumEdge f := by
  induction n with
  | zero => simp [TaggedTail.sumEdge]
  | succ n ih =>
    simp only [TaggedTail.sumEdge,List.ofFn_succ,List.sum_cons]
    rw [Nat.mul_add]
    exact congrArg (a*f 0+·) (ih (fun i => f i.succ))

private theorem endpoint_add_time {α : Type} {n : Nat} (next : α → Fin n → α)
    (f : α → Nat) (t m : Nat) (x : α) :
    RankRenewal.endpointSum next f (t+m) x =
      RankRenewal.endpointSum next (fun s => RankRenewal.endpointSum next f m s) t x := by
  induction t generalizing x with
  | zero => simp [RankRenewal.endpointSum]
  | succ t ih =>
    rw [Nat.succ_add]
    simp only [RankRenewal.endpointSum,ih]

private theorem endpoint_scale {α : Type} {n : Nat} (next : α → Fin n → α)
    (f : α → Nat) (k t : Nat) (x : α) :
    RankRenewal.endpointSum next (fun y => k*f y) t x =
      k*RankRenewal.endpointSum next f t x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih => simp only [RankRenewal.endpointSum,ih,sScale]

private theorem pad_le {α : Type} {n : Nat} (next : α → Fin n → α)
    (f : α → Nat) (mono : ∀ x e, f x≤f (next x e)) (t m : Nat) (x : α) :
    n^m*RankRenewal.endpointSum next f t x ≤ RankRenewal.endpointSum next f (t+m) x := by
  have hb (x : α) (m : Nat) :
      n^m*f x ≤ RankRenewal.endpointSum next f m x := by
    induction m generalizing x with
    | zero => simp [RankRenewal.endpointSum]
    | succ m ih =>
      change _ ≤ TaggedTail.sumEdge (fun e => RankRenewal.endpointSum next f m (next x e))
      have hPoint (e : Fin n) := Nat.le_trans (Nat.mul_le_mul_left (n^m) (mono x e)) (ih (next x e))
      calc
        _ = TaggedTail.sumEdge (fun _ : Fin n => n^m*f x) := by rw [sConst,Nat.pow_succ]; ac_rfl
        _ ≤ _ := sMono hPoint
  rw [← endpoint_scale,endpoint_add_time]
  induction t generalizing x with
  | zero => exact hb x m
  | succ t ih =>
    change TaggedTail.sumEdge _ ≤ TaggedTail.sumEdge _
    exact sMono (fun e => ih (next x e))

theorem postA1_score_sticky {p c n d : Nat} (x : Config p c n) (y : Fin n)
    (w : List (Fin n)) (e : Fin n) :
    postA1BirthScore x y d w ≤ postA1BirthScore x y d (pushMark w e) := by
  classical
  unfold postA1BirthScore
  split
  · rename_i hh
    obtain ⟨a,b,hW,hV,hB⟩ := hh
    have hn : ∃ u v, pushMark w e=u++v ∧ ValidCountWord x y d u ∧
        ((run x u) (liftedSite y (d+1))).leader=true :=
      ⟨a,b++[e],by simp [pushMark,hW,List.append_assoc],hV,hB⟩
    rw [if_pos hn]; exact Nat.le_refl _
  · exact Nat.zero_le _

/-- The post-A1 estimate holds at every remaining horizon at most the
gap's full cutoff. Padding divides out the extra raw alphabet factors,
so a random A1 time need not be summed over by a union bound. -/
theorem postA1_early_le_cutoff {p c n d : Nat} (hn : 4≤n) (hc : 12≤c)
    (x : Config p c n) (y : Fin n) (hD : d+1<n)
    (hQ : 0<2*c) (j : Fin (d+1)) (hj : j.val+1=d+1)
    (hStart : Encodes (physicalFrame x y d) (.active ⟨0,hQ⟩ .outward j))
    (t : Nat) (ht : t≤2*n*(c*(d+1))) :
    256^(d+1) * RankRenewal.endpointSum pushMark (postA1BirthScore x y d) t [] ≤ n^t := by
  let T := 2*n*(c*(d+1))
  let m := T-t
  have hTM : t+m=T := by unfold m T; omega
  have hh := pad_le pushMark (postA1BirthScore x y d) (postA1_score_sticky x y) t m []
  rw [hTM] at hh
  have hp := postA1_early_gap_tail hn hc x y hD hQ j hj hStart
  change 256^(d+1)*RankRenewal.endpointSum pushMark (postA1BirthScore x y d) T []≤n^T at hp
  have h := Nat.le_trans (Nat.mul_le_mul_left (256^(d+1)) hh) hp
  apply Nat.le_of_mul_le_mul_left _ (show 0<n^m from Nat.pow_pos (by omega))
  rw [← Nat.pow_add,show m+t=T by omega]
  simpa only [Nat.mul_left_comm] using h

end L4.FreshCountHits
