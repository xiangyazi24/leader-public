import Leader.L4.WindowSealed
import Leader.L4.TripleLongMonitor

/-! The scoped sealed long-race monitor. A foreign native event is a raw
keep mark, not a reason to freeze the physical configuration. -/
namespace L4.WindowScopedRace
open TriplePhase TripleRenewal TripleLongMonitor SevenTagCharge WindowLocal

structure State (p c n : Nat) where
  ledger : Ledger p c n
  left : Phase
  right : Phase
  mode : Mode
  exited : Bool

def next {p c n : Nat} (group cert : List (Fin n)) (v : Fin n) (a b : Nat)
    (x : State p c n) (e : Fin n) : State p c n :=
  let localExit := decide (route group cert none x.ledger e ≠ Event.keep)
  let l := x.left.tick v a e
  let r := x.right.tick (liftedSite v (a+1)) b e
  let m := if x.mode.done then x.mode else if localExit then .success
    else survivingMode v a b x.mode x.left x.right l r e
  ⟨advance x.ledger e,l,r,m,x.exited || localExit⟩

def ready {p c n : Nat} (x : State p c n) : Prop := x.mode.done=true

theorem project_step {p c n : Nat} (group cert : List (Fin n)) (v : Fin n) (a b : Nat)
    (x : State p c n) (e : Fin n) :
    (next group cert v a b x e).ledger = advance x.ledger e := rfl

theorem done_sticky {p c n : Nat} (group cert : List (Fin n)) (v : Fin n) (a b : Nat)
    (x : State p c n) (e : Fin n) (h : ready x) :
    (next group cert v a b x e).mode=x.mode := by
  simp [next,show x.mode.done=true from h]

theorem stop_priority {p c n : Nat} (group cert : List (Fin n)) (v : Fin n) (a b : Nat)
    (x : State p c n) (e : Fin n) (h : ¬ready x)
    (he : route group cert none x.ledger e ≠ Event.keep) :
    (next group cert v a b x e).mode=.success := by
  simp [next,he,show x.mode.done=false from Bool.eq_false_iff.mpr h]

theorem mode_keep {p c n : Nat} (group cert : List (Fin n)) (v : Fin n) (a b : Nat)
    (x : State p c n) (e : Fin n) (h : ¬ready x)
    (he : route group cert none x.ledger e = Event.keep) :
    (next group cert v a b x e).mode =
      survivingMode v a b x.mode x.left x.right
        (x.left.tick v a e) (x.right.tick (liftedSite v (a+1)) b e) e := by
  simp [next,he,show x.mode.done=false from Bool.eq_false_iff.mpr h]

structure Seal {p c n : Nat} (x : State p c n) (v : Fin n) (a b : Nat)
    (l m r s t u : Fin n) : Prop where
  base : rightNeighbor s=v
  left : CertifiedSector x.ledger l m s t a
  right : CertifiedSector x.ledger m r t u b
  leftPhase : x.left.Holds x.ledger.config v a
  rightPhase : x.right.Holds x.ledger.config (liftedSite v (a+1)) b

theorem Seal.paired {p c n a b : Nat} {x : State p c n} {v l m r s t u : Fin n}
    (h : Seal x v a b l m r s t u) (hsize : a+b+2<n) :
    Paired x.ledger.config v a b x.left x.right := by
  have ht : liftedSite v (a+1)=rightNeighbor t := h.base ▸ h.left.terminal_site
  refine ⟨⟨?_,?_,?_,?_,?_,by omega,Or.inl hsize⟩,h.leftPhase,h.rightPhase⟩
  · rw [← h.base]; exact h.left.left_live.2
  · rw [ht]; exact h.left.right_live.2
  · rw [ht,h.right.terminal_site]; exact h.right.right_live.2
  · rw [← h.base]; exact h.left.gap
  · rw [ht]; exact h.right.gap

theorem seal_keep {p c n a b : Nat} (hn : 4≤n) (initial : Config p c n)
    (group cert : List (Fin n)) {x : State p c n} {v l m r s t u : Fin n} (e : Fin n)
    (hsize : a+b+2<n) (hv : Valid x.ledger initial)
    (hs : cert ⊆ group) (hl : l ∈ cert) (hm : m ∈ cert) (hr : r ∈ cert)
    (h : Seal x v a b l m r s t u) (he : route group cert none x.ledger e = Event.keep) :
    Seal (next group cert v a b x e) v a b l m r s t u := by
  have hL := h.leftPhase
  rw [← h.base] at hL
  have hR := h.rightPhase
  rw [← h.base,h.left.terminal_site] at hR
  have H := WindowSealed.certified_twin_tick_keep hn initial x.ledger group cert none
    e l m r s t u (by omega) (by omega) hv hs hl hm hr h.left h.right he x.left x.right hL hR
  refine ⟨h.base,H.1.1,H.2.1,?_,?_⟩
  · simpa only [next,h.base] using H.1.2
  · have ht : liftedSite v (a+1)=rightNeighbor t := h.base ▸ h.left.terminal_site
    simpa only [next,ht] using H.2.2

/-- On the true terminal attacker mark the middle certified leader is
physically killed, not merely reported as a global event. Hence the
priority of the local route prevents a surviving dummy-cycle impact. -/
theorem live_no_impact {p c n a b : Nat} (hn : 4≤n) (initial : Config p c n)
    (group cert : List (Fin n)) {x : State p c n} {v l m r s t u : Fin n}
    (e : Fin n) (q : Nat) (hsize : a+b+2<n) (hv : Valid x.ledger initial)
    (hs : cert ⊆ group) (hm : m ∈ cert) (h : Seal x v a b l m r s t u)
    (he : route group cert none x.ledger e = Event.keep)
    (hL : x.left=.forward .live q) (hR : TripleVulnerable.DummyCycle x.right) :
    ¬(q=a ∧ e=liftedSite v a) := by
  rintro ⟨hQ,rfl⟩
  subst q
  have hp := h.paired hsize
  have ht : rightNeighbor (liftedSite v a)=rightNeighbor t := by
    rw [← liftedSite_succ,← h.base,h.left.terminal_site]
  have hND := certified_no_death_on_keep hn initial x.ledger group cert none
    (liftedSite v a) t m hv hs hm h.left.right_live he ht
  have hV := TripleVulnerable.cycle_vulnerable _ _ _ hp.target hR
  have hB : (x.ledger.config (liftedSite v a)).bullet=.live := by
    have H := hp.attacker
    rw [hL] at H
    simpa [Kind.bullet] using H.unique a (Nat.le_refl _)
  have hT := hp.geom.second_leader
  rw [liftedSite_succ] at hV hT
  have hShield : (fireResponder (x.ledger.config (rightNeighbor (liftedSite v a)))).shield = false := by
    rcases hV with hV | ⟨hV,hShield⟩
    · simp [fireResponder,hT,hV]
    · simp [fireResponder,hT,hV,hShield]
  have hDeath := (nativeDeath_iff _ _).mpr
    ⟨hT, TripleResidual.poised_live _ (.inl hB), hShield⟩
  rw [hND] at hDeath
  contradiction

/-- Initial physical ledger reference and fixed certified endpoints for one trial. -/
structure Context {p c n : Nat} (initial : Config p c n) (group cert : List (Fin n))
    (v : Fin n) (a b : Nat) where
  hn : 4≤n
  size : a+b+2<n
  l : Fin n
  m : Fin n
  r : Fin n
  s : Fin n
  t : Fin n
  u : Fin n
  sub : cert ⊆ group
  left_mem : l ∈ cert
  mid_mem : m ∈ cert
  right_mem : r ∈ cert

variable {p c n : Nat} {initial : Config p c n} {group cert : List (Fin n)}
  {v : Fin n} {a b : Nat}

def Context.Holds (C : Context initial group cert v a b) (x : State p c n) : Prop :=
  Valid x.ledger initial ∧ Seal x v a b C.l C.m C.r C.s C.t C.u

def Context.Good (C : Context initial group cert v a b) (x : State p c n) : Prop :=
  x.exited=true ∨ C.Holds x

theorem Context.holds_keep (C : Context initial group cert v a b) (x : State p c n)
    (e : Fin n) (h : C.Holds x) (he : route group cert none x.ledger e=Event.keep) :
    C.Holds (next group cert v a b x e) :=
  ⟨valid_step C.hn x.ledger initial e h.1,
    seal_keep C.hn initial group cert e C.size h.1 C.sub C.left_mem C.mid_mem C.right_mem h.2 he⟩

theorem Context.good_step (C : Context initial group cert v a b) (x : State p c n)
    (e : Fin n) (h : C.Good x) :
    C.Good (next group cert v a b x e) := by
  by_cases he : route group cert none x.ledger e=Event.keep
  · cases h with
    | inl h => exact Or.inl (by simp [next,h])
    | inr h => exact Or.inr (C.holds_keep x e h he)
  · exact Or.inl (by simp [next,he])

theorem Context.holds_of_active (C : Context initial group cert v a b) (x : State p c n)
    (h : C.Good x) (hs : x.exited=false) : C.Holds x :=
  h.resolve_left (by simp [hs])

theorem survives_dummy_attack (C : Context initial group cert v a b) (x : State p c n)
    (e : Fin n) (q : Nat) (h : C.Holds x)
    (hL : x.left=.forward .live q) (hR : TripleVulnerable.DummyCycle x.right)
    (he : route group cert none x.ledger e=Event.keep) (hq : q≤a) :
    ∃ q', x.left.tick v a e=.forward .live q' ∧ q≤q' ∧ q'≤a := by
  have hf := live_no_impact C.hn initial group cert e q C.size h.1 C.sub C.mid_mem h.2 he hL hR
  rw [hL]
  by_cases he : e=liftedSite v q
  · have hq' : q<a := by
      by_cases h : q=a
      · exact (hf ⟨h,h ▸ he⟩).elim
      · omega
    exact ⟨q+1,by simp [Phase.tick,he,hq'],by omega,by omega⟩
  · exact ⟨q,by simp [Phase.tick,he],Nat.le_refl _,hq⟩

theorem mode_shape_step (C : Context initial group cert v a b) (hA : 2*(b+1)<a+1)
    (x : State p c n) (e : Fin n) (hG : C.Good x)
    (hActive : x.exited=true → ready x) (hX : Shape a b x.mode x.left x.right) :
    Shape a b (next group cert v a b x e).mode (next group cert v a b x e).left
      (next group cert v a b x e).right := by
  by_cases hD : ready x
  · rw [done_sticky group cert v a b x e hD]
    have hh : x.mode.done=true := hD
    cases hM : x.mode <;> simp [Shape,hM,Mode.done] at hh ⊢
  by_cases hS : route group cert none x.ledger e=Event.keep
  · have hh : C.Holds x := hG.resolve_left (fun hs => hD (hActive hs))
    have hp := hh.2.paired C.size
    rw [mode_keep group cert v a b x e hD hS]
    change Shape a b
      (survivingMode v a b x.mode x.left x.right (x.left.tick v a e)
        (x.right.tick (liftedSite v (a+1)) b e) e)
      (x.left.tick v a e) (x.right.tick (liftedSite v (a+1)) b e)
    let j := liftedSite v (a+1)
    let l' := x.left.tick v a e
    let r' := x.right.tick j b e
    cases hM : x.mode with
    | seek =>
      change Shape a b (if x.left.isReady then if e=v then onPosition a b l' r'
        else if rightNeighbor e=v then .failed else .seek else .seek) l' r'
      by_cases hl : x.left.isReady=true
      · rw [if_pos hl]
        by_cases he : e=v
        · rw [if_pos he]
          have hL : l'=.forward .live 1 := by
            simp [l',isReady_eq _ hl,he,Phase.tick,show a≠0 by omega]
          rw [hL]
          exact shape_onPosition a b 1 r' (by omega) (by omega)
        · rw [if_neg he]
          split <;> trivial
      · rw [if_neg hl]
        trivial
    | position =>
      rcases (show ∃ q, x.left=.forward .live q ∧ q≤a ∧ 2*(b+1)<a+1-q from by rw [hM] at hX; exact hX)
        with ⟨q,hq,hB,hR⟩
      by_cases he : e=liftedSite v a
      ·
        have hq' : q<a := by omega
        have hn' : a<n := by have := hp.geom.at_least_two; omega
        subst e
        have hN : liftedSite v a≠liftedSite v q :=
          fun h => (Nat.ne_of_gt hq') (liftedSite_inj v hn' (by omega) h)
        -- The final bond is harmless while the shot is still behind it.
        have hOld : x.left.tick v a (liftedSite v a)=x.left := by simp [hq,Phase.tick,hN]
        change Shape a b (onPosition a b l' r') l' r'
        have hL : l'=.forward .live q := hOld.trans hq
        rw [hL]
        exact shape_onPosition a b q r' hB (by omega)
      · obtain ⟨q',hL,_,hq',hi⟩ := forward_tick_in_range v a q e hB he
        have hLt : l'=.forward .live q' := by simpa [l',hq] using hL
        change Shape a b (onPosition a b l' r') l' r'
        rw [hLt]
        exact shape_onPosition a b q' r' hq' (by omega)
    | raceReady =>
      have hh := (show Shape a b .raceReady x.left x.right from by rw [hM] at hX; exact hX).1
      obtain ⟨q,hq,hBound,hShot⟩ := hh
      change Shape a b (if e=liftedSite v a ∧ shotLeft a x.left=1 then .failed else
          if r'.isReady then .awaitRight else .raceReady) l' r'
      by_cases he : e=liftedSite v a ∧ shotLeft a x.left=1
      · rw [if_pos he]; trivial
      · rw [if_neg he]
        have hh : ∃ q', l'=.forward .live q' ∧ q≤q' ∧ q'≤a := by
          by_cases he' : e=liftedSite v a
          · have hQ : q<a := by
              by_cases hEq : q=a
              · exact (he ⟨he',by rw [hq,hEq]; simp [shotLeft]⟩).elim
              · omega
            have hN : e≠liftedSite v q := by
              rw [he']
              intro h
              have hn' := hp.geom.at_least_two
              exact (Nat.ne_of_gt hQ) (liftedSite_inj v (by omega) (by omega) h)
            exact ⟨q,by simp [l',hq,Phase.tick,hN],Nat.le_refl _,hBound⟩
          · obtain ⟨q',hL,hm,hq',_⟩ := forward_tick_in_range v a q e hBound he'
            exact ⟨q',by simpa [l',hq] using hL,hm,hq'⟩
        obtain ⟨q',hLt,hm,hq'⟩ := hh
        cases hr : r'.isReady
        · rw [if_neg (by simp)]
          exact ⟨⟨q',hLt,hq',by omega⟩,hr⟩
        · simp only [if_true]
          exact ⟨⟨q',hLt,hq',by omega⟩,hr⟩
    | awaitRight =>
      obtain ⟨⟨q,hq,hB,hShot⟩,hr⟩ := (show Shape a b .awaitRight x.left x.right from by rw [hM] at hX; exact hX)
      have hR : x.right=.ready := isReady_eq _ hr
      obtain ⟨q',hL,hm,hq'⟩ := survives_dummy_attack C x e q hh hq
        (by rw [hR]; trivial) hS hB
      have hW : ∃ q, l'=.forward .live q ∧ q≤a ∧ a+1-q≤2*(b+1) :=
        ⟨q',hL,hq',by omega⟩
      change Shape a b (if e=j then .failed else if rightNeighbor e=j then .raceDummy
        else .awaitRight) l' r'
      by_cases he : e=j
      · rw [if_pos he]; trivial
      · rw [if_neg he]
        by_cases hi : rightNeighbor e=j
        · rw [if_pos hi]
          have hR' : r'=.forward .dummy 0 := by rw [show r'=x.right.tick j b e from rfl,hR]
                                                exact ready_tick_incoming j b e hi he
          exact ⟨hW,0,.inl hR'⟩
        · rw [if_neg hi]
          exact ⟨hW,by simp [r',hR,Phase.tick,he,hi,Phase.isReady]⟩
    | raceDummy =>
      obtain ⟨⟨q,hq,hB,hShot⟩,⟨k,hk⟩⟩ := (show Shape a b .raceDummy x.left x.right from by rw [hM] at hX; exact hX)
      have hr : TripleVulnerable.DummyCycle x.right := by
        rcases hk with hk|hk <;> rw [hk] <;> trivial
      have hN : x.right.isReady=false := by
        rcases hk with hk|hk <;> rw [hk] <;> rfl
      obtain ⟨q',hL,hm,hq'⟩ := survives_dummy_attack C x e q hh hq hr hS hB
      have hCycle : TripleVulnerable.DummyCycle r' := TripleVulnerable.dummy_cycle_on_tick j b _ e hr
        (by rw [hN]; intro hh; contradiction)
      change Shape a b (if r'.isReady then .failed else .raceDummy) l' r'
      cases hR : r'.isReady
      · rw [if_neg (by simp)]
        refine ⟨⟨q',hL,hq',by omega⟩,?_⟩
        cases hg : r' with
        | ready => simp [hg,Phase.isReady] at hR
        | forward kind k =>
          cases kind
          · exact ⟨k,.inl rfl⟩
          · rw [hg] at hCycle; exact False.elim hCycle
        | returning kind k =>
          cases kind
          · exact ⟨k,.inr rfl⟩
          · rw [hg] at hCycle; exact False.elim hCycle
      · simp only [if_true]; trivial
    | failed => trivial
    | success => trivial
  · rw [stop_priority group cert v a b x e hD hS]
    trivial

theorem ready_of_exited_step (x : State p c n)
    (h : x.exited=true → ready x) (e : Fin n) :
    (next group cert v a b x e).exited=true → ready (next group cert v a b x e) := by
  intro hE
  by_cases hD : ready x
  · unfold ready
    rw [done_sticky group cert v a b x e hD]
    exact hD
  · by_cases he : route group cert none x.ledger e=Event.keep
    · exact (hD (h (by simpa [next,he] using hE))).elim
    · unfold ready
      rw [stop_priority group cert v a b x e hD he]
      rfl

def workEdge (v : Fin n) (a : Nat) (x : State p c n) : Fin n :=
  if x.mode=.awaitRight then liftedSite v (a+1) else nominate v x.left

theorem reserve_step (C : Context initial group cert v a b)
    (hA : 2*(b+1)<a+1) (x : State p c n) (e : Fin n)
    (hG : C.Good x) (hActive : x.exited=true → ready x)
    (hX : Shape a b x.mode x.left x.right) (hD : ¬ready x) :
    reserve a b (next group cert v a b x e).mode (next group cert v a b x e).left +
      (if e=workEdge v a x then 1 else 0) ≤ reserve a b x.mode x.left := by
  have hd : x.mode.done=false := Bool.eq_false_iff.mpr hD
  by_cases hS : route group cert none x.ledger e ≠ Event.keep
  · rw [stop_priority group cert v a b x e hD hS]
    have h := reserve_positive a b x.mode x.left x.right hX hd
    change 0+(if e=workEdge v a x then 1 else 0)≤reserve a b x.mode x.left
    split <;> omega
  have hSF : route group cert none x.ledger e=Event.keep := Classical.not_not.mp hS
  have hh : C.Holds x := hG.resolve_left (fun hs => hD (hActive hs))
  have hp := hh.2.paired C.size
  rw [mode_keep group cert v a b x e hD hSF]
  let j := liftedSite v (a+1)
  let l' := x.left.tick v a e
  let r' := x.right.tick j b e
  change reserve a b (survivingMode v a b x.mode x.left x.right l' r' e) l' +
    (if e=workEdge v a x then 1 else 0) ≤ reserve a b x.mode x.left
  cases hM : x.mode with
  | seek =>
    have hW : workEdge v a x=nominate v x.left := by simp [workEdge,hM]
    rw [hW]
    by_cases hr : x.left.isReady=true
    · have hl := isReady_eq _ hr
      rw [hl,show reserve a b .seek .ready=a+2*(b+1)+2 by simp [reserve,serviceLeft]]
      change reserve a b
        (if e=v then onPosition a b l' r' else if rightNeighbor e=v then .failed else .seek)
        l'+(if e=v then 1 else 0)≤a+2*(b+1)+2
      by_cases he : e=v
      · rw [if_pos he,if_pos he]
        have hL : l'=.forward .live 1 := by simp [l',hl,he,Phase.tick,show a≠0 by omega]
        have h := onPosition_reserve_le a b l' r'
        rw [hL] at h ⊢
        simp only [shotLeft] at h
        omega
      · rw [if_neg he,if_neg he]
        by_cases hi : rightNeighbor e=v
        · rw [if_pos hi]
          simp [reserve]
        · have hL : l'=.ready := by simp [l',hl,Phase.tick,he,hi]
          rw [if_neg hi,hL]
          simp [reserve,serviceLeft]
    · have hR := Bool.eq_false_iff.mpr hr
      have hV := portValid _ _ _ hp.attacker
      have hh : serviceLeft a l'+(if e=nominate v x.left then 1 else 0)≤serviceLeft a x.left := by
        by_cases he : e=nominate v x.left
        · rw [if_pos he]
          have h : serviceLeft a l'+1=serviceLeft a x.left := by
            unfold l'
            rw [he]
            exact nonready_nominated_spends v a x.left hR hV
          omega
        · rw [if_neg he,show l'=x.left from idle_nonready v a x.left e hR he,Nat.add_zero]
          exact Nat.le_refl _
      have hM' : survivingMode v a b .seek x.left x.right l' r' e=.seek := by
        simp only [survivingMode,if_neg hr]
      rw [hM']
      change serviceLeft a l'+a+2*(b+1)+2+(if e=nominate v x.left then 1 else 0) ≤
        serviceLeft a x.left+a+2*(b+1)+2
      omega
  | position =>
    obtain ⟨q,hq,hB,hR⟩ := (show Shape a b .position x.left x.right from hM ▸ hX)
    have hW : workEdge v a x=liftedSite v q := by simp [workEdge,hM,hq,nominate]
    rw [hW,hq]
    change reserve a b (onPosition a b l' r') l'+(if e=liftedSite v q then 1 else 0)≤
      a+1-q+2*(b+1)+1
    have hT : ¬(q=a ∧ e=liftedSite v a) := by intro hh; omega
    have hshot := shot_nominated_delta v a q e hB hT
    have h := onPosition_reserve_le a b l' r'
    have hEq : l'=(Phase.forward .live q).tick v a e := by simp [l',hq]
    rw [←hEq] at hshot
    change shotLeft a l'+(if e=liftedSite v q then 1 else 0)=a+1-q at hshot
    omega
  | raceReady =>
    obtain ⟨⟨q,hq,hB,_⟩,_⟩ := (show Shape a b .raceReady x.left x.right from hM ▸ hX)
    have hW : workEdge v a x=liftedSite v q := by simp [workEdge,hM,hq,nominate]
    rw [hW,hq]
    change reserve a b (if e=liftedSite v a ∧ a+1-q=1 then .failed else
        if r'.isReady then .awaitRight else .raceReady) l'+
        (if e=liftedSite v q then 1 else 0)≤a+1-q+2*(b+1)+1
    by_cases he : e=liftedSite v a ∧ a+1-q=1
    · rw [if_pos he]
      change 0+(if e=liftedSite v q then 1 else 0)≤_
      split <;> omega
    · rw [if_neg he]
      have hT : ¬(q=a ∧ e=liftedSite v a) := by
        rintro ⟨rfl,hh⟩
        exact he ⟨hh,by omega⟩
      have hshot := shot_nominated_delta v a q e hB hT
      have hEq : l'=(Phase.forward .live q).tick v a e := by simp [l',hq]
      rw [←hEq] at hshot
      change shotLeft a l'+(if e=liftedSite v q then 1 else 0)=a+1-q at hshot
      by_cases hr : r'.isReady=true
      · rw [if_pos hr]
        change shotLeft a l'+1+(if e=liftedSite v q then 1 else 0)≤_
        omega
      · rw [if_neg hr]
        change shotLeft a l'+2*(b+1)+1+(if e=liftedSite v q then 1 else 0)≤_
        omega
  | awaitRight =>
    obtain ⟨⟨q,hq,hB,_⟩,hr⟩ := (show Shape a b .awaitRight x.left x.right from hM ▸ hX)
    have hCycle : TripleVulnerable.DummyCycle x.right := by rw [isReady_eq _ hr]; trivial
    have hT := live_no_impact C.hn initial group cert e q C.size hh.1 C.sub C.mid_mem hh.2 hSF hq hCycle
    have hshot := shot_nominated_delta v a q e hB hT
    have hEq : l'=(Phase.forward .live q).tick v a e := by simp [l',hq]
    rw [←hEq] at hshot
    change shotLeft a l'+(if e=liftedSite v q then 1 else 0)=a+1-q at hshot
    have hW : workEdge v a x=j := by simp [workEdge,hM,j]
    rw [hW,hq]
    change reserve a b (if e=j then .failed else if rightNeighbor e=j then .raceDummy
      else .awaitRight) l'+(if e=j then 1 else 0)≤a+1-q+1
    by_cases he : e=j
    · rw [if_pos he,if_pos he]
      change 0+1≤_
      omega
    · rw [if_neg he,if_neg he,Nat.add_zero]
      by_cases hi : rightNeighbor e=j
      · rw [if_pos hi]
        change shotLeft a l'≤_
        omega
      · rw [if_neg hi]
        change shotLeft a l'+1≤_
        omega
  | raceDummy =>
    obtain ⟨⟨q,hq,hB,_⟩,⟨k,hk⟩⟩ := (show Shape a b .raceDummy x.left x.right from hM ▸ hX)
    have hCycle : TripleVulnerable.DummyCycle x.right := by rcases hk with hk|hk <;> rw [hk] <;> trivial
    have hT := live_no_impact C.hn initial group cert e q C.size hh.1 C.sub C.mid_mem hh.2 hSF hq hCycle
    have hshot := shot_nominated_delta v a q e hB hT
    have hEq : l'=(Phase.forward .live q).tick v a e := by simp [l',hq]
    rw [←hEq] at hshot
    change shotLeft a l'+(if e=liftedSite v q then 1 else 0)=a+1-q at hshot
    have hW : workEdge v a x=liftedSite v q := by simp [workEdge,hM,hq,nominate]
    rw [hW,hq]
    change reserve a b (if r'.isReady then .failed else .raceDummy) l'+
      (if e=liftedSite v q then 1 else 0)≤a+1-q
    split
    · simp only [reserve,Nat.zero_add]
      omega
    · exact Nat.le_of_eq hshot
  | failed | success => simp [hM,Mode.done] at hd

theorem shape_run (C : Context initial group cert v a b) (hA : 2*(b+1)<a+1)
    (x : State p c n) (w : List (Fin n)) (hG : C.Good x)
    (hActive : x.exited=true → ready x) (hX : Shape a b x.mode x.left x.right) :
    let y := GGTiming.runMarks (next group cert v a b) x w
    C.Good y ∧ (y.exited=true → ready y) ∧ Shape a b y.mode y.left y.right := by
  induction w generalizing x with
  | nil => exact ⟨hG,hActive,hX⟩
  | cons e w ih =>
    exact ih (next group cert v a b x e)
      (C.good_step x e hG) (ready_of_exited_step x hActive e) (mode_shape_step C hA x e hG hActive hX)

theorem reserve_mean (C : Context initial group cert v a b) (hA : 2*(b+1)<a+1)
    (x : State p c n) (hG : C.Good x) (hActive : x.exited=true → ready x)
    (hX : Shape a b x.mode x.left x.right) :
    IIDExpectedHittingTimeAtMost (next group cert v a b) ready x (n*reserve a b x.mode x.left) := by
  let fold := GGTiming.runMarks (next group cert v a b) x
  let Q : FixedResidual.Countdown (next group cert v a b) ready x :=
    ⟨fun w => reserve a b (fold w).mode (fold w).left, fun w => workEdge v a (fold w),?_⟩
  · exact FixedResidual.expected_of_countdown _ _ _ Q
  · intro w hd e
    have hk := shape_run C hA x w hG hActive hX
    have H := reserve_step C hA (fold w) e hk.1 hk.2.1 hk.2.2 hd
    simpa only [fold,GGTiming.runMarks_append,GGTiming.runMarks] using H

abbrev Cursor (p c n : Nat) := Ledger p c n × Bool

def cursorNext (group cert : List (Fin n)) (x : Cursor p c n) (e : Fin n) :
    Cursor p c n :=
  ⟨advance x.1 e,x.2 || decide (route group cert none x.1 e ≠ Event.keep)⟩

def project (x : State p c n) : Cursor p c n := ⟨x.ledger,x.exited⟩

def Cursor.exit (x : Cursor p c n) : Prop := x.2=true

def Context.Certified (C : Context initial group cert v a b) (z : Cursor p c n) : Prop :=
  ∃ lp rp, C.Holds ⟨z.1,lp,rp,.seek,z.2⟩

def stage (C : Context initial group cert v a b) (z : Cursor p c n)
    (lp rp : Phase) (h : C.Holds ⟨z.1,lp,rp,.seek,z.2⟩) :
    Stage (cursorNext group cert) z where
  State := State p c n
  start := ⟨z.1,lp,rp,.seek,z.2⟩
  next := next group cert v a b
  project := project
  ready := ready
  reachable := C.Good
  projInit := rfl
  projStep _ _ := rfl
  reachStart := Or.inr h
  reachStep x e := C.good_step x e

theorem proper_start (C : Context initial group cert v a b) (z : Cursor p c n)
    (lp rp : Phase) (h : C.Holds ⟨z.1,lp,rp,.seek,z.2⟩) :
    ¬ (stage C z lp rp h).ready (stage C z lp rp h).start := by
  intro hf
  exact Bool.noConfusion (show false=true from hf)

theorem stage_restart (C : Context initial group cert v a b) (x : State p c n)
    (hG : C.Good x) (hExit : ¬ Cursor.exit (project x)) :
    C.Certified (project x) := by
  have hh := hG.resolve_left hExit
  exact ⟨x.left,x.right,hh.1,hh.2.base,hh.2.left,hh.2.right,hh.2.leftPhase,hh.2.rightPhase⟩

theorem stage_mean (C : Context initial group cert v a b) (z : Cursor p c n)
    (lp rp : Phase) (h : C.Holds ⟨z.1,lp,rp,.seek,z.2⟩)
    (hz : ¬ Cursor.exit z) (hA : 2*(b+1)<a+1) :
    let S := stage C z lp rp h
    IIDExpectedHittingTimeAtMost S.next S.ready S.start (10*n*((a+1)+(b+1))) := by
  let x : State p c n := ⟨z.1,lp,rp,.seek,z.2⟩
  have H := reserve_mean C hA x (.inr h) (fun hE => (hz hE).elim) trivial
  have hc := valid_service_bound a lp (portValid _ _ _ h.2.leftPhase)
  dsimp only
  have hb : reserve a b x.mode x.left≤10*((a+1)+(b+1)) := by
    change serviceLeft a lp+a+2*(b+1)+2≤_
    omega
  intro t
  have hM := Nat.mul_le_mul_left n hb
  rw [←Nat.mul_assoc,Nat.mul_comm n 10] at hM
  exact Nat.le_trans (H t) (Nat.mul_le_mul_right _ hM)

def attempt_of_failure_mass (C : Context initial group cert v a b) (z : Cursor p c n)
    (lp rp : Phase) (h : C.Holds ⟨z.1,lp,rp,.seek,z.2⟩) (hz : ¬ Cursor.exit z)
    (hA : 2*(b+1)<a+1)
    (hFail : ∀ t, 256 * terminalMass (next group cert v a b) ready
      (fun y => ¬ Cursor.exit (project y)) t (⟨z.1,lp,rp,.seek,z.2⟩ : State p c n)≤255*n^t) :
    UniformAttempt (cursorNext group cert) Cursor.exit C.Certified
      (10*n*((a+1)+(b+1))) 256 z where
  stage := stage C z lp rp h
  properStart := proper_start C z lp rp h
  restart y hy _ hs := stage_restart C y hy hs
  mean := stage_mean C z lp rp h hz hA
  failBound := hFail

theorem success_sound_step (x : State p c n) (e : Fin n)
    (h : x.mode=.success → x.exited=true) :
    (next group cert v a b x e).mode=.success →
      (next group cert v a b x e).exited=true := by
  intro hm
  by_cases hD : ready x
  · rw [done_sticky group cert v a b x e hD] at hm
    simp [next,h hm]
  · by_cases hS : route group cert none x.ledger e=Event.keep
    · rw [mode_keep group cert v a b x e hD hS] at hm
      have hd : x.mode.done=false := Bool.eq_false_iff.mpr hD
      cases hM : x.mode <;> simp [Mode.done,hM] at hd
      · simp only [hM,survivingMode] at hm
        split at hm
        · split at hm
          · unfold onPosition splitTarget at hm
            split at hm <;> (first | contradiction | split at hm <;> contradiction)
          · split at hm <;> contradiction
        · contradiction
      · simp only [hM,survivingMode,onPosition,splitTarget] at hm
        split at hm <;> (first | contradiction | split at hm <;> contradiction)
      · simp only [hM,survivingMode] at hm
        split at hm <;> (first | contradiction | split at hm <;> contradiction)
      · simp only [hM,survivingMode] at hm
        split at hm <;> (first | contradiction | split at hm <;> contradiction)
      · simp only [hM,survivingMode] at hm
        split at hm <;> contradiction
    · simp [next,hS]

end L4.WindowScopedRace
