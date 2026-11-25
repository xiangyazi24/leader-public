import Leader.L4.FixedResidual
import Leader.L4.TripleBoundary
import Leader.L4.TripleLongRace

/-! Literal observer for the two long-sector races.
The phases are auxiliary tick coordinates, not a replacement kernel.
The physical observer advances on every raw mark, including padding
after the first failed decision. -/
namespace L4.TripleLongMonitor
open TripleBoundary TriplePhase TripleResidual TripleRenewal

inductive Mode where
  | seek | position | raceReady | awaitRight | raceDummy | failed | success
  deriving DecidableEq, Repr

def Mode.done : Mode → Bool
  | .failed | .success => true
  | _ => false

structure State (p c n : Nat) where
  obs : Obs p c n
  left : Phase
  right : Phase
  mode : Mode

/-- Exact count of remaining progress services from a valid nonready
coordinate. The right dummy cycle launched at offset 0 uses 2b+1. -/
def serviceLeft (d : Nat) : Phase → Nat
  | .ready => 0
  | .forward _ q => (d+1-q)+d
  | .returning _ q => q+1

def nominate {n : Nat} (s : Fin n) : Phase → Fin n
  | .ready => s
  | .forward _ q | .returning _ q => liftedSite s q

/-- Hit count to the live impact, excluding its original launch mark. -/
def shotLeft (a : Nat) : Phase → Nat
  | .forward .live q => a+1-q
  | _ => 0

def splitTarget (r : Phase) : Mode :=
  if r.isReady then .awaitRight else .raceReady

def onPosition (a b : Nat) (l r : Phase) : Mode :=
  if shotLeft a l=2*(b+1) then splitTarget r else .position

/-- Bookkeeping on an already committed surviving mark. The classifier
reads readiness, orientations and attacker-terminal at the *old*
endpoint, with updated target readiness used only after that mark. -/
def survivingMode {n : Nat} (v : Fin n) (a b : Nat)
    (mode : Mode) (l _r l' r' : Phase) (e : Fin n) : Mode :=
  let j := liftedSite v (a+1)
  match mode with
  | .seek =>
    if l.isReady then
      if e=v then onPosition a b l' r'
      else if rightNeighbor e=v then .failed else .seek
    else .seek
  | .position => onPosition a b l' r'
  | .raceReady =>
    if e=liftedSite v a ∧ shotLeft a l=1 then .failed else
      if r'.isReady then .awaitRight else .raceReady
  | .awaitRight =>
    if e=j then .failed else if rightNeighbor e=j then .raceDummy else .awaitRight
  | .raceDummy =>
    if r'.isReady then .failed else .raceDummy
  | .failed => .failed
  | .success => .success

def next {p c n : Nat} (v : Fin n) (a b : Nat) (x : State p c n) (e : Fin n) :
    State p c n :=
  let z := advance x.obs e
  let l := x.left.tick v a e
  let r := x.right.tick (liftedSite v (a+1)) b e
  let m := if x.mode.done then x.mode else
    if z.stopped then .success else survivingMode v a b x.mode x.left x.right l r e
  ⟨z,l,r,m⟩

def ready {p c n : Nat} (x : State p c n) : Prop := x.mode.done=true

def Good {p c n : Nat} (v : Fin n) (a b : Nat) (x : State p c n) : Prop :=
  x.obs.stopped=true ∨
    (MCOV x.obs.config ∧ COV x.obs.config ∧ Paired x.obs.config v a b x.left x.right)

theorem project_step {p c n : Nat} (v : Fin n) (a b : Nat)
    (x : State p c n) (e : Fin n) :
    (next v a b x e).obs=advance x.obs e := rfl

theorem done_sticky {p c n : Nat} (v : Fin n) (a b : Nat)
    (x : State p c n) (e : Fin n) (h : ready x) :
    (next v a b x e).mode=x.mode := by
  have h' : x.mode.done=true := h
  simp [next,h']

theorem stop_priority {p c n : Nat} (v : Fin n) (a b : Nat)
    (x : State p c n) (e : Fin n)
    (h : ¬ready x) (hs : (advance x.obs e).stopped=true) :
    (next v a b x e).mode=.success := by simp [next,ready] at h ⊢; rw [h,hs]; rfl

theorem survive_good {p c n : Nat} (hn : 4≤n) (v : Fin n) (a b : Nat)
    (x : State p c n) (e : Fin n) (hx : Good v a b x) :
    Good v a b (next v a b x e) := by
  by_cases h : (advance x.obs e).stopped=true
  · exact Or.inl h
  have hS : x.obs.stopped=false := by
    cases hs : x.obs.stopped
    · rfl
    · exact (h (by simp [advance,hs])).elim
  have hE : event x.obs.config e=false := by simpa [advance,hS] using h
  have h' := hx.resolve_left (by simp [hS])
  have hC := EntranceCover.cover_closed hn x.obs.config e ⟨h'.1,h'.2.1⟩
  have hP := paired_tick_literal hn x.obs.config v e h'.1 h'.2.1 x.left x.right h'.2.2 hE
  exact Or.inr (by simpa only [next,advance,hS,Bool.false_eq_true,if_false] using
    (And.intro hC.1 (And.intro hC.2 hP)))

/-- First decision can be sticky while reachability keeps following the
original physical scheduler. In particular a surviving state after
arbitrary further marks on a failed word is still a fresh restart. -/
def stage {p c n : Nat} (hn : 4≤n) (v : Fin n) (a b : Nat) (z : Obs p c n)
    (l r : Phase) (h : MCOV z.config ∧ COV z.config ∧ Paired z.config v a b l r) :
    Stage advance z where
  State := State p c n
  start := ⟨z,l,r,.seek⟩
  next := next v a b
  project := State.obs
  ready := ready
  reachable := Good v a b
  projInit := rfl
  projStep := project_step v a b
  reachStart := Or.inr h
  reachStep x e := survive_good hn v a b x e

theorem proper_start {p c n : Nat} (hn : 4≤n) (v : Fin n) (a b : Nat) (z : Obs p c n)
    (l r : Phase) (h : MCOV z.config ∧ COV z.config ∧ Paired z.config v a b l r) :
    ¬ (stage hn v a b z l r h).ready (stage hn v a b z l r h).start := by
  intro hf
  exact Bool.noConfusion (show false=true from hf)

theorem restart_certified {p c n : Nat} (v : Fin n) (a b : Nat) (x : State p c n)
    (h : Good v a b x) (hs : x.obs.stopped≠true) : Certified v a b x.obs := by
  have h' := h.resolve_left hs
  exact ⟨h'.1,h'.2.1,x.left,x.right,h'.2.2⟩

/-- On a nonterminal surviving mark exact literal priority reduces
to the old-edge classifier, without inspecting any hypothetical mark. -/
theorem mode_survives {p c n : Nat} (v : Fin n) (a b : Nat) (x : State p c n)
    (e : Fin n) (hD : ¬ready x) (hs : (advance x.obs e).stopped=false) :
    (next v a b x e).mode =
      survivingMode v a b x.mode x.left x.right
        (x.left.tick v a e) (x.right.tick (liftedSite v (a+1)) b e) e := by
  have hm : x.mode.done=false := Bool.eq_false_iff.mpr hD
  simp [next,hm,hs]

/-- Geometry-only port bounds, extracted from the physical seal. -/
def PortValid (d : Nat) : Phase → Prop
  | .ready => True
  | .forward _ q => q≤d
  | .returning _ q => q+1≤d

theorem portValid {p c n d : Nat} (x : Config p c n) (s : Fin n) (u : Phase)
    (h : u.Holds x s d) : PortValid d u := by
  cases u with
  | ready => trivial
  | forward k q => exact (show SealedFront x s d q k from h).within
  | returning k q => exact h.1.le

theorem valid_service_bound (d : Nat) (u : Phase) (h : PortValid d u) :
    serviceLeft d u≤2*d+1 := by
  cases u <;> simp [PortValid,serviceLeft] at h ⊢ <;> omega

theorem nominated_inside {n : Nat} (s : Fin n) (d : Nat) (u : Phase)
    (h : PortValid d u) :
    ∃ q, q<d+1 ∧ nominate s u=liftedSite s q := by
  cases u with
  | ready => exact ⟨0,by omega,(liftedSite_zero s).symm⟩
  | forward k q => exact ⟨q,Nat.lt_succ_of_le h,rfl⟩
  | returning k q => exact ⟨q,by have H : q+1≤d := h; omega,rfl⟩

theorem idle_nonready {n : Nat} (s : Fin n) (d : Nat) (u : Phase) (e : Fin n)
    (hu : u.isReady=false) (he : e≠nominate s u) :
    u.tick s d e=u := by
  cases u <;> simp [Phase.tick,Phase.isReady,nominate] at hu he ⊢
  all_goals intro h; exact (he h).elim

theorem ready_iff_service_zero (d : Nat) (u : Phase) (h : PortValid d u) :
    u.isReady=true ↔ serviceLeft d u=0 := by
  cases u <;> simp [Phase.isReady,serviceLeft,PortValid] at h ⊢
  omega

theorem nonready_nominated_spends {n : Nat} (s : Fin n) (d : Nat) (u : Phase)
    (hu : u.isReady=false) (h : PortValid d u) :
    serviceLeft d (u.tick s d (nominate s u))+1=serviceLeft d u := by
  cases u with
  | ready => exact Bool.noConfusion hu
  | forward k q =>
    have hq : q≤d := h
    by_cases hlt : q<d
    · simp [nominate,Phase.tick,hlt,serviceLeft]
      omega
    · have he : q=d := by omega
      subst q
      by_cases hd : d=0
      · subst d; simp [nominate,Phase.tick,serviceLeft]
      · simp [nominate,Phase.tick,hd,serviceLeft]
        omega
  | returning k q =>
    by_cases hq : q=0
    · subst q; simp [nominate,Phase.tick,serviceLeft]
    · simp [nominate,Phase.tick,hq,serviceLeft]
      omega

theorem shot_interior_spends {n : Nat} (v : Fin n) (a q : Nat) (hq : q<a) :
    (Phase.forward .live q).tick v a (liftedSite v q)=.forward .live (q+1) ∧
    shotLeft a (.forward .live (q+1))+1=shotLeft a (.forward .live q) := by
  exact ⟨by simp [Phase.tick,hq],by simp only [shotLeft]; omega⟩

theorem sector_progress_labels_distinct {p c n a b : Nat} (x : Config p c n) (v : Fin n)
    (l r : Phase) (h : Paired x v a b l r) :
    nominate v l≠nominate (liftedSite v (a+1)) r := by
  obtain ⟨i,hi,he⟩ := nominated_inside v a l (portValid _ _ _ h.attacker)
  obtain ⟨j,hj,hE⟩ := nominated_inside (liftedSite v (a+1)) b r (portValid _ _ _ h.target)
  rw [he,hE]
  apply TripleLongRace.disjoint_sector_bonds v _ hi hj
  rcases h.geom.arity with hA|⟨hA,_⟩ <;> omega

/-- The live shot and target modes retain exact finite quota bounds. -/
def Shape (a b : Nat) (m : Mode) (l r : Phase) : Prop :=
  match m with
  | .seek | .failed | .success => True
  | .position => ∃ q, l=.forward .live q ∧ q≤a ∧ 2*(b+1)<a+1-q
  | .raceReady => (∃ q, l=.forward .live q ∧ q≤a ∧ a+1-q≤2*(b+1)) ∧ r.isReady=false
  | .awaitRight => (∃ q, l=.forward .live q ∧ q≤a ∧ a+1-q≤2*(b+1)) ∧ r.isReady=true
  | .raceDummy => (∃ q, l=.forward .live q ∧ q≤a ∧ a+1-q≤2*(b+1)) ∧
      (∃ k, r=.forward .dummy k ∨ r=.returning .dummy k)

theorem shape_onPosition (a b q : Nat) (r : Phase)
    (h : q≤a) (hb : 2*(b+1)≤a+1-q) :
    Shape a b (onPosition a b (.forward .live q) r) (.forward .live q) r := by
  by_cases he : a+1-q=2*(b+1)
  · have hM : onPosition a b (.forward .live q) r=splitTarget r := by
      unfold onPosition
      exact if_pos he
    rw [hM]
    cases hr : r.isReady
    · have hR : splitTarget r=.raceReady := by simp [splitTarget,hr]
      rw [hR]
      exact ⟨⟨q,rfl,h,by omega⟩,hr⟩
    · have hR : splitTarget r=.awaitRight := by simp [splitTarget,hr]
      rw [hR]
      exact ⟨⟨q,rfl,h,by omega⟩,hr⟩
  · have hM : onPosition a b (.forward .live q) r=.position := by
      unfold onPosition
      exact if_neg he
    rw [hM]
    exact ⟨q,rfl,h,by omega⟩

theorem forward_tick_in_range {n : Nat} (v : Fin n) (a q : Nat) (e : Fin n)
    (h : q≤a) (he : e≠liftedSite v a) :
    ∃ q', (Phase.forward .live q).tick v a e=.forward .live q' ∧ q≤q' ∧ q'≤a ∧ q'≤q+1 := by
  by_cases hE : e=liftedSite v q
  · have hq : q<a := by
      by_cases h' : q=a
      · exact (he (h' ▸ hE)).elim
      · omega
    refine ⟨q+1,?_,by omega,by omega,by omega⟩
    simp [Phase.tick,hE,hq]
  · exact ⟨q,by simp [Phase.tick,hE],Nat.le_refl _,h,by omega⟩

theorem predecessor_characterization {n : Nat} (e v : Fin n) (a : Nat) :
    rightNeighbor e=liftedSite v (a+1) ↔ e=liftedSite v a := by
  rw [liftedSite_succ]
  constructor
  · intro h
    simpa only [RearTrace.predecessor_right] using congrArg RearTrace.predecessor h
  · intro h
    rw [h]

theorem in_out_distinct {n : Nat} (hn : 4≤n) (s : Fin n) :
    rightNeighbor s≠s := by
  intro h
  have hh : liftedSite s 1=liftedSite s 0 := by simpa [liftedSite_succ,liftedSite_zero] using h
  have H := liftedSite_inj s (show 1<n by omega) (show 0<n by omega) hh
  omega

theorem physical_event_false {p c n : Nat} (obs : Obs p c n) (e : Fin n)
    (h : (advance obs e).stopped=false) : event obs.config e=false := by
  cases ht : obs.stopped
  · simpa [advance,ht] using h
  · simp [advance,ht] at h

theorem survives_dummy_attack {p c n a b : Nat} (x : State p c n) (v e : Fin n)
    (q : Nat) (hp : Paired x.obs.config v a b x.left x.right)
    (hL : x.left=.forward .live q) (hR : TripleVulnerable.DummyCycle x.right)
    (hS : (advance x.obs e).stopped=false) (hq : q≤a) :
    ∃ q', x.left.tick v a e=.forward .live q' ∧ q≤q' ∧ q'≤a := by
  have hf : ¬(q=a ∧ e=liftedSite v a) := by
    rintro ⟨rfl,rfl⟩
    rw [hL] at hp
    have he := TripleVulnerable.live_terminal_stops _ _ _ hp hR
    rw [physical_event_false _ _ hS] at he
    contradiction
  rw [hL]
  by_cases he : e=liftedSite v q
  · have hq' : q<a := by
      by_cases h : q=a
      · exact (hf ⟨h,h ▸ he⟩).elim
      · omega
    exact ⟨q+1,by simp [Phase.tick,he,hq'],by omega,by omega⟩
  · exact ⟨q,by simp [Phase.tick,he],Nat.le_refl _,hq⟩

theorem isReady_eq (q : Phase) (h : q.isReady=true) : q=.ready := by
  cases q <;> simp [Phase.isReady] at h ⊢

theorem ready_tick_incoming {n : Nat} (s : Fin n) (d : Nat) (e : Fin n)
    (hin : rightNeighbor e=s) (hne : e≠s) :
    Phase.ready.tick s d e=.forward .dummy 0 := by simp [Phase.tick,hin,hne]

theorem mode_shape_step {p c n : Nat} (_hn : 4≤n) (v : Fin n) (a b : Nat)
    (hA : 2*(b+1)<a+1) (x : State p c n) (e : Fin n) (hG : Good v a b x)
    (hX : Shape a b x.mode x.left x.right) :
    Shape a b (next v a b x e).mode (next v a b x e).left (next v a b x e).right := by
  by_cases hD : ready x
  · rw [done_sticky v a b x e hD]
    have hh : x.mode.done=true := hD
    cases hM : x.mode <;> simp [Shape,hM,Mode.done] at hh ⊢
  cases hS : (advance x.obs e).stopped
  · have hp : Paired x.obs.config v a b x.left x.right := by
      apply (hG.resolve_left ?_).2.2
      intro hs; have H : (advance x.obs e).stopped=true := by simp [advance,hs]
      rw [hS] at H; contradiction
    rw [mode_survives v a b x e hD hS]
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
      obtain ⟨q',hL,hm,hq'⟩ := survives_dummy_attack x v e q hp hq
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
      obtain ⟨q',hL,hm,hq'⟩ := survives_dummy_attack x v e q hp hq hr hS hB
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
  · rw [stop_priority v a b x e hD hS]
    trivial

def reserve (a b : Nat) (m : Mode) (l : Phase) : Nat :=
  match m with
  | .seek => serviceLeft a l+a+2*(b+1)+2
  | .position | .raceReady => shotLeft a l+2*(b+1)+1
  | .awaitRight => shotLeft a l+1
  | .raceDummy => shotLeft a l
  | .failed | .success => 0

def workEdge {p c n : Nat} (v : Fin n) (a : Nat) (x : State p c n) : Fin n :=
  if x.mode=.awaitRight then liftedSite v (a+1) else nominate v x.left

theorem onPosition_reserve_le (a b : Nat) (l r : Phase) :
    reserve a b (onPosition a b l r) l≤shotLeft a l+2*(b+1)+1 := by
  unfold onPosition
  split
  · unfold splitTarget
    split <;> simp [reserve] <;> omega
  · exact Nat.le_refl _

theorem reserve_positive (a b : Nat) (m : Mode) (l r : Phase)
    (h : Shape a b m l r) (hd : m.done=false) :
    1≤reserve a b m l := by
  cases m <;> simp [reserve,Mode.done] at hd ⊢
  · obtain ⟨⟨q,he,hq,_⟩,_⟩ := h
    rw [he]
    simp only [shotLeft]
    omega

theorem shot_nominated_delta {n : Nat} (v : Fin n) (a q : Nat) (e : Fin n)
    (h : q≤a) (ht : ¬(q=a ∧ e=liftedSite v a)) :
    shotLeft a ((Phase.forward .live q).tick v a e)+
      (if e=liftedSite v q then 1 else 0) = shotLeft a (.forward .live q) := by
  by_cases hE : e=liftedSite v q
  · have hq : q<a := by
      by_cases he : q=a
      · exact (ht ⟨he,he ▸ hE⟩).elim
      · omega
    simp [Phase.tick,hE,hq,shotLeft]
    omega
  · simp [Phase.tick,hE]

theorem live_no_impact {p c n a b : Nat} (x : State p c n) (v e : Fin n)
    (q : Nat) (hp : Paired x.obs.config v a b x.left x.right)
    (hL : x.left=.forward .live q) (hR : TripleVulnerable.DummyCycle x.right)
    (hS : (advance x.obs e).stopped=false) : ¬(q=a ∧ e=liftedSite v a) := by
  intro h
  obtain ⟨rfl,rfl⟩ := h
  rw [hL] at hp
  have he := TripleVulnerable.live_terminal_stops _ _ _ hp hR
  rw [physical_event_false _ _ hS] at he
  contradiction

theorem reserve_step {p c n : Nat} (v : Fin n) (a b : Nat)
    (hA : 2*(b+1)<a+1) (x : State p c n) (e : Fin n)
    (hG : Good v a b x) (hX : Shape a b x.mode x.left x.right) (hD : ¬ready x) :
    reserve a b (next v a b x e).mode (next v a b x e).left +
      (if e=workEdge v a x then 1 else 0) ≤ reserve a b x.mode x.left := by
  have hd : x.mode.done=false := Bool.eq_false_iff.mpr hD
  by_cases hS : (advance x.obs e).stopped=true
  · rw [stop_priority v a b x e hD hS]
    have h := reserve_positive a b x.mode x.left x.right hX hd
    change 0+(if e=workEdge v a x then 1 else 0)≤reserve a b x.mode x.left
    split <;> omega
  have hSF := Bool.eq_false_iff.mpr hS
  have hp : Paired x.obs.config v a b x.left x.right := by
    apply (hG.resolve_left ?_).2.2
    intro h
    exact hS (by simp [advance,h])
  rw [mode_survives v a b x e hD hSF]
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
    have hT := live_no_impact x v e q hp hq hCycle hSF
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
    have hT := live_no_impact x v e q hp hq hCycle hSF
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

/-- Shapes and covers stay valid all the way through a padded word.
This version uses the same transition as the physical Stage. -/
theorem shape_run {p c n : Nat} (hn : 4≤n) (v : Fin n) (a b : Nat) (hA : 2*(b+1)<a+1)
    (x : State p c n) (w : List (Fin n))
    (hG : Good v a b x) (hX : Shape a b x.mode x.left x.right) :
    let y := GGTiming.runMarks (next v a b) x w
    Good v a b y ∧ Shape a b y.mode y.left y.right := by
  induction w generalizing x with
  | nil => exact ⟨hG,hX⟩
  | cons e w ih =>
    exact ih (next v a b x e)
      (survive_good hn v a b x e hG) (mode_shape_step hn v a b hA x e hG hX)

theorem reserve_mean {p c n : Nat} (hn : 4≤n) (v : Fin n) (a b : Nat) (hA : 2*(b+1)<a+1)
    (x : State p c n) (hG : Good v a b x) (hX : Shape a b x.mode x.left x.right) :
    IIDExpectedHittingTimeAtMost (next v a b) ready x (n*reserve a b x.mode x.left) := by
  let fold := GGTiming.runMarks (next v a b) x
  let Q : FixedResidual.Countdown (next v a b) ready x :=
    ⟨fun w => reserve a b (fold w).mode (fold w).left, fun w => workEdge v a (fold w),?_⟩
  · exact FixedResidual.expected_of_countdown _ _ _ Q
  · intro w hd e
    have hk := shape_run hn v a b hA x w hG hX
    have H := reserve_step v a b hA (fold w) e hk.1 hk.2 hd
    simpa only [fold,GGTiming.runMarks_append,GGTiming.runMarks] using H

theorem stage_mean {p c n : Nat} (hn : 4≤n) (v : Fin n) (a b : Nat) (z : Obs p c n)
    (l r : Phase) (h : MCOV z.config ∧ COV z.config ∧ Paired z.config v a b l r)
    (hA : 2*(b+1)<a+1) :
    let S := stage hn v a b z l r h
    IIDExpectedHittingTimeAtMost S.next S.ready S.start (10*n*((a+1)+(b+1))) := by
  let x : State p c n := ⟨z,l,r,.seek⟩
  have H := reserve_mean hn v a b hA x (.inr h) trivial
  have hc := valid_service_bound a l (portValid _ _ _ h.2.2.attacker)
  dsimp only
  have hb : reserve a b x.mode x.left≤10*((a+1)+(b+1)) := by
    change serviceLeft a l+a+2*(b+1)+2≤_
    omega
  intro t
  have hM := Nat.mul_le_mul_left n hb
  rw [←Nat.mul_assoc,Nat.mul_comm n 10] at hM
  exact Nat.le_trans (H t) (Nat.mul_le_mul_right _ hM)

/-- Once the physical monitor's terminal numerator is proved, no other
interface remains for this long case. Certification restarts on the
actual padded projection, never on a frozen failed configuration. -/
def attempt_of_failure_mass {p c n : Nat} (hn : 4≤n) (v : Fin n) (a b : Nat) (z : Obs p c n)
    (l r : Phase) (h : MCOV z.config ∧ COV z.config ∧ Paired z.config v a b l r)
    (hA : 2*(b+1)<a+1)
    (hFail : ∀ t, 256 * terminalMass (next v a b) ready (fun y => y.obs.stopped≠true) t
      (⟨z,l,r,.seek⟩ : State p c n)≤255*n^t) :
    UniformAttempt advance (fun u => u.stopped=true) (Certified v a b)
      (10*n*((a+1)+(b+1))) 256 z where
  stage := stage hn v a b z l r h
  properStart := proper_start hn v a b z l r h
  restart y hy _ hs := restart_certified v a b y hy hs
  mean := stage_mean hn v a b z l r h hA
  failBound := hFail

theorem success_sound_step {p c n : Nat} (v : Fin n) (a b : Nat) (x : State p c n)
    (e : Fin n) (h : x.mode=.success → x.obs.stopped=true) :
    (next v a b x e).mode=.success → (next v a b x e).obs.stopped=true := by
  intro hm
  rw [project_step]
  by_cases hD : ready x
  · rw [done_sticky v a b x e hD] at hm
    simp [advance,h hm]
  · cases hS : (advance x.obs e).stopped
    · rw [mode_survives v a b x e hD hS] at hm
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
    · rfl

theorem failed_of_ready_survives {p c n : Nat} (x : State p c n)
    (hSound : x.mode=.success → x.obs.stopped=true)
    (hD : ready x) (hS : x.obs.stopped≠true) : x.mode=.failed := by
  have h := hS ∘ hSound
  have hd : x.mode.done=true := hD
  cases hm : x.mode <;> simp [Mode.done,hm] at hd h ⊢

theorem race_ticks_independent {p c n a b : Nat} (x : Config p c n)
    (v e : Fin n) (l r : Phase) (h : Paired x v a b l r)
    (hL : l.isReady=false) (hR : r.isReady=false) :
    (e=nominate v l → r.tick (liftedSite v (a+1)) b e=r) ∧
    (e=nominate (liftedSite v (a+1)) r → l.tick v a e=l) := by
  have hn := sector_progress_labels_distinct x v l r h
  exact ⟨fun h => idle_nonready _ _ _ _ hR (h.symm ▸ hn),
    fun h => idle_nonready _ _ _ _ hL (h.symm ▸ hn.symm)⟩

theorem await_incoming_exact {p c n : Nat} (hn : 4≤n) (v : Fin n) (a b : Nat)
    (x : State p c n) (e : Fin n)
    (hm : x.mode=.awaitRight) (hr : x.right=.ready)
    (he : rightNeighbor e=liftedSite v (a+1)) (hS : (advance x.obs e).stopped=false) :
    (next v a b x e).mode=.raceDummy ∧ (next v a b x e).right=.forward .dummy 0 := by
  have hD : ¬ ready x := by simp [ready,hm,Mode.done]
  have hN : e≠liftedSite v (a+1) := by
    intro h; subst e; exact in_out_distinct hn _ he
  constructor
  · rw [mode_survives v a b x e hD hS]
    simp [survivingMode,hm,he,hN]
  · change x.right.tick _ b e=_
    rw [hr]
    exact ready_tick_incoming _ _ _ he hN

end L4.TripleLongMonitor

