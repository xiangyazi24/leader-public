import Leader.L4.Height.ObserverDirty

/-! The old-pair row projected to the observer path and door. -/
namespace L4.Height.ObserverDirty
namespace Decoded

open L4.BStarLapTransfer

abbrev Guard := L4.BStarLapTransfer.Site

/-- Forget a front's observation bit, while retaining a reply's sign. -/
def slot (t : Nat) : Slot :=
  if front t then .front else if t = 4 then .negative
  else if t = 5 then .positive else if t = 1 then .trail else .empty

def control (c : Nat) : Control :=
  if c = 1 then .waiting else if c = 2 then .pending else .issue

def terminalSeen (v : Guard) (before ordinary : Bool × Bool) : Bool :=
  v.b == 3 || before.2 || ordinary.2

/-- Every decoded site satisfies the displayed bounds, including raw spares. -/
def Bounded (s : Guard) : Prop := s.a ≤ 5 ∧ s.b ≤ 5 ∧ s.pc ≤ 2

theorem decode_bounded (x : Raw) : Bounded (decode x) := by
  have clamp (m t : Nat) : normal m t ≤ m := by
    unfold normal
    split <;> omega
  exact ⟨clamp _ _, clamp _ _, clamp _ _⟩

def pair (u v : Guard) (ra rb : Bool) (before ordinary : Bool × Bool) : Guard × Guard :=
  let p := plan u v ra rb ra rb before ordinary
  (p.1.1.site u, p.1.2.site v)

private theorem back_cases {t : Nat} (h : back t = true) : t = 4 ∨ t = 5 := by
  simpa [back] using h

private theorem slot_front (hit : Bool) : slot (normal 5 (flag hit % 8)) = .front := by
  cases hit <;> rfl

private theorem slot_return (hit : Bool) :
    slot (normal 5 ((if hit then 5 else 4) % 8)) =
      (if hit then .positive else .negative) := by
  cases hit <;> rfl

private abbrev putA (t : Nat) : Writes := .one (.a t)
private abbrev putB (t : Nat) : Writes := .one (.b t)
private abbrev putC (t : Nat) : Writes := .one (.pc t)

private def watch (s : Guard) (seen : Nat → Bool) : Writes :=
  (touched putA s.a (seen s.a)).thenDo (touched putB s.b (seen s.b))

private def send (out : Nat → Writes) (p q : Nat) (hit : Bool) : Writes :=
  if front p then out (flag hit) else if back q then out 0 else .skip

private def receive (p q : Nat) : Writes :=
  if front p then putA 1 else if back q then putA q
  else if p == 1 && q == 0 then putA 0 else .skip

private def serveDoor (a pc : Nat) (seen : Bool) : Writes :=
  if pc == 0 then (putA (flag seen)).thenDo (putC 1)
  else if pc == 1 && (back a || a == 0) then
    (putA 0).thenDo (putC (if a == 4 then 2 else 0))
  else .skip

private def serveTerminal (b : Nat) (seen : Bool) : Writes :=
  if front b then putB (if seen then 5 else 4)
  else if b == 1 then putB 0 else .skip

private def servePending (pc : Nat) : Writes :=
  if pc == 2 then putC 0 else .skip

private def discard : Writes := (putB 0).thenDo (putC 0)

private def factored (u v : Guard) (ra rb : Bool) (before ordinary : Bool × Bool) :
    Guard × Guard :=
  let seed := rb && rb && (v.pc == 2)
  let seenL := fun t : Nat => t == 3 || before.1 || ordinary.1 || seed
  let seenR := fun t : Nat => t == 3 || before.2 || ordinary.2
  let crossed := before.1 && !ordinary.1 && ordinary.2
  let seenHop := v.a == 3 || before.2 || ordinary.1 || seed || crossed
  let routeL := (watch u seenL).thenDo
    (send (fun t => if ra then putB t else putA t) v.a (if ra then u.b else u.a) seenHop)
  let routeR := (watch v seenR).thenDo (receive v.a (if ra then u.b else u.a))
  let l := routeL.thenDo (if ra then serveDoor u.a u.pc (seenL 2) else discard)
  let r := (routeR.thenDo (if rb then serveTerminal v.b (seenR v.b) else discard)).thenDo
    (if rb then servePending v.pc else .skip)
  (l.site u, r.site v)

private def routedWrites (l r : Writes) (out : Nat → Writes) (p q : Nat)
    (hit : Bool) : Writes × Writes :=
  if front p then (l.thenDo (out (flag hit)), r.thenDo (putA 1))
  else if back q then (l.thenDo (out 0), r.thenDo (putA q))
  else if p == 1 && q == 0 then (l, r.thenDo (putA 0))
  else (l, r)

private theorem route_apply (l r : Writes) (out : Nat → Writes) (p q : Nat)
    (hit : Bool) (u v : Guard) :
    let route := routedWrites l r out p q hit
    route.1.site u = (send out p q hit).site (l.site u) ∧
      route.2.site v = (receive p q).site (r.site v) := by
  by_cases hf : front p = true
  · simp [routedWrites, send, receive, hf, Writes.site]
  by_cases hb : back q = true
  · simp [routedWrites, send, receive, hf, hb, Writes.site]
  by_cases ht : (p == 1 && q == 0) = true <;>
    simp [routedWrites, send, receive, hf, hb, ht, Writes.site]

private def sourceWrites (w : Writes) (ra : Bool) (u : Guard) (seen : Bool) : Writes :=
  let l :=
    if ra then
      if u.pc == 0 then (w.thenDo (putA (flag seen))).thenDo (putC 1)
      else if u.pc == 1 && (back u.a || u.a == 0) then
        (w.thenDo (putA 0)).thenDo (putC (if u.a == 4 then 2 else 0))
      else w
    else w
  if ra && ra then l else l.thenDo discard

private theorem source_apply (w : Writes) (ra : Bool) (u : Guard) (seen : Bool) :
    (sourceWrites w ra u seen).site u =
      (if ra then serveDoor u.a u.pc seen else discard).site (w.site u) := by
  cases ra
  · rfl
  by_cases hi : (u.pc == 0) = true
  · simp [sourceWrites, serveDoor, hi, Writes.site]
  by_cases hw : (u.pc == 1 && (back u.a || u.a == 0)) = true <;>
    simp [sourceWrites, serveDoor, hi, hw, Writes.site]

private def turnWrites (w : Writes) (b : Nat) (seen : Bool) : Writes :=
  if front b then w.thenDo (putB (if seen then 5 else 4))
  else if b == 1 then w.thenDo (putB 0) else w

private def commitWrites (w : Writes) (pc : Nat) : Writes :=
  if pc == 2 then w.thenDo (putC 0) else w

private def receiverWrites (w : Writes) (rb : Bool) (v : Guard) (seen : Bool) : Writes :=
  let r := if rb then commitWrites (turnWrites w v.b seen) v.pc else w
  if rb && rb then r else r.thenDo discard

private theorem turn_apply (w : Writes) (b : Nat) (seen : Bool) (x : Guard) :
    (turnWrites w b seen).site x = (serveTerminal b seen).site (w.site x) := by
  by_cases hf : front b = true
  · simp [turnWrites, serveTerminal, hf, Writes.site]
  by_cases ht : (b == 1) = true <;>
    simp [turnWrites, serveTerminal, hf, ht, Writes.site]

private theorem commit_apply (w : Writes) (pc : Nat) (x : Guard) :
    (commitWrites w pc).site x = (servePending pc).site (w.site x) := by
  by_cases hp : (pc == 2) = true <;> simp [commitWrites, servePending, hp, Writes.site]

private theorem receiver_apply (w : Writes) (rb : Bool) (v : Guard) (seen : Bool) :
    (receiverWrites w rb v seen).site v =
      (if rb then servePending v.pc else .skip).site
        ((if rb then serveTerminal v.b seen else discard).site (w.site v)) := by
  cases rb
  · rfl
  change (commitWrites (turnWrites w v.b seen) v.pc).site v = _
  rw [commit_apply, turn_apply] <;> rfl

/-- Factor the actual plan into independent writes without expanding their guards
in a single term. -/
private theorem pair_factored (u v : Guard) (ra rb : Bool)
    (before ordinary : Bool × Bool) :
    pair u v ra rb before ordinary = factored u v ra rb before ordinary := by
  let seed := rb && rb && (v.pc == 2)
  let seenL := fun t : Nat => t == 3 || before.1 || ordinary.1 || seed
  let seenR := fun t : Nat => t == 3 || before.2 || ordinary.2
  let crossed := before.1 && !ordinary.1 && ordinary.2
  let seenHop := v.a == 3 || before.2 || ordinary.1 || seed || crossed
  let out := fun t => if ra then putB t else putA t
  let q := if ra then u.b else u.a
  let route := routedWrites (watch u seenL) (watch v seenR) out v.a q seenHop
  change ((sourceWrites route.1 ra u (seenL 2)).site u,
      (receiverWrites route.2 rb v (seenR v.b)).site v) = _
  have h := route_apply (watch u seenL) (watch v seenR) out v.a q seenHop u v
  change route.1.site u = _ ∧ route.2.site v = _ at h
  rw [source_apply, receiver_apply, h.1, h.2] <;> rfl

private theorem touchB_a (s : Guard) (t : Nat) (hit : Bool) :
    ((touched putB t hit).site s).a = s.a := by
  unfold touched
  split <;> rfl

private theorem touchA_b (s : Guard) (t : Nat) (hit : Bool) :
    ((touched putA t hit).site s).b = s.b := by
  unfold touched
  split <;> rfl

private theorem touchA_pc (s : Guard) (t : Nat) (hit : Bool) :
    ((touched putA t hit).site s).pc = s.pc := by
  unfold touched
  split <;> rfl

private theorem touchB_pc (s : Guard) (t : Nat) (hit : Bool) :
    ((touched putB t hit).site s).pc = s.pc := by
  unfold touched
  split <;> rfl

private theorem watch_a (s : Guard) (seen : Nat → Bool) :
    slot ((watch s seen).site s).a = slot s.a := by
  simp only [watch, Writes.site, touchB_a]
  by_cases h : front s.a = true
  · change slot ((touched putA s.a (seen s.a)).site s).a = slot s.a
    rw [show slot s.a = .front by simp [slot, h]]
    simpa only [touched, h, if_true, putA, Writes.site, Set.site] using slot_front (seen s.a)
  · simp only [touched, if_neg h, Writes.site]

private theorem watch_b (s : Guard) (seen : Nat → Bool) :
    slot ((watch s seen).site s).b = slot s.b := by
  simp only [watch, Writes.site]
  by_cases h : front s.b = true
  · rw [show slot s.b = .front by simp [slot, h]]
    simpa only [touched, h, if_true, putB, Writes.site, Set.site] using slot_front (seen s.b)
  · simp only [touched, if_neg h, Writes.site]
    by_cases ha : front s.a = true <;> simp [ha, putA, Set.site, Writes.site]

private theorem watch_pc (s : Guard) (seen : Nat → Bool) :
    ((watch s seen).site s).pc = s.pc := by
  simp only [watch, Writes.site, touchB_pc, touchA_pc]

private theorem slot_nonfront {t : Nat} (h : front t ≠ true) : slot t ≠ .front := by
  unfold slot
  rw [if_neg h]
  split <;> (try split) <;> (try split) <;> simp

private theorem slot_nonback {t : Nat} (h : back t ≠ true) :
    slot t ≠ .negative ∧ slot t ≠ .positive := by
  have h4 : t ≠ 4 := fun he => h (by simp [he, back])
  have h5 : t ≠ 5 := fun he => h (by simp [he, back])
  unfold slot
  rw [if_neg h4, if_neg h5]
  split <;> (try split) <;> simp

private theorem slot_trail (t : Nat) : slot t = .trail ↔ t = 1 := by
  by_cases he : t = 1
  · subst t
    decide
  simp only [slot, if_neg he]
  split <;> (try split) <;> (try split) <;> simp [he]

private theorem slot_empty (t : Nat) (h : t ≤ 5) : slot t = .empty ↔ t = 0 := by
  constructor
  · intro he
    unfold slot at he
    split at he
    · contradiction
    split at he
    · contradiction
    split at he
    · contradiction
    split at he
    · contradiction
    have h2 : t ≠ 2 := fun hn => by simp [hn, front] at *
    have h3 : t ≠ 3 := fun hn => by simp [hn, front] at *
    omega
  · rintro rfl
    rfl

private theorem route (p q : Nat) (hq : q ≤ 5) :
    hop (slot p) (slot q) =
      if front p then (.trail, .front)
      else if back q then (slot q, .empty)
      else if p == 1 && q == 0 then (.empty, .empty)
      else (slot p, slot q) := by
  by_cases hf : front p = true
  · rw [if_pos hf]
    simp [slot, hf, hop]
  have hp := slot_nonfront hf
  by_cases hr : back q = true
  · rw [if_neg hf, if_pos hr]
    rcases back_cases hr with e | e
    · rw [e, show slot 4 = .negative from rfl]
      cases h : slot p <;> simp_all [hop]
    · rw [e, show slot 5 = .positive from rfl]
      cases h : slot p <;> simp_all [hop]
  have hqr := slot_nonback hr
  by_cases ht : (p == 1 && q == 0) = true
  · rw [if_neg hf, if_neg hr, if_pos ht]
    have eh : p = 1 ∧ q = 0 := by simpa using ht
    rw [eh.1, eh.2] <;> rfl
  have hte : ¬ (slot p = .trail ∧ slot q = .empty) := by
    rintro ⟨hpt, hqt⟩
    have ep := (slot_trail p).mp hpt
    have eq := (slot_empty q hq).mp hqt
    exact ht (by simp [ep, eq])
  rw [if_neg hf, if_neg hr, if_neg ht]
  cases hsp : slot p <;> cases hsq : slot q <;> simp_all [hop]

private theorem receive_a (s : Guard) (p q : Nat) (hq : q ≤ 5)
    (hs : slot s.a = slot p) :
    slot ((receive p q).site s).a = (hop (slot p) (slot q)).1 := by
  rw [route p q hq]
  by_cases hf : front p = true
  · simp [receive, hf, putA, Writes.site, Set.site, normal]
    rfl
  by_cases hb : back q = true
  · have hn : normal 5 (q % 8) = q := by
      rw [Nat.mod_eq_of_lt (show q < 8 by omega)]
      simp [normal, hq]
    simp [receive, hf, hb, putA, Writes.site, Set.site, hn]
  by_cases he : (p == 1 && q == 0) = true
  · simp [receive, hf, hb, he, putA, Writes.site, Set.site, normal]
    rfl
  · simp [receive, hf, hb, he, Writes.site, hs]

private theorem receive_b (s : Guard) (p q : Nat) :
    ((receive p q).site s).b = s.b := by
  unfold receive
  split <;> (try split) <;> (try split) <;> rfl

private theorem receive_pc (s : Guard) (p q : Nat) :
    ((receive p q).site s).pc = s.pc := by
  unfold receive
  split <;> (try split) <;> (try split) <;> rfl

private theorem send_a (s : Guard) (p q : Nat) (hit : Bool) (hq : q ≤ 5)
    (hs : slot s.a = slot q) :
    slot ((send putA p q hit).site s).a = (hop (slot p) (slot q)).2 := by
  rw [route p q hq]
  by_cases hf : front p = true
  · simp [send, hf, putA, Writes.site, Set.site, slot_front]
  by_cases hb : back q = true
  · simp [send, hf, hb, putA, Writes.site, Set.site, normal]
    rfl
  by_cases he : (p == 1 && q == 0) = true
  · have hz : q = 0 := (show p = 1 ∧ q = 0 by simpa using he).2
    rw [if_neg hf, if_neg hb, if_pos he]
    simp only [send, if_neg hf, if_neg hb, Writes.site, hs]
    rw [hz] <;> rfl
  · simp [send, hf, hb, he, Writes.site, hs]

private theorem send_b (s : Guard) (p q : Nat) (hit : Bool) (hq : q ≤ 5)
    (hs : slot s.b = slot q) :
    slot ((send putB p q hit).site s).b = (hop (slot p) (slot q)).2 := by
  rw [route p q hq]
  by_cases hf : front p = true
  · simp [send, hf, putB, Writes.site, Set.site, slot_front]
  by_cases hb : back q = true
  · simp [send, hf, hb, putB, Writes.site, Set.site, normal]
    rfl
  by_cases he : (p == 1 && q == 0) = true
  · have hz : q = 0 := (show p = 1 ∧ q = 0 by simpa using he).2
    rw [if_neg hf, if_neg hb, if_pos he]
    simp only [send, if_neg hf, if_neg hb, Writes.site, hs]
    rw [hz] <;> rfl
  · simp [send, hf, hb, he, Writes.site, hs]

private theorem sendB_a (s : Guard) (p q : Nat) (hit : Bool) :
    ((send putB p q hit).site s).a = s.a := by
  unfold send
  split <;> (try split) <;> rfl

private theorem sendB_pc (s : Guard) (p q : Nat) (hit : Bool) :
    ((send putB p q hit).site s).pc = s.pc := by
  unfold send
  split <;> (try split) <;> rfl

private theorem door_b (s : Guard) (a pc : Nat) (hit : Bool) :
    ((serveDoor a pc hit).site s).b = s.b := by
  unfold serveDoor
  split <;> (try split) <;> rfl

private theorem door_view (s : Guard) (a pc : Nat) (hit : Bool)
    (ha : slot s.a = slot a) (hc : s.pc = pc) (hpc : pc ≤ 2) (hbnd : a ≤ 5) :
    let z := (serveDoor a pc hit).site s
    (slot z.a, control z.pc) = door (control pc) (slot a) := by
  have hc' : pc = 0 ∨ pc = 1 ∨ pc = 2 := by omega
  rcases hc' with rfl | rfl | rfl
  · change (slot (normal 5 (flag hit % 8)), control 1) = door (control 0) (slot a)
    rw [slot_front] <;> rfl
  · by_cases hback : back a = true
    · rcases back_cases hback with rfl | rfl <;> rfl
    by_cases h0 : a = 0
    · subst a
      rfl
    have hb := slot_nonback hback
    have he : slot a ≠ .empty := fun h => h0 ((slot_empty a hbnd).mp h)
    cases h : slot a <;> simp_all [serveDoor, Writes.site, control, door]
  · simp [serveDoor, Writes.site, ha, hc, control, door]

private theorem terminal_a (s : Guard) (b : Nat) (hit : Bool) :
    ((serveTerminal b hit).site s).a = s.a := by
  unfold serveTerminal
  split <;> (try split) <;> rfl

private theorem terminal_pc (s : Guard) (b : Nat) (hit : Bool) :
    ((serveTerminal b hit).site s).pc = s.pc := by
  unfold serveTerminal
  split <;> (try split) <;> rfl

private theorem terminal_view (s : Guard) (b : Nat) (hit : Bool)
    (hb : slot s.b = slot b) :
    slot ((serveTerminal b hit).site s).b = terminal hit (slot b) := by
  by_cases hf : front b = true
  · have h : slot b = .front := by simp [slot, hf]
    simp only [serveTerminal, if_pos hf, putB, Writes.site, Set.site, h, terminal]
    exact slot_return hit
  by_cases ht : b = 1
  · subst b
    rfl
  have hnf := slot_nonfront hf
  have hnt : slot b ≠ .trail := fun e => ht ((slot_trail _).mp e)
  simp only [serveTerminal, if_neg hf, beq_iff_eq, if_neg ht, Writes.site, hb]
  cases e : slot b <;> simp_all [terminal]

private theorem pending_a (s : Guard) (pc : Nat) :
    ((servePending pc).site s).a = s.a := by
  unfold servePending
  split <;> rfl

private theorem pending_b (s : Guard) (pc : Nat) :
    ((servePending pc).site s).b = s.b := by
  unfold servePending
  split <;> rfl

private theorem pending_view (s : Guard) (pc : Nat) (hc : s.pc = pc) :
    control ((servePending pc).site s).pc = commit (control pc) := by
  by_cases h : pc = 2
  · rw [h] <;> rfl
  by_cases h' : pc = 1 <;>
    simp [servePending, h, h', Writes.site, hc, control, commit]

private theorem discard_a (s : Guard) : (discard.site s).a = s.a := rfl

/-- Interior services project to exactly one ordinary path hop. -/
theorem edgeInterior (u v : Guard) (before ordinary : Bool × Bool)
    (hu : Bounded u) (_hv : Bounded v) :
    let out := pair u v false false before ordinary
    (slot out.2.a, slot out.1.a) = hop (slot v.a) (slot u.a) := by
  simp only [pair_factored, factored, Bool.false_eq_true, if_false, Bool.false_and,
    Bool.or_false, Writes.site, discard_a]
  exact Prod.ext
    (receive_a _ _ _ hu.1 (watch_a _ _))
    (send_a _ _ _ _ hu.1 (watch_a _ _))

/-- The reference's incoming edge turns its old terminal and commits old
pending control on the same mark as the first path hop. -/
theorem edgeIncoming (u v : Guard) (before ordinary : Bool × Bool)
    (hu : Bounded u) (_hv : Bounded v) :
    let out := pair u v false true before ordinary
    (slot out.2.a, slot out.1.a) = hop (slot v.a) (slot u.a) ∧
      slot out.2.b = terminal (terminalSeen v before ordinary) (slot v.b) ∧
      control out.2.pc = commit (control v.pc) := by
  simp only [pair_factored, factored, Bool.false_eq_true, if_false, if_true, Bool.true_and,
    Writes.site, discard_a, pending_a, pending_b, terminal_a, terminalSeen]
  refine ⟨Prod.ext (receive_a _ _ _ hu.1 (watch_a _ _))
    (send_a _ _ _ _ hu.1 (watch_a _ _)), ?_, ?_⟩
  · apply terminal_view
    rw [receive_b, watch_b]
  · apply pending_view
    rw [terminal_pc, receive_pc, watch_pc]

/-- The reference's outgoing edge serves the old door as it transfers the
last path slot to or from the distinct terminal. -/
theorem edgeOutgoing (u v : Guard) (before ordinary : Bool × Bool)
    (hu : Bounded u) (_hv : Bounded v) :
    let out := pair u v true false before ordinary
    (slot out.2.a, slot out.1.b) = hop (slot v.a) (slot u.b) ∧
      (slot out.1.a, control out.1.pc) = door (control u.pc) (slot u.a) := by
  simp only [pair_factored, factored, Bool.false_eq_true, if_false, if_true,
    Bool.false_and, Bool.or_false, Writes.site, discard_a, door_b]
  refine ⟨Prod.ext (receive_a _ _ _ hu.2.1 (watch_a _ _))
    (send_b _ _ _ _ hu.2.1 (watch_b _ _)), ?_⟩
  apply door_view
  · rw [sendB_a, watch_a]
  · rw [sendB_pc, watch_pc]
  · exact hu.2.2
  · exact hu.1

end Decoded

end L4.Height.ObserverDirty
