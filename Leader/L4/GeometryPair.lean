import Leader.L4.Protocol

namespace L4

private theorem incoming_materialize {p c1 : Nat} (u v : Site p c1)
    (hm : u.mark = true) : materialize u v = u := by
  cases u
  simp_all [materialize]

private def incomingLeft {p c1 : Nat} (u : Site p c1) : Site p c1 :=
  { u with bullet := .none, signal := u.signal.max .one, stock := false, mark := true }

private theorem incoming_prefix {p c1 : Nat} (u v : Site p c1)
    (hu : u.leader = false) (hv : v.leader = true) (hm : u.mark = true)
    (hkill : u.bullet = .live → v.signal = .zero ∧ v.shield = true) :
    stepPrefix u v = (incomingLeft u, fireResponder v) := by
  have hF : fireInitiator u = u := by simp [fireInitiator, hu]
  have hL : (fireResponder v).leader = true := by
    cases ht : v.signal <;> simp [fireResponder, hv, ht]
  have hI : impact u (fireResponder v) = ({ u with bullet := .none }, fireResponder v) := by
    cases hb : u.bullet with
    | none =>
      unfold impact
      have hh : (Bullet.none == Bullet.none) = true := rfl
      simp [hb, hL, hh]
      cases u
      simp_all
    | dummy =>
      have h₁ : (Bullet.dummy == Bullet.none) = false := rfl
      have h₂ : (Bullet.dummy == Bullet.live) = false := rfl
      simp [impact, hb, hL, h₁, h₂]
    | live =>
      obtain ⟨hz, hsh⟩ := hkill hb
      have hh : (Bullet.live == Bullet.none) = false := rfl
      simp [impact, fireResponder, hv, hz, hb, hsh, hh]
  simp [stepPrefix, incoming_materialize u v hm, native, hF, hI,
    followerBullet, hL, payment, incomingLeft]

private theorem incoming_timer_off {Q : Nat} (s : Source Q) (l r : Rail) :
    (patrol true false true s l r).source = .off := by
  cases s <;> cases l <;> cases r <;> rfl

private theorem incoming_pair_shape {p c1 : Nat} (u v : Site p c1)
    (hu : u.leader = false) (hv : v.leader = true) (hm : u.mark = true)
    (hkill : u.bullet = .live → v.signal = .zero ∧ v.shield = true) :
    pairStep u v =
      let a := incomingLeft u
      let b := fireResponder v
      patrolWrite a b (patrol true false true b.source a.rail b.rail) := by
  unfold pairStep
  rw [incoming_prefix u v hu hv hm hkill]
  have hL : (fireResponder v).leader = true := by
    cases ht : v.signal <;> simp [fireResponder, hv, ht]
  simp [hL, finishBirth, patrolWrite, pinned, incomingLeft]

/-- The incoming edge to a sole covered leader preserves geometry and the
    blue-safety facts used by the cycle proof. -/
theorem incoming_safe {p c1 : Nat} (u v : Site p c1)
    (hu : u.leader = false) (hv : v.leader = true) (hm : u.mark = true)
    (hs : u.source = .off)
    (hkill : u.bullet = .live → v.signal = .zero ∧ v.shield = true)
    (hOldBlue : v.bullet = .live → v.shield = true ∧ v.signal = .zero) :
    let a := (pairStep u v).1
    let b := (pairStep u v).2
    (a.leader = u.leader ∧ a.mark = u.mark ∧
      a.residue = u.residue ∧ a.source = .off) ∧
    (b.leader = v.leader ∧ b.mark = v.mark ∧
      b.residue = v.residue ∧ b.source = .off) ∧
    a.bullet ≠ .live ∧
    (b.bullet = .live → b.shield = true ∧ b.signal = .zero) ∧
    (v.shield = true → v.signal = .zero → b.shield = true ∧ b.signal = .zero) := by
  rw [incoming_pair_shape u v hu hv hm hkill]
  cases hSignal : v.signal <;> cases hBullet : v.bullet <;>
    simp_all [patrolWrite, incomingLeft, fireResponder, incoming_timer_off]

end L4

#print axioms L4.incoming_safe
