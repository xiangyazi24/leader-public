import Leader.L4.TaggedRows

namespace L4

/-- A replacement live responder (N1 two), or an N0 live initiator
whose newly fired bullet moves into a previously empty ordinary site. -/
def freshResponder {p c1 : Nat} (u v : Site p c1) : Bool :=
  (v.leader && (v.signal == .two)) ||
    (tagOverwrite u && !v.leader && !u.mark && !defect u v &&
      (v.bullet == .none))

def freshStep {p c1 : Nat} (u v : Site p c1) (a b : Bool) : Bool × Bool :=
  (false, freshResponder u v || (tagStep u v a b).2)

theorem freshResponder_iff {p c1 : Nat} (u v : Site p c1) :
    freshResponder u v = true ↔
      (v.leader = true ∧ v.signal = .two) ∨
      (tagOverwrite u = true ∧ v.leader = false ∧ u.mark = false ∧
        defect u v = false ∧ v.bullet = .none) := by
  have hS (s : Signal) : (s == .two) = true ↔ s = .two := by
    cases s <;> decide
  have hB (b : Bullet) : (b == .none) = true ↔ b = .none := by
    cases b <;> decide
  simp [freshResponder, hS, hB, and_assoc]

/-- Any N0 launch, independent of the old initiator bullet, travels in the
ordinary empty row. That row leaves the boundary unmarked, so P5 cannot
overwrite this new responder bullet. -/
private theorem freshN0_prefix {p c1 : Nat} (u v : Site p c1)
    (hi : tagOverwrite u = true) (hl : v.leader = false)
    (hm : u.mark = false) (hd : defect u v = false) (hv : v.bullet = .none) :
    (stepPrefix u v).2.bullet = .live ∧
      (stepPrefix u v).2.leader = false ∧ (stepPrefix u v).1.mark = false ∧
      (stepPrefix u v).1.signal = .zero ∧ (stepPrefix u v).2.signal = .zero := by
  have hMat : materialize u v = u := by simp [materialize, hl, hm, hd]
  have hInit : fireInitiator u = {u with bullet := .live, shield := true, signal := .zero} := by
    simp [fireInitiator, show (u.leader && !(u.signal == .zero)) = true from hi]
  have huB : (Bullet.live == Bullet.none) = false := rfl
  have hvB : (Bullet.none == Bullet.none) = true := rfl
  simp only [stepPrefix, hMat, native, hInit, fireResponder, hl, Bool.false_eq_true,
    if_false, impact, Bool.and_false, pinned, Bool.not_false, Bool.true_and, hm,
    followerBullet, huB, hv, hvB, if_true, payment]
  cases hU : u.leader <;> cases hS : u.stock <;> cases hV : v.stock <;>
    simp [payer, Signal.max] <;> (try (intro he; simp [he]))

/-- N1 two creates a live shield before N2, so the responding leader
cannot die in the native impact. -/
theorem freshN1_prefix {p c1 : Nat} (u v : Site p c1)
    (hl : v.leader = true) (hs : v.signal = .two) :
    (stepPrefix u v).2.bullet = .live ∧ (stepPrefix u v).2.leader = true ∧
      (stepPrefix u v).2.shield = true ∧ (stepPrefix u v).2.signal = .zero := by
  have hf : fireResponder v = {v with bullet := .live, shield := true, signal := .zero} := by
    simp [fireResponder, hl, hs]
  unfold stepPrefix native
  rw [hf]
  generalize h : fireInitiator (materialize u v) = a
  have hnn : (Bullet.none == Bullet.none) = true := rfl
  have hdn : (Bullet.dummy == Bullet.none) = false := rfl
  have hln : (Bullet.live == Bullet.none) = false := rfl
  cases ha : a.bullet <;>
    simp [impact, followerBullet, payment, hl, ha, hnn, hdn, hln]

theorem freshN0_signals {p c1 : Nat} (u v : Site p c1)
    (hi : tagOverwrite u = true) (hl : v.leader = false)
    (hm : u.mark = false) (hd : defect u v = false) (hv : v.bullet = .none) :
    (pairStep u v).1.signal = .zero ∧ (pairStep u v).2.signal = .zero := by
  obtain ⟨_,hl',hm',hs,ht⟩ := freshN0_prefix u v hi hl hm hd hv
  unfold pairStep
  generalize hh : stepPrefix u v = q at hl' hm' hs ht ⊢
  cases q with
  | mk l r =>
    dsimp at hl' hm' hs ht
    simp [patrolWrite, finishBirth, pinned, hl', hm', hs] <;> (try exact ht)

theorem freshN1_physical {p c1 : Nat} (u v : Site p c1)
    (hl : v.leader = true) (hs : v.signal = .two) :
    (pairStep u v).2.leader = true ∧ (pairStep u v).2.shield = true ∧
      (pairStep u v).2.signal = .zero := by
  obtain ⟨_,hl',hh',hs'⟩ := freshN1_prefix u v hl hs
  unfold pairStep
  generalize hh : stepPrefix u v = q at hl' hh' hs' ⊢
  cases q with
  | mk l r =>
    dsimp at hl' hh' hs'
    simp [patrolWrite, finishBirth, pinned, hl', hh', hs']

/-- For an unobstructed transfer of a zero-signal old donor, both signal
coordinates are zero afterwards. Without the donor hypothesis, only the
responding carrier is forced to zero. -/
theorem freshTransfer_signals {p c1 : Nat} (u v : Site p c1)
    (h : tagTransfer u v = true) :
    (pairStep u v).2.signal = .zero ∧
      (u.signal = .zero → (pairStep u v).1.signal = .zero) := by
  obtain ⟨hb,ho,hl,hm,hd,hv⟩ := (tagTransfer_iff u v).mp h
  have hMat : materialize u v = u := by simp [materialize, hl, hm, hd]
  have hInit : fireInitiator u = u := by
    unfold fireInitiator
    rw [show (u.leader && !(u.signal == .zero)) = false from ho]
    rfl
  have huB : (Bullet.live == Bullet.none) = false := rfl
  have hvB : (Bullet.none == Bullet.none) = true := rfl
  have hPrefix : (stepPrefix u v).2.leader = false ∧ (stepPrefix u v).1.mark = false ∧
      (stepPrefix u v).2.signal = .zero ∧
      (u.signal = .zero → (stepPrefix u v).1.signal = .zero) := by
    simp only [stepPrefix, hMat, native, hInit, fireResponder, hl, Bool.false_eq_true,
      if_false, impact, Bool.and_false, pinned, Bool.not_false, Bool.true_and, hm,
      followerBullet, hb, huB, hv, hvB, if_true, payment]
    cases hU : u.leader <;> cases hS : u.stock <;> cases hV : v.stock <;>
      simp [payer, Signal.max] <;> (try (intro he; simp [he]))
  obtain ⟨hl',hm',hs,ht⟩ := hPrefix
  unfold pairStep
  generalize hh : stepPrefix u v = q at hl' hm' hs ht ⊢
  cases q with
  | mk l r =>
    dsimp at hl' hm' hs ht
    simp [patrolWrite, finishBirth, pinned, hl', hm', hs] <;> (try exact ht)

/-- The literal physical output is live in each creation case. -/
theorem freshResponder_live {p c1 : Nat} (u v : Site p c1)
    (h : freshResponder u v = true) : (pairStep u v).2.bullet = .live := by
  have hcase : (stepPrefix u v).2.bullet = .live ∧ pinned (stepPrefix u v).1 (stepPrefix u v).2 = false := by
    rcases (freshResponder_iff u v).mp h with ⟨hl,hs⟩ | ⟨hi,hl,hm,hd,hv⟩
    · obtain ⟨hb,hl',_,_⟩ := freshN1_prefix u v hl hs
      exact ⟨hb, by simp [pinned,hl']⟩
    · obtain ⟨hb,hl',hm',_,_⟩ := freshN0_prefix u v hi hl hm hd hv
      exact ⟨hb, by simp [pinned,hl',hm']⟩
  unfold pairStep
  generalize hw : stepPrefix u v = q at hcase ⊢
  cases q with
  | mk l r =>
    obtain ⟨hb,hp⟩ := hcase
    dsimp at hb hp
    simp [patrolWrite, finishBirth, pinned, hb, show (!r.leader && l.mark) = false from hp]

theorem freshStep_responder_live {p c1 : Nat} (u v : Site p c1) (a b : Bool)
    (h : (freshStep u v a b).2 = true) : (pairStep u v).2.bullet = .live := by
  simp only [freshStep, Bool.or_eq_true] at h
  rcases h with h | h
  · exact freshResponder_live u v h
  · exact tagStep_responder_live u v a b h

theorem freshStep_resident {p c1 : Nat} (u v : Site p c1)
    (hb : v.bullet = .live) (ho : tagOverwrite v = false) (hf : tagBirth u v = false) :
    (freshStep u v false true).2 = true := by
  have hr := (tagResident_no_birth_iff u v).mpr ⟨hb,ho,hf⟩
  simp [freshStep, tagStep, hr]

/-- An old live, zero-signal resident retains zero and its shield while
its identity survives the incoming service. Collision may reset the signal
to zero again but cannot replace that resident. -/
theorem freshResident_zero {p c1 : Nat} (u v : Site p c1)
    (hr : tagResident u v = true) (hz : v.signal = .zero) :
    (pairStep u v).2.signal = .zero ∧ (pairStep u v).2.shield = v.shield := by
  have hf : fireResponder v = v := by
    cases hl : v.leader <;> simp [fireResponder, hl, hz]
  have hi (a b : Site p c1) :
      (impact a b).2.signal = b.signal ∧ (impact a b).2.shield = b.shield := by
    unfold impact
    split
    · split <;> exact ⟨rfl,rfl⟩
    · exact ⟨rfl,rfl⟩
  have hg (g : Bool) (a b : Site p c1) (hb : b.signal = .zero) :
      (followerBullet g a b).2.signal = .zero ∧
        (followerBullet g a b).2.shield = b.shield := by
    unfold followerBullet
    split
    · split
      · exact ⟨hb,rfl⟩
      · exact ⟨rfl,rfl⟩
    · exact ⟨hb,rfl⟩
  have hp (a b : Site p c1) :
      (payment a b).2.signal = b.signal ∧ (payment a b).2.shield = b.shield := by
    unfold payment
    split
    · exact ⟨rfl,rfl⟩
    · split
      · exact ⟨rfl,rfl⟩
      · split <;> exact ⟨rfl,rfl⟩
  have hn : (native (materialize u v) v).2.signal = .zero ∧
      (native (materialize u v) v).2.shield = v.shield := by
    unfold native
    rw [hf]
    let a := fireInitiator (materialize u v)
    let z := impact a v
    have hi' := hi a v
    have hg' := hg (pinned z.1 z.2) z.1 z.2 (hi'.1.trans hz)
    exact ⟨hg'.1,hg'.2.trans hi'.2⟩
  let z := native (materialize u v) v
  have hpay := hp z.1 z.2
  have hprefix : (stepPrefix u v).2.signal = .zero ∧
      (stepPrefix u v).2.shield = v.shield :=
    ⟨hpay.1.trans hn.1,hpay.2.trans hn.2⟩
  have hbirth := ((tagResident_no_birth_iff u v).mp hr).2.2
  unfold pairStep tagBirth at *
  generalize hx : stepPrefix u v = q at hprefix hbirth ⊢
  cases q with
  | mk l r =>
    obtain ⟨hs,hh⟩ := hprefix
    dsimp at hs hh hbirth
    simp only [patrolWrite, finishBirth, pinned] at *
    simp only [hbirth, Bool.false_eq_true, if_false, hs, hh, and_self]

/-- The new creation observer never claims an output already attributed
to a surviving old physical bullet by either old-lineage case. -/
theorem freshResponder_disjoint {p c1 : Nat} (u v : Site p c1)
    (h : freshResponder u v = true) :
    tagTransfer u v = false ∧ tagResident u v = false := by
  constructor
  · cases ht : tagTransfer u v
    · rfl
    · obtain ⟨_,ho,hl,_,_,_⟩ := (tagTransfer_iff u v).mp ht
      rcases (freshResponder_iff u v).mp h with ⟨hL,_⟩ | ⟨hO,_,_,_,_⟩
      · simp [hl] at hL
      · simp [ho] at hO
  · cases hr : tagResident u v
    · rfl
    · obtain ⟨hb,ho,_⟩ := (tagResident_iff u v).mp hr
      rcases (freshResponder_iff u v).mp h with ⟨hL,hS⟩ | ⟨_,_,_,_,hB⟩
      · have hneq : (Signal.two == Signal.zero) = false := rfl
        simp [tagOverwrite,hL,hS,hneq] at ho
      · simp [hb] at hB

end L4
