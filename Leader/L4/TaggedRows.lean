import Leader.L4.Protocol

namespace L4

/-- N0 or N1 overwrites an old bullet, even when the replacement is also live. -/
def tagOverwrite {p c1 : Nat} (u : Site p c1) : Bool :=
  u.leader && !(u.signal == .zero)

/-- An old live initiator reaches exactly the previously empty ordinary
responder. A collision with a resident bullet does not transfer the tag. -/
def tagTransfer {p c1 : Nat} (u v : Site p c1) : Bool :=
  (u.bullet == .live) && !tagOverwrite u && !v.leader &&
    !u.mark && !defect u v && (v.bullet == .none)

/-- A responder's old live bullet survives exactly when it is not overwritten
by N1 and is still live at the end of the literal row. The latter excludes
P5, which is the only suffix that can remove a resident bullet. -/
def tagResident {p c1 : Nat} (u v : Site p c1) : Bool :=
  (v.bullet == .live) && !tagOverwrite v && ((pairStep u v).2.bullet == .live)

/-- Transport or retention of two existing tags under one selected mark.
An unselected site's tag is unchanged by the ring wrapper; no new tag is made. -/
def tagStep {p c1 : Nat} (u v : Site p c1) (leftTag rightTag : Bool) : Bool × Bool :=
  (false, (leftTag && tagTransfer u v) || (rightTag && tagResident u v))

private theorem live_eq_of_beq (b : Bullet) (h : (b == .live) = true) : b = .live := by
  cases b <;> first | rfl | exact False.elim (Bool.noConfusion h)

private theorem none_eq_of_beq (b : Bullet) (h : (b == .none) = true) : b = .none := by
  cases b <;> first | rfl | exact False.elim (Bool.noConfusion h)

private theorem not_is_true (a : Bool) : (!a) = true ↔ a = false := by
  cases a <;> decide

/-- The transport detector is a case-by-case condition in the old bytes. -/
theorem tagTransfer_iff {p c1 : Nat} (u v : Site p c1) :
    tagTransfer u v = true ↔
      u.bullet = .live ∧ tagOverwrite u = false ∧ v.leader = false ∧
        u.mark = false ∧ defect u v = false ∧ v.bullet = .none := by
  simp only [tagTransfer, Bool.and_eq_true, not_is_true]
  constructor
  · rintro ⟨⟨⟨⟨⟨h,ho⟩,hl⟩,hm⟩,hd⟩,hb⟩
    exact ⟨live_eq_of_beq u.bullet h, ho, hl, hm, hd, none_eq_of_beq v.bullet hb⟩
  · rintro ⟨hu,ho,hl,hm,hd,hv⟩
    exact ⟨⟨⟨⟨⟨by rw [hu]; rfl,ho⟩,hl⟩,hm⟩,hd⟩,by rw [hv]; rfl⟩

private theorem transfer_prefix {p c1 : Nat} (u v : Site p c1)
    (h : tagTransfer u v = true) :
    (stepPrefix u v).2.bullet = .live ∧
      (stepPrefix u v).2.leader = false ∧ (stepPrefix u v).1.mark = false := by
  obtain ⟨hb,ho,hl,hm,hd,hv⟩ := (tagTransfer_iff u v).mp h
  have hMat : materialize u v = u := by simp [materialize, hl, hm, hd]
  have hInit : fireInitiator u = u := by
    unfold fireInitiator
    rw [show (u.leader && !(u.signal == .zero)) = false from ho]
    rfl
  have huB : (Bullet.live == Bullet.none) = false := rfl
  have hvB : (Bullet.none == Bullet.none) = true := rfl
  simp only [stepPrefix, hMat, native, hInit, fireResponder, hl, Bool.false_eq_true,
    if_false, impact, Bool.and_false, pinned, Bool.not_false, Bool.true_and, hm,
    followerBullet, hb, huB, hv, hvB, if_true, payment]
  cases hU : u.leader <;> cases hS : u.stock <;> cases hV : v.stock <;>
    simp [payer]

/-- Every transfer selected by the tag observer lands on a live bullet
in the literal physical successor. No assumption is made on timer scratch. -/
theorem tagTransfer_live {p c1 : Nat} (u v : Site p c1)
    (h : tagTransfer u v = true) : (pairStep u v).2.bullet = .live := by
  have ⟨hB,hL,hM⟩ := transfer_prefix u v h
  unfold pairStep
  generalize hw : stepPrefix u v = w at hB hL hM ⊢
  cases w with
  | mk a b =>
    dsimp at hB hL hM
    simp [pinned, patrolWrite, finishBirth, hB, hL, hM]

theorem tagResident_iff {p c1 : Nat} (u v : Site p c1) :
    tagResident u v = true ↔
      v.bullet = .live ∧ tagOverwrite v = false ∧ (pairStep u v).2.bullet = .live := by
  simp only [tagResident, Bool.and_eq_true, not_is_true]
  constructor
  · rintro ⟨⟨h,ho⟩,h'⟩
    exact ⟨live_eq_of_beq v.bullet h, ho, live_eq_of_beq (pairStep u v).2.bullet h'⟩
  · rintro ⟨h,ho,h'⟩
    exact ⟨⟨by rw [h]; rfl,ho⟩,by rw [h']; rfl⟩

/-- The P5 commit test of the literal row, exposed for tracking extinction
of a resident bullet without introducing a new local state field. -/
def tagBirth {p c1 : Nat} (u v : Site p c1) : Bool :=
  let (a,b) := stepPrefix u v
  let f := patrol (b.leader || a.mark) (pinned a b) b.leader b.source a.rail b.rail
  f.fire && pinned a b

private theorem responder_no_overwrite_prefix {p c1 : Nat} (u v : Site p c1)
    (h : v.bullet = .live) (ho : tagOverwrite v = false) :
    (stepPrefix u v).2.bullet = .live := by
  have hF : fireResponder v = v := by
    cases hh : v.leader
    · simp [fireResponder, hh]
    · have hs : (v.signal == .zero) = true := by
        have hv : (v.leader && !(v.signal == .zero)) = false := ho
        cases hc : (v.signal == .zero) <;> simp_all
      have hZero : v.signal = .zero := by
        cases hc : v.signal with
        | zero => rfl
        | one =>
          have hf : (Signal.one == Signal.zero) = false := rfl
          simp [hc, hf] at hs
        | two =>
          have hf : (Signal.two == Signal.zero) = false := rfl
          simp [hc, hf] at hs
      simp [fireResponder, hh, hZero]
  have hImpact (a b : Site p c1) : (impact a b).2.bullet = b.bullet := by
    unfold impact
    split
    · split <;> rfl
    · rfl
  have hFollow (g : Bool) (a b : Site p c1) (hb : b.bullet = .live) :
      (followerBullet g a b).2.bullet = .live := by
    unfold followerBullet
    split
    · split
      · exact hb
      · have hf : (Bullet.live == Bullet.none) = false := rfl
        simp [hb, hf]
    · exact hb
  have hPay (a b : Site p c1) : (payment a b).2.bullet = b.bullet := by
    unfold payment
    split
    · rfl
    · split
      · rfl
      · split <;> rfl
  have hN : (native (materialize u v) v).2.bullet = .live := by
    unfold native
    rw [hF]
    generalize he : impact (fireInitiator (materialize u v)) v = w
    cases w with
    | mk a b =>
      have hB : b.bullet = .live := by
        have hn := hImpact (fireInitiator (materialize u v)) v
        rw [he] at hn
        exact hn.trans h
      exact hFollow _ _ _ hB
  unfold stepPrefix
  generalize hz : native (materialize u v) v = q at hN ⊢
  cases q with
  | mk a b => exact (hPay a b).trans hN

private theorem responder_bullet_after_patrol {p c1 : Nat} (u v : Site p c1) :
    (pairStep u v).2.bullet =
      if tagBirth u v then Bullet.none else (stepPrefix u v).2.bullet := by
  unfold pairStep tagBirth
  generalize he : stepPrefix u v = w
  cases w with
  | mk a b =>
    simp only [patrolWrite, finishBirth, pinned]
    by_cases h : ((patrol (b.leader || a.mark) (!b.leader && a.mark)
      b.leader b.source a.rail b.rail).fire && (!b.leader && a.mark)) = true
    · simp only [h, if_true]
    · simp only [h, Bool.false_eq_true, if_false]

/-- Once N1 does not overwrite an old live resident bullet, its only possible
extinction on the incoming service is the canonical P5 birth. -/
theorem tagResident_no_birth_iff {p c1 : Nat} (u v : Site p c1) :
    tagResident u v = true ↔
      v.bullet = .live ∧ tagOverwrite v = false ∧ tagBirth u v = false := by
  rw [tagResident_iff, responder_bullet_after_patrol]
  constructor <;> intro h
  · refine ⟨h.1, h.2.1, ?_⟩
    cases hf : tagBirth u v
    · rfl
    · exact False.elim (by simpa [hf] using h.2.2)
  · refine ⟨h.1, h.2.1, ?_⟩
    simpa only [h.2.2, Bool.false_eq_true, if_false] using
      responder_no_overwrite_prefix u v h.1 h.2.1

/-- Transport and retention cannot both claim the responder's output tag. -/
theorem tagTransfer_excludes_resident {p c1 : Nat} (u v : Site p c1)
    (h : tagTransfer u v = true) : tagResident u v = false := by
  have hEmpty := ((tagTransfer_iff u v).mp h).2.2.2.2.2
  have hNe : (Bullet.none == Bullet.live) = false := rfl
  simp [tagResident, hEmpty, hNe]

/-- An outgoing tagged bullet either moves to the responder or is extinguished. -/
theorem tagStep_outgoing {p c1 : Nat} (u v : Site p c1) :
    tagStep u v true false = (false, tagTransfer u v) := by
  simp [tagStep]

/-- For an incoming service, an existing sole responder tag can only stay or end. -/
theorem tagStep_incoming {p c1 : Nat} (u v : Site p c1) :
    tagStep u v false true = (false, tagResident u v) := by
  simp [tagStep]

theorem tagStep_no_new {p c1 : Nat} (u v : Site p c1) :
    tagStep u v false false = (false, false) := by
  simp [tagStep]

/-- Any surviving tag sits on a live physical bullet after the selected mark. -/
theorem tagStep_responder_live {p c1 : Nat} (u v : Site p c1) (a b : Bool)
    (h : (tagStep u v a b).2 = true) : (pairStep u v).2.bullet = .live := by
  simp only [tagStep, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨_,h⟩ | ⟨_,h⟩
  · exact tagTransfer_live u v h
  · exact ((tagResident_iff u v).mp h).2.2

end L4

