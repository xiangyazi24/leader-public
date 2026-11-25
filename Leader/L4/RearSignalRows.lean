import Leader.L4.FreshInvariant
namespace L4

private theorem post_signal {p c1 : Nat} (u v : Site p c1) :
    (pairStep u v).1.signal = (stepPrefix u v).1.signal ∧
      ((stepPrefix u v).2.signal ≠ .one → (pairStep u v).2.signal ≠ .one) ∧
      ((stepPrefix u v).2.leader = true →
        (pairStep u v).2.leader = true ∧
          (pairStep u v).2.signal = (stepPrefix u v).2.signal ∧
          (pairStep u v).2.shield = (stepPrefix u v).2.shield) := by
  unfold pairStep
  generalize stepPrefix u v = uv
  rcases uv with ⟨a,b⟩
  dsimp only
  generalize patrol (b.leader || a.mark) (pinned a b) b.leader b.source a.rail b.rail = r
  cases hm : a.mark <;> cases hl : b.leader <;> cases hf : r.fire <;>
    simp [patrolWrite, finishBirth, pinned, hm, hl]

private theorem pay_fields {p c1 : Nat} (a b : Site p c1) :
    (payment a b).1.signal = a.signal ∧
      (payment a b).2.signal = b.signal ∧
      (payment a b).2.shield = b.shield ∧ (payment a b).2.leader = b.leader := by
  unfold payment
  split
  · exact ⟨rfl,rfl,rfl,rfl⟩
  · split
    · exact ⟨rfl,rfl,rfl,rfl⟩
    · split <;> exact ⟨rfl,rfl,rfl,rfl⟩

/-- The responder cannot acquire signal one. -/
theorem rear_responder_no_one {p c1 : Nat} (u v : Site p c1)
    (hv : v.signal ≠ .one) : (pairStep u v).2.signal ≠ .one := by
  apply (post_signal u v).2.1
  have hf : (fireResponder v).signal ≠ .one := by
    unfold fireResponder
    split
    · cases h : v.signal <;> simp_all
    · exact hv
  unfold stepPrefix native
  generalize fireInitiator (materialize u v) = a
  generalize fireResponder v = b at hf ⊢
  have hi : (impact a b).2.signal = b.signal := by
    unfold impact
    split
    · split <;> rfl
    · rfl
  generalize impact a b = uv at hi ⊢
  rcases uv with ⟨a',b'⟩
  simp only [pay_fields]
  change b'.signal = b.signal at hi
  unfold followerBullet
  split
  · split <;> simp_all
  · simpa [hi] using hf

/-- On any pair with a nonleader successor, 0/2 signals remain 0/2. -/
theorem rear_corridor_no_one {p c1 : Nat} (u v : Site p c1)
    (hu : u.signal ≠ .one) (hv : v.signal ≠ .one) (hl : v.leader = false) :
    (pairStep u v).1.signal ≠ .one ∧ (pairStep u v).2.signal ≠ .one := by
  refine ⟨?_, rear_responder_no_one u v hv⟩
  rw [(post_signal u v).1]
  have hu' : (fireInitiator (materialize u v)).signal ≠ .one := by
    unfold fireInitiator
    split
    · exact Signal.noConfusion
    · unfold materialize
      split <;> exact hu
  have hf : fireResponder v = v := by simp [fireResponder,hl]
  unfold stepPrefix native
  rw [hf]
  generalize fireInitiator (materialize u v) = a at hu' ⊢
  have hi : impact a v = (a,v) := by simp [impact,hl]
  rw [hi]
  simp only [pay_fields]
  have max_ne (a b : Signal) (ha : a ≠ .one) (hb : b ≠ .one) :
      Signal.max a b ≠ .one := by cases a <;> cases b <;> simp_all [Signal.max]
  unfold followerBullet
  split
  · split <;> simp [hl] <;> exact max_ne _ _ hu' (by first | exact hv | decide)
  · simp only [hl, Bool.false_eq_true, if_false]
    split <;> exact max_ne _ _ hu' (by first | exact hv | decide)

/-- Incoming N1 and N2 cannot unshield or kill a shielded no-one leader. -/
theorem rear_incoming_shield {p c1 : Nat} (u v : Site p c1)
    (hl : v.leader = true) (hs : v.shield = true) (hn : v.signal ≠ .one) :
    (pairStep u v).2.leader = true ∧ (pairStep u v).2.shield = true ∧
      (pairStep u v).2.signal ≠ .one := by
  have hf : (fireResponder v).leader = true ∧ (fireResponder v).shield = true := by
    unfold fireResponder
    rw [if_pos hl]
    cases h : v.signal <;> simp_all
  have hp : (stepPrefix u v).2.leader = true ∧ (stepPrefix u v).2.shield = true := by
    unfold stepPrefix native
    generalize fireResponder v = b at hf ⊢
    generalize fireInitiator (materialize u v) = a
    have hi : (impact a b).2 = b := by
      unfold impact
      split <;> simp [hf.2]
    generalize impact a b = ab at hi ⊢
    rcases ab with ⟨a',b'⟩
    have hb : b' = b := hi
    subst b'
    simp [pay_fields, followerBullet, hf.1, hf.2]
  have h := (post_signal u v).2.2 hp.1
  exact ⟨h.1,h.2.2.trans hp.2,rear_responder_no_one u v hn⟩

/-- Outgoing N0/N5 preserve shield and no-one across a no-one nonleader. -/
theorem rear_outgoing_shield {p c1 : Nat} (u v : Site p c1)
    (hl : u.leader = true) (hs : u.shield = true)
    (hu : u.signal ≠ .one) (hv : v.signal ≠ .one) (hr : v.leader = false) :
    (pairStep u v).1.leader = true ∧ (pairStep u v).1.shield = true ∧
      (pairStep u v).1.signal ≠ .one := by
  have hmat : (materialize u v).leader = true ∧ (materialize u v).shield = true := by
    unfold materialize
    split <;> exact ⟨hl,hs⟩
  have hf : (fireInitiator (materialize u v)).leader = true ∧
      (fireInitiator (materialize u v)).shield = true := by
    unfold fireInitiator
    split
    · exact ⟨hmat.1,rfl⟩
    · exact hmat
  have hlocal : (stepPrefix u v).1.leader = true ∧ (stepPrefix u v).1.shield = true := by
    have hfr : fireResponder v = v := by simp [fireResponder,hr]
    unfold stepPrefix native
    rw [hfr]
    generalize fireInitiator (materialize u v) = a at hf ⊢
    have hi : impact a v = (a,v) := by simp [impact,hr]
    rw [hi]
    dsimp only
    unfold followerBullet
    split
    · split <;> cases hM : a.mark <;> cases hV : v.stock <;>
        simp [payment, hr, hf.1, hf.2, payer, hV]
    · cases hM : a.mark <;> cases hV : v.stock <;>
        simp [payment, hr, hf.1, hf.2, payer, hV]
  refine ⟨?_,?_,(rear_corridor_no_one u v hu hv hr).1⟩ <;>
    unfold pairStep <;> generalize stepPrefix u v = uv at hlocal ⊢ <;>
    rcases uv with ⟨a,b⟩ <;> dsimp only <;>
    generalize patrol (b.leader || a.mark) (pinned a b) b.leader b.source a.rail b.rail = r <;>
    cases hf : r.fire <;> cases hm : a.mark <;> cases hr : b.leader <;>
    simp_all [patrolWrite, finishBirth, pinned]

/-- Lift the pair-local preservation to any retained subset of the swept
corridor. The sole outgoing boundary exception is supplied by the caller
(e.g. an actual transfer through the former tag endpoint). -/
theorem rear_swept_step {p c1 n : Nat} (x : Config p c1 n) (e : Fin n)
    (Swept : Fin n → Prop)
    (h : ∀ i, Swept i → (x i).signal ≠ .one)
    (hout : Swept e →
      ((x (rightNeighbor e)).signal ≠ .one ∧
        (x (rightNeighbor e)).leader = false) ∨
      (pairStep (x e) (x (rightNeighbor e))).1.signal ≠ .one) :
    ∀ i, Swept i → (step x e i).signal ≠ .one := by
  intro i hi
  by_cases he : i = e
  · subst i
    simp only [step, if_pos rfl]
    rcases hout hi with ⟨hs,hl⟩ | hrow
    · exact (rear_corridor_no_one _ _ (h _ hi) hs hl).1
    · exact hrow
  · by_cases hr : i = rightNeighbor e
    · subst i
      simpa only [step, if_neg he, if_pos rfl, if_true] using
        rear_responder_no_one (x e) (x (rightNeighbor e)) (h _ hi)
    · simpa only [step, if_neg he, if_neg hr] using h i hi

/-- Fixed-rear specialization. All contacts with the incoming edge are
admissible; only its selected outgoing edge needs the nonleader/no-one
successor hypothesis. -/
theorem rear_fixed_step {p c1 n : Nat} (x : Config p c1 n) (e z : Fin n)
    (hl : (x z).leader = true) (hs : (x z).shield = true)
    (h : (x z).signal ≠ .one)
    (hout : z = e → (x (rightNeighbor e)).signal ≠ .one ∧
      (x (rightNeighbor e)).leader = false) :
    (step x e z).leader = true ∧ (step x e z).shield = true ∧
      (step x e z).signal ≠ .one := by
  by_cases he : z = e
  · obtain ⟨hv,hr⟩ := hout he
    subst z
    simpa only [step, if_pos rfl] using rear_outgoing_shield _ _ hl hs h hv hr
  · by_cases hr : z = rightNeighbor e
    · subst z
      simpa only [step, if_neg he, if_pos rfl, if_true] using rear_incoming_shield _ _ hl hs h
    · simpa only [step, if_neg he, if_neg hr] using And.intro hl (And.intro hs h)

/-- A successful original-tag transfer appends a zero-signal site even
if that site previously had inherited signal one. Its prior carrier remains
no-one if already swept. -/
theorem rear_transfer_no_one {p c1 : Nat} (u v : Site p c1)
    (ht : tagTransfer u v = true) :
    (pairStep u v).2.signal = .zero ∧
      (u.signal ≠ .one → (pairStep u v).1.signal ≠ .one) := by
  have hv := (freshTransfer_signals u v ht).1
  refine ⟨hv, ?_⟩
  intro hu
  cases hU : u.signal
  · intro he
    rw [(freshTransfer_signals u v ht).2 hU] at he
    contradiction
  · exact False.elim (hu hU)
  · obtain ⟨hb,ho,hl,hm,hd,he⟩ := (tagTransfer_iff u v).mp ht
    have hMat : materialize u v = u := by simp [materialize,hl,hm,hd]
    have hInit : fireInitiator u = u := by
      unfold fireInitiator
      rw [show (u.leader && !(u.signal == .zero)) = false from ho]
      rfl
    rw [(post_signal u v).1]
    unfold stepPrefix native
    rw [hMat,hInit]
    simp [fireResponder,hl,impact,hm,pinned,followerBullet,hb,he,hU,Signal.max,pay_fields,
      show (Bullet.live == Bullet.none) = false from rfl]

end L4
