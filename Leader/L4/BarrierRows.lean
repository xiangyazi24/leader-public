import Leader.L4.Protocol

namespace L4

/-- Both stock coordinates survive canonical birth unchanged, also on P5. -/
theorem finishBirth_stocks {p c1 : Nat} (fire : Bool) (u v : Site p c1) :
    ((finishBirth fire u v).1.stock, (finishBirth fire u v).2.stock) =
      (u.stock, v.stock) := by
  unfold finishBirth
  split <;> rfl

/-- The entire serialized timer suffix, not merely its rail groups, cannot
modify either stock coordinate. -/
theorem pairStep_stocks_eq_prefix {p c1 : Nat} (u v : Site p c1) :
    ((pairStep u v).1.stock, (pairStep u v).2.stock) =
      ((stepPrefix u v).1.stock, (stepPrefix u v).2.stock) := by
  generalize h : stepPrefix u v = w
  cases w with
  | mk a b => simp [pairStep, h, finishBirth_stocks, patrolWrite]

private theorem materializeOrdinary {p c1 : Nat} (u v : Site p c1)
    (hm : u.mark = false) (hr : v.residue = nextResidue u.residue)
    (hl : v.leader = false) : materialize u v = u := by
  simp [materialize, defect, hm, hl, hr]

private def ordinaryNative {p c1 : Nat} (u v : Site p c1) :
    Site p c1 × Site p c1 :=
  let a := fireInitiator u
  if a.bullet == .none then
    ({ a with signal := a.signal.max v.signal }, v)
  else
    ({ a with bullet := .none, signal := a.signal.max .zero },
      { v with bullet := if v.bullet == .none then a.bullet else v.bullet,
               signal := .zero })

private theorem fireInitiator_geometry {p c1 : Nat} (u : Site p c1) :
    (fireInitiator u).leader = u.leader ∧ (fireInitiator u).mark = u.mark ∧
      (fireInitiator u).residue = u.residue ∧ (fireInitiator u).stock = u.stock := by
  unfold fireInitiator
  split <;> exact ⟨rfl, rfl, rfl, rfl⟩

private theorem nativeOrdinaryShape {p c1 : Nat} (u v : Site p c1)
    (hm : u.mark = false) (hl : v.leader = false) :
    native u v = ordinaryNative u v := by
  have ha : (fireInitiator u).mark = u.mark := (fireInitiator_geometry u).2.1
  cases hb : ((fireInitiator u).bullet == Bullet.none) <;>
    simp [native, ordinaryNative, fireResponder, impact, hl, pinned, ha, hm, followerBullet, hb]

private structure PairGeometry {p c1 : Nat} (u v a b : Site p c1) : Prop where
  leftLeader : a.leader = u.leader
  rightLeader : b.leader = v.leader
  leftMark : a.mark = u.mark
  rightMark : b.mark = v.mark
  leftResidue : a.residue = u.residue
  rightResidue : b.residue = v.residue

private theorem ordinaryNativeFacts {p c1 : Nat} (u v : Site p c1) :
    PairGeometry u v (ordinaryNative u v).1 (ordinaryNative u v).2 ∧
      (ordinaryNative u v).1.stock = u.stock ∧
      (ordinaryNative u v).2.stock = v.stock := by
  have ⟨hl, hm, hr, hs⟩ := fireInitiator_geometry u
  cases hb : ((fireInitiator u).bullet == Bullet.none) <;>
    simp only [ordinaryNative, hb, Bool.false_eq_true, if_false, if_true] <;>
    exact ⟨⟨hl, rfl, hm, rfl, hr, rfl⟩, hs, trivial⟩

private theorem paymentOrdinaryShape {p c1 : Nat} (u v : Site p c1)
    (hm : u.mark = false) (hl : v.leader = false) :
    payment u v =
      if payer u && !v.stock then
        ({ u with stock := false }, { v with stock := true })
      else (u, v) := by
  cases hs : u.stock <;> cases hl' : u.leader <;> cases ht : v.stock <;>
    simp [payment, payer, hl, hm, hs, hl', ht]

private theorem ordinaryPrefix {p c1 : Nat} (u v : Site p c1)
    (hm : u.mark = false) (hr : v.residue = nextResidue u.residue)
    (hl : v.leader = false) :
    stepPrefix u v =
      let a := (ordinaryNative u v).1
      let b := (ordinaryNative u v).2
      if payer u && !v.stock then
        ({ a with stock := false }, { b with stock := true })
      else (a,b) := by
  simp only [stepPrefix, materializeOrdinary u v hm hr hl, nativeOrdinaryShape u v hm hl]
  have ⟨hG, hUs, hVs⟩ := ordinaryNativeFacts u v
  rw [paymentOrdinaryShape _ _ (hG.leftMark.trans hm) (hG.rightLeader.trans hl)]
  simp [payer, hG.leftLeader, hUs, hVs]

/-- Literal P2 projection over every ancillary payload. Marks and the
residue hypothesis exclude latent or explicit ghosts at the responder. -/
theorem ordinary_pair_stock {p c1 : Nat} (u v : Site p c1)
    (hm : u.mark = false) (hr : v.residue = nextResidue u.residue)
    (hl : v.leader = false) :
    ((pairStep u v).1.stock, (pairStep u v).2.stock) =
      if payer u && !v.stock then (false, true) else (u.stock, v.stock) := by
  have ⟨_, hUs, hVs⟩ := ordinaryNativeFacts u v
  rw [pairStep_stocks_eq_prefix, ordinaryPrefix u v hm hr hl]
  split
  · rfl
  · rw [hUs, hVs]

/-- A living initiator fills an empty ordinary responder on that same mark. -/
theorem leader_inject_stock {p c1 : Nat} (u v : Site p c1)
    (hm : u.mark = false) (hr : v.residue = nextResidue u.residue)
    (hl : v.leader = false) (hu : u.leader = true) (hs : v.stock = false) :
    ((pairStep u v).1.stock, (pairStep u v).2.stock) = (false, true) := by
  rw [ordinary_pair_stock u v hm hr hl]
  simp [payer, hu, hs]

/-- S1 shuts off the unpinned controller and no arrival can set its birth latch. -/
theorem patrol_unpinned_source_fire {Q : Nat} (root leader : Bool)
    (s : Source Q) (l r : Rail) :
    (patrol root false leader s l r).source = .off ∧
      (patrol root false leader s l r).fire = false := by
  unfold patrol
  simp only [sourceGuard, Bool.not_false, if_true]
  generalize h : (if s == Source.off then r else Rail.x) = r'
  cases root <;> cases leader <;> cases l <;> cases r' <;>
    exact ⟨rfl, rfl⟩

private theorem ordinaryPrefixFacts {p c1 : Nat} (u v : Site p c1)
    (hm : u.mark = false) (hr : v.residue = nextResidue u.residue)
    (hl : v.leader = false) :
    PairGeometry u v (stepPrefix u v).1 (stepPrefix u v).2 := by
  have ⟨hG, _, _⟩ := ordinaryNativeFacts u v
  rw [ordinaryPrefix u v hm hr hl]
  dsimp only
  split <;> exact
    ⟨hG.leftLeader, hG.rightLeader, hG.leftMark, hG.rightMark,
      hG.leftResidue, hG.rightResidue⟩

/-- The premise excludes all root/residue writes on an ordinary bond.
In particular no call to the timer can give this ordinary responder a
controller or birth. -/
theorem ordinary_pair_geometry {p c1 : Nat} (u v : Site p c1)
    (hm : u.mark = false) (hr : v.residue = nextResidue u.residue)
    (hl : v.leader = false) :
    let a := (pairStep u v).1
    let b := (pairStep u v).2
    (a.leader = u.leader ∧ a.mark = u.mark ∧ a.residue = u.residue) ∧
    (b.leader = v.leader ∧ b.mark = v.mark ∧ b.residue = v.residue ∧ b.source = .off) := by
  have hG := ordinaryPrefixFacts u v hm hr hl
  unfold pairStep
  generalize hx : stepPrefix u v = w at hG ⊢
  cases w with
  | mk a b =>
    have hbm : b.leader = false := hG.rightLeader.trans hl
    have ham : a.mark = false := hG.leftMark.trans hm
    have hS := (patrol_unpinned_source_fire false false b.source a.rail b.rail).1
    simp [hbm, ham, pinned, patrolWrite, finishBirth, hS]
    exact ⟨⟨hG.leftLeader, hm, hG.leftResidue⟩,
      ⟨hl, hG.rightMark, hG.rightResidue⟩⟩

end L4

#print axioms L4.finishBirth_stocks
#print axioms L4.pairStep_stocks_eq_prefix
#print axioms L4.ordinary_pair_stock
#print axioms L4.leader_inject_stock

#print axioms L4.patrol_unpinned_source_fire
#print axioms L4.ordinary_pair_geometry
