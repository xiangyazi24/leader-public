import Leader.L4.WindowA0Guard
import Leader.L4.ResidualSweep

/-! Local moving-top cleanup ingredients, not a full
seven-tag observer or probability theorem. -/
namespace L4.WindowA0Cleanup
open ResidualSweep

private theorem patrol_body {Q : Nat} (a b : Rail) :
    let m := patrol false false false (.off : Source Q) a b
    (m.left,m.right) = body a b := by
  dsimp only
  rw [FixedResidual.body_exact]
  cases a <;> cases b <;> rfl

theorem ordinary_rails {p c : Nat} (u v : Site p c)
    (hL : (stepPrefix u v).2.leader = false)
    (hM : (stepPrefix u v).1.mark = false)
    (hS : (stepPrefix u v).2.source = .off) :
    ((pairStep u v).1.rail,(pairStep u v).2.rail) =
      body (stepPrefix u v).1.rail (stepPrefix u v).2.rail := by
  have h := WindowA0Guard.pair_rail_projection u v
  simp only [hL,hM,hS,pinned,Bool.false_or,Bool.not_false,Bool.true_and] at h
  exact h.trans (patrol_body _ _)

theorem ordinary_break {p c : Nat} (u v : Site p c)
    (hL : (stepPrefix u v).2.leader = false)
    (hM : (stepPrefix u v).1.mark = false)
    (hS : (stepPrefix u v).2.source = .off) :
    (pairStep u v).1.rail ≠ .x ∧
    ((stepPrefix u v).1.rail ≠ .x → (stepPrefix u v).2.rail ≠ .x →
      (pairStep u v).2.rail ≠ .x) := by
  let z := stepPrefix u v
  have h := ordinary_rails u v hL hM hS
  have hl := congrArg Prod.fst h
  have hr := congrArg Prod.snd h
  dsimp only at hl hr
  rw [hl,hr]
  exact ⟨body_break_left z.1.rail z.2.rail,body_break_right z.1.rail z.2.rail⟩

/-- The incoming hit clears U at the responder, including when the
two dirty sockets initially contain different workers. -/
theorem ordinary_reverse {p c : Nat} (u v : Site p c)
    (hL : (stepPrefix u v).2.leader = false)
    (hM : (stepPrefix u v).1.mark = false)
    (hS : (stepPrefix u v).2.source = .off) :
    ¬ Up (pairStep u v).2.rail ∧
    (¬ Up (stepPrefix u v).1.rail → ¬ Up (stepPrefix u v).2.rail →
      ¬ Up (pairStep u v).1.rail) := by
  let z := stepPrefix u v
  have h := ordinary_rails u v hL hM hS
  have hl := congrArg Prod.fst h
  have hr := congrArg Prod.snd h
  dsimp only at hl hr
  rw [hl,hr]
  exact ⟨body_up_progress z.1.rail z.2.rail,body_up_left z.1.rail z.2.rail⟩

/-- The forward clearing nomination consumes the old frontier E/D
and leaves E/D on the next rail, with no assumptions on other fields. -/
theorem ordinary_forward {p c : Nat} (u v : Site p c)
    (hL : (stepPrefix u v).2.leader = false)
    (hM : (stepPrefix u v).1.mark = false)
    (hS : (stepPrefix u v).2.source = .off)
    (hc : Cleared (stepPrefix u v).1.rail)
    (hu : ¬ Up (stepPrefix u v).2.rail)
    (hx : (stepPrefix u v).2.rail ≠ .x) :
    (pairStep u v).1.rail = .e ∧ Cleared (pairStep u v).2.rail := by
  have h := ordinary_rails u v hL hM hS
  have hl := congrArg Prod.fst h
  have hr := congrArg Prod.snd h
  dsimp only at hl hr
  rw [hl,hr]
  exact ⟨body_clear_left _ _ hc hu,body_clear_right _ _ hc hu hx⟩

/-- An unpaid incoming hit at a retained pinned top gives a valid
E/DI/DC seed whenever the top is X-free. -/
theorem pinned_top_seed {p c : Nat} (u v : Site p c)
    (hL : (stepPrefix u v).2.leader = false)
    (hM : (stepPrefix u v).1.mark = true)
    (hx : (stepPrefix u v).2.rail ≠ .x) :
    Cleared (pairStep u v).2.rail := by
  have h := WindowA0Guard.pair_rail_projection u v
  have hr := congrArg Prod.snd h
  dsimp only at hr
  simp only [hL,hM,pinned,Bool.false_or,Bool.not_false,Bool.true_and] at hr
  rw [hr,FixedResidual.top_exact true false _ _ _ (.inl rfl)]
  exact top_cleared _ hx

/-- A retained pinned pair is the simultaneous door/turn row; neither
projection invents a scheduler mark. The no-break and launch tests
therefore apply to the same completed pair. -/
theorem pinned_rails {p c : Nat} (u v : Site p c)
    (hL : (stepPrefix u v).2.leader = false)
    (hM : (stepPrefix u v).1.mark = true) :
    let z := stepPrefix u v
    (pairStep u v).1.rail = (FixedResidual.serviceDoor z.2.source z.1.rail).left ∧
      (pairStep u v).2.rail = FixedResidual.topRail z.2.rail := by
  have h := WindowA0Guard.pair_rail_projection u v
  simp only [hL,hM,pinned,Bool.false_or,Bool.not_false,Bool.true_and] at h
  have hl := congrArg Prod.fst h
  have hr := congrArg Prod.snd h
  dsimp only at hl hr ⊢
  rw [hl,hr]
  exact ⟨(FixedResidual.door_exact _ _ _).2.1,
    FixedResidual.top_exact true false _ _ _ (.inl rfl)⟩

theorem pinned_break {p c : Nat} (u v : Site p c)
    (hL : (stepPrefix u v).2.leader = false)
    (hM : (stepPrefix u v).1.mark = true) :
    (pairStep u v).1.rail ≠ .x := by
  rw [(pinned_rails u v hL hM).1]
  exact door_no_break _ _

theorem pinned_up {p c : Nat} (u v : Site p c)
    (hL : (stepPrefix u v).2.leader = false)
    (hM : (stepPrefix u v).1.mark = true)
    (hn : ¬ launches (stepPrefix u v).2.source (stepPrefix u v).1.rail)
    (hl : ¬ Up (stepPrefix u v).1.rail) :
    ¬ Up (pairStep u v).1.rail ∧ ¬ Up (pairStep u v).2.rail := by
  obtain ⟨h1,h2⟩ := pinned_rails u v hL hM
  rw [h1,h2]
  exact ⟨door_no_up_unless_launch _ _ hn hl,top_no_up _⟩

#print axioms pinned_rails
#print axioms pinned_break
#print axioms pinned_up

#print axioms ordinary_rails
#print axioms ordinary_forward
#print axioms pinned_top_seed

/-- Forward cursor in absolute lifted indices. Seed is the obligation
to process the current top before using a retained frontier. -/
structure Cursor where
  top : Nat
  front : Nat
  seed : Bool

def credit (J : Nat) (x : Cursor) : Nat :=
  (J-x.top)+(J-x.front)+x.seed.toNat

/-- A new seed obligation requires passing the old frontier, hence
spends an increase of both top and frontier. A stationary nominated
mark advances the frontier or discharges a pending seed. Nonnominated
marks use the same contract with hit=false. -/
theorem credit_step (J : Nat) (x y : Cursor) (hit : Bool)
    (hI : x.top ≤ y.top) (hF : x.front ≤ y.front)
    (hyI : y.top ≤ J) (hyF : y.front ≤ J)
    (hReseed : x.seed.toNat < y.seed.toNat →
      x.top < y.top ∧ x.front < y.front)
    (hHit : hit = true → x.top < y.top ∨ x.front < y.front ∨
      y.seed.toNat < x.seed.toNat) :
    credit J y + hit.toNat ≤ credit J x := by
  unfold credit
  by_cases hs : x.seed.toNat < y.seed.toNat
  · obtain ⟨h1,h2⟩ := hReseed hs
    cases hx : x.seed <;> cases hy : y.seed <;> cases hit <;> simp_all <;> omega
  · by_cases he : hit = true
    · have hh := hHit he
      rcases hh with h|h|h <;> simp only [he, Bool.toNat_true] <;> omega
    · have h0 := Bool.eq_false_iff.mpr he
      simp only [h0,Bool.toNat_false]
      omega

/-- 2h+1 front/seed credits, plus one exceptional final door hit. -/
theorem initial_credit (I J : Nat) :
    credit J ⟨I,I,true⟩ + 1 = 2*(J-I)+2 := by
  unfold credit
  simp
  omega

/-- Actual cursor policy on an unrequested boundary advance: keep the
old frontier if still retained, otherwise create one new seed. -/
def onAdvance (x : Cursor) (newTop : Nat) : Cursor :=
  if x.front < newTop then ⟨newTop,newTop,true⟩
  else {x with top := newTop}

theorem advance_credit (J newTop : Nat) (x : Cursor)
    (hi : x.top < newTop) (hf : x.front ≤ J) (hJ : newTop ≤ J) :
    credit J (onAdvance x newTop) + 1 ≤ credit J x := by
  unfold onAdvance
  split
  · rename_i h
    exact credit_step J x ⟨newTop,newTop,true⟩ true (Nat.le_of_lt hi) (Nat.le_of_lt h)
      hJ hJ (fun _ => ⟨hi,h⟩) (fun _ => Or.inl hi)
  · exact credit_step J x {x with top := newTop} true (Nat.le_of_lt hi) (Nat.le_refl _)
      hJ hf (fun h => (Nat.lt_irrefl _ h).elim) (fun _ => Or.inl hi)

#print axioms advance_credit

/-- Hard check from n=16 and flat residues, using the literal P3
and door rows. Skipping the new top leaves the dirty T/T cut. -/
def reseedFixture : Config 2 12 16 := fun i =>
  let x := WindowA0Rows.blank i
  { x with stock := i.val == 15
           rail := if i.val == 1 || i.val == 2 then .t else .e }

theorem reseed_replay : MCOV reseedFixture ∧ COV reseedFixture ∧
    ((run reseedFixture [15]) 0).mark = true ∧
    ((run reseedFixture [15,1,2]) 1).rail = .t ∧
    ((run reseedFixture [15,1,2]) 2).rail = .t ∧
    ((run reseedFixture [15,1,2]) 3).source = .i1 ∧
    ((run reseedFixture [15,0,1]) 2).rail = .e ∧
    ((run reseedFixture [15,0,1,2]) 2).rail = .ui ∧
    ((run reseedFixture [15,0,1,2]) 3).source = .i1 := by
  unfold MCOV COV
  decide

#print axioms ordinary_break
#print axioms ordinary_reverse
#print axioms credit_step
#print axioms initial_credit
#print axioms reseed_replay
end L4.WindowA0Cleanup
