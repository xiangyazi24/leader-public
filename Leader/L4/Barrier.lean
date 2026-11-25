import Leader.L4.Statement
import Leader.L4.BarrierRows
import Leader.L4.OpenQueue
import Lean.Elab.Tactic.Omega

namespace L4

/-- The full reachable-state MARK-COVER implication, encoded on incoming edges. -/
def MCOV {p c1 n : Nat} (x : Config p c1 n) : Prop :=
  ∀ e : Fin n, ((x (rightNeighbor e)).leader = true ∨
    (x (rightNeighbor e)).residue ≠ nextResidue (x e).residue) → (x e).mark = true

/-- Full source provenance COV, encoded on incoming edges. -/
def COV {p c1 n : Nat} (x : Config p c1 n) : Prop :=
  ∀ e : Fin n, (x (rightNeighbor e)).source ≠ .off →
    (x (rightNeighbor e)).leader = false ∧ (x e).mark = true

/-- The covered root test on the incoming edge of the responder. The raw
room for a defect is retained so that the pre-cover and post-cover tests can
be distinguished. -/
def EffectiveRootOn {p c1 n : Nat} (x : Config p c1 n) (e : Fin n) : Prop :=
  (x (rightNeighbor e)).leader = true ∨ (x e).mark = true ∨
    (x (rightNeighbor e)).residue ≠ nextResidue (x e).residue

/-- A local pre-mark cut from a stationary long first-barrier tenure. To
instantiate it, select the current barrier leader and certify that its first
three clockwise successors are nonroots. The fact that this is the tagged
bullet's first barrier and that the tenure remains active across a trace are
global obligations, not axioms of the pair map. -/
structure LongBarrier {p c1 n : Nat} (x : Config p c1 n) (z : Fin n) : Prop where
  size : 4 ≤ n
  markCover : MCOV x
  sourceCover : COV x
  barrierLeader : (x z).leader = true
  firstOrdinary : ¬ EffectiveRootOn x z
  secondOrdinary : ¬ EffectiveRootOn x (rightNeighbor z)
  thirdOrdinary : ¬ EffectiveRootOn x (rightNeighbor (rightNeighbor z))

theorem coveredOrdinary {p c1 n : Nat} {x : Config p c1 n} {e : Fin n}
    (hc : COV x) (h : ¬ EffectiveRootOn x e) :
    (x e).mark = false ∧
    (x (rightNeighbor e)).residue = nextResidue (x e).residue ∧
    (x (rightNeighbor e)).leader = false ∧ (x (rightNeighbor e)).source = .off := by
  have hm : (x e).mark = false := by
    cases h' : (x e).mark
    · rfl
    · exact False.elim (h (Or.inr (Or.inl h')))
  have hl : (x (rightNeighbor e)).leader = false := by
    cases h' : (x (rightNeighbor e)).leader
    · rfl
    · exact False.elim (h (Or.inl h'))
  have hr : (x (rightNeighbor e)).residue = nextResidue (x e).residue := by
    by_cases he : (x (rightNeighbor e)).residue = nextResidue (x e).residue
    · exact he
    · exact False.elim (h (Or.inr (Or.inr he)))
  have hs : (x (rightNeighbor e)).source = .off := by
    by_cases he : (x (rightNeighbor e)).source = .off
    · exact he
    · have h' := (hc e he).2
      simp [hm] at h'
  exact ⟨hm, hr, hl, hs⟩

/-- After MCOV, an unmarked incoming bond is exactly a nonroot. -/
theorem covered_noRoot_iff {p c1 n : Nat} {x : Config p c1 n} {e : Fin n}
    (hc : MCOV x) : ¬ EffectiveRootOn x e ↔ (x e).mark = false := by
  unfold EffectiveRootOn
  constructor
  · intro h
    cases hm : (x e).mark
    · rfl
    · exact False.elim (h (Or.inr (Or.inl hm)))
  · intro hm h
    rcases h with hl | hmk | hr
    · simpa [hm] using hc e (Or.inl hl)
    · simp [hm] at hmk
    · simpa [hm] using hc e (Or.inr hr)

private theorem succ_inj {n : Nat} {a b : Fin n}
    (h : rightNeighbor a = rightNeighbor b) : a = b := by
  have hh := congrArg Fin.val h
  change (a.val+1)%n = (b.val+1)%n at hh
  apply Fin.ext
  have ha := a.isLt
  have hb := b.isLt
  by_cases ha' : a.val+1 < n <;> by_cases hb' : b.val+1 < n
  · rw [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at hh
    omega
  · rw [Nat.mod_eq_of_lt ha', show b.val+1 = n by omega, Nat.mod_self] at hh
    omega
  · rw [show a.val+1 = n by omega, Nat.mod_self, Nat.mod_eq_of_lt hb'] at hh
    omega
  · omega

private theorem succ_ne {n : Nat} (hn : 4 ≤ n) (a : Fin n) :
    rightNeighbor a ≠ a := by
  intro he
  have hh := congrArg Fin.val he
  change (a.val+1)%n = a.val at hh
  have ha := a.isLt
  by_cases hlt : a.val+1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hh
    omega
  · rw [show a.val+1 = n by omega, Nat.mod_self] at hh
    omega

private theorem succ2_ne {n : Nat} (hn : 4 ≤ n) (a : Fin n) :
    rightNeighbor (rightNeighbor a) ≠ a := by
  intro he
  have ha := a.isLt
  have hh := congrArg Fin.val he
  change (((a.val + 1) % n) + 1) % n = a.val at hh
  by_cases h1 : a.val+1 < n
  · rw [Nat.mod_eq_of_lt h1] at hh
    by_cases h2 : a.val+1+1 < n
    · rw [Nat.mod_eq_of_lt h2] at hh
      omega
    · rw [show a.val+1+1 = n by omega, Nat.mod_self] at hh
      omega
  · rw [show a.val+1 = n by omega, Nat.mod_self] at hh
    simp only [Nat.zero_add] at hh
    rw [Nat.mod_eq_of_lt (show 1 < n by omega)] at hh
    omega

theorem barrierBondsDistinct {n : Nat} (hn : 4 ≤ n) (z : Fin n) :
    z ≠ rightNeighbor z ∧ z ≠ rightNeighbor (rightNeighbor z) ∧
    rightNeighbor z ≠ rightNeighbor (rightNeighbor z) :=
  ⟨Ne.symm (succ_ne hn z), Ne.symm (succ2_ne hn z), Ne.symm (succ_ne hn _)⟩

open OpenQueue

/-- The two real stock slots next to a stationary barrier. -/
def barrierStock {p c1 n : Nat} (x : Config p c1 n) (z : Fin n) : StockPair :=
  ⟨(x (rightNeighbor z)).stock, (x (rightNeighbor (rightNeighbor z))).stock⟩

/-- Which of the physical queue bonds was selected? -/
def barrierBond {n : Nat} (z e : Fin n) : Bond :=
  if e = z then .inject
  else if e = rightNeighbor z then .transfer
  else if e = rightNeighbor (rightNeighbor z) then .outlet
  else .other

/-- The real outlet accepts exactly when the third slot starts empty. -/
def barrierAccept {p c1 n : Nat} (x : Config p c1 n) (z : Fin n) : Bool :=
  !(x (rightNeighbor (rightNeighbor (rightNeighbor z)))).stock

/-- Actual row semantics for every selected edge of the physical ring. The
real projection is the blocked-outlet map; only the ideal outlet is always
open. No restriction is placed on the three stocks or other local bytes. -/
theorem barrierStock_step {p c1 n : Nat} (x : Config p c1 n)
    (z e : Fin n) (h : LongBarrier x z) :
    barrierStock (step x e) z =
    realStep (barrierStock x z) (barrierBond z e) (barrierAccept x z) := by
  let a := rightNeighbor z
  let b := rightNeighbor a
  let c := rightNeighbor b
  have hza : z ≠ a := Ne.symm (succ_ne h.size z)
  have hzb : z ≠ b := Ne.symm (succ2_ne h.size z)
  have hab : a ≠ b := Ne.symm (succ_ne h.size a)
  have hac : a ≠ c := Ne.symm (succ2_ne h.size a)
  by_cases hez : e = z
  · subst e
    obtain ⟨hm, hr, hl, _⟩ := coveredOrdinary h.sourceCover h.firstOrdinary
    have hrow := ordinary_pair_stock (x z) (x a) hm hr hl
    have hfirst : (pairStep (x z) (x a)).2.stock = true := by
      cases ha : (x a).stock <;>
        simpa [payer, h.barrierLeader, ha] using congrArg Prod.snd hrow
    have hsa : step x z a = (pairStep (x z) (x a)).2 := by
      unfold step
      rw [if_neg (show a ≠ z from Ne.symm hza), if_pos (show a = rightNeighbor z from rfl)]
    have hsb : step x z b = x b := by
      unfold step
      rw [if_neg (show b ≠ z from Ne.symm hzb),
          if_neg (show b ≠ rightNeighbor z from Ne.symm hab)]
    rw [show barrierBond z z = .inject by simp [barrierBond]]
    change StockPair.mk (step x z a).stock (step x z b).stock =
      realStep _ .inject _
    rw [hsa, hsb, hfirst]
    rfl
  by_cases hea : e = a
  · subst e
    obtain ⟨hm, hr, hl, _⟩ := coveredOrdinary h.sourceCover h.secondOrdinary
    have hrow := ordinary_pair_stock (x a) (x b) hm hr hl
    obtain ⟨_, _, hal, _⟩ := coveredOrdinary h.sourceCover h.firstOrdinary
    change (x a).leader = false at hal
    have hsa : step x a a = (pairStep (x a) (x b)).1 := by
      unfold step
      rw [if_pos rfl]
    have hsb : step x a b = (pairStep (x a) (x b)).2 := by
      unfold step
      rw [if_neg (show b ≠ a from Ne.symm hab), if_pos (show b = rightNeighbor a from rfl)]
    have hbond : barrierBond z a = .transfer := by
      unfold barrierBond
      rw [if_neg hez, if_pos (show a = rightNeighbor z from rfl)]
    change StockPair.mk (step x a a).stock (step x a b).stock =
      realStep (barrierStock x z) (barrierBond z a) _
    rw [hsa, hsb, hbond]
    change StockPair.mk (pairStep (x a) (x b)).1.stock (pairStep (x a) (x b)).2.stock =
      realStep ⟨(x a).stock, (x b).stock⟩ .transfer _
    have hp := congrArg (fun q : Bool × Bool => StockPair.mk q.1 q.2) hrow
    cases ha : (x a).stock <;> cases hb : (x b).stock <;>
      simpa [realStep, payer, hal, ha, hb] using hp
  by_cases heb : e = b
  · subst e
    obtain ⟨hm, hr, hl, _⟩ := coveredOrdinary h.sourceCover h.thirdOrdinary
    obtain ⟨_, _, hbl, _⟩ := coveredOrdinary h.sourceCover h.secondOrdinary
    change (x b).leader = false at hbl
    have hrow := ordinary_pair_stock (x b) (x c) hm hr hl
    have hsa : step x b a = x a := by
      unfold step
      rw [if_neg hab, if_neg (show a ≠ rightNeighbor b from hac)]
    have hsb : step x b b = (pairStep (x b) (x c)).1 := by
      unfold step
      rw [if_pos rfl]
    have hbond : barrierBond z b = .outlet := by
      unfold barrierBond
      rw [if_neg hez, if_neg (show b ≠ rightNeighbor z from hea),
          if_pos (show b = rightNeighbor (rightNeighbor z) from rfl)]
    change StockPair.mk (step x b a).stock (step x b b).stock =
      realStep (barrierStock x z) (barrierBond z b) _
    rw [hsa, hsb, hbond]
    change StockPair.mk (x a).stock (pairStep (x b) (x c)).1.stock =
      realStep ⟨(x a).stock, (x b).stock⟩ .outlet (!(x c).stock)
    have hp := congrArg (fun q : Bool × Bool => StockPair.mk (x a).stock q.1) hrow
    cases hb : (x b).stock <;> cases hc : (x c).stock <;>
      simpa [realStep, payer, hbl, hb, hc] using hp
  · have ha' : a ≠ rightNeighbor e := by
      intro hh
      exact hez (succ_inj hh.symm)
    have hb' : b ≠ rightNeighbor e := by
      intro hh
      exact hea (succ_inj hh.symm)
    have hsa : step x e a = x a := by simp [step, Ne.symm hea, ha']
    have hsb : step x e b = x b := by simp [step, Ne.symm heb, hb']
    have hbond : barrierBond z e = .other := by
      unfold barrierBond
      rw [if_neg hez, if_neg (show e ≠ rightNeighbor z from hea),
        if_neg (show e ≠ rightNeighbor (rightNeighbor z) from heb)]
    change StockPair.mk (step x e a).stock (step x e b).stock =
      realStep (barrierStock x z) (barrierBond z e) _
    rw [hsa, hsb, hbond]
    rfl

/-- The literal one-step coupling and same-mark ingress inclusion. -/
theorem barrierCoupled_step {p c1 n : Nat} (x : Config p c1 n)
    (z e : Fin n) (h : LongBarrier x z) (i : StockPair)
    (hle : Below i (barrierStock x z)) :
    Below (idealStep i (barrierBond z e)) (barrierStock (step x e) z) ∧
      (ingress (barrierStock x z) (barrierBond z e) = true →
        ingress i (barrierBond z e) = true) := by
  rw [barrierStock_step x z e h]
  exact oneStep i (barrierStock x z) (barrierBond z e) (barrierAccept x z) hle

/-- Every pre-mark cut in this segment is a long tenure at the same site.
The last selected edge may end the tenure; we do not require its post-state
to be long. -/
def LongBarrierWord {p c1 n : Nat} (z : Fin n) (x : Config p c1 n) :
    List (Fin n) → Prop
  | [] => True
  | e :: w => LongBarrier x z ∧ LongBarrierWord z (step x e) w

/-- Record the selected labels and actual real acceptance at each pre-mark. -/
def observeBarrier {p c1 n : Nat} (z : Fin n) (x : Config p c1 n) :
    List (Fin n) → List OpenQueue.Mark
  | [] => []
  | e :: w => ⟨barrierBond z e, barrierAccept x z⟩ ::
      observeBarrier z (step x e) w

/-- The observed real queue is exactly the projection of the physical
execution for the entire long segment, including its last active mark. -/
theorem barrierStock_run {p c1 n : Nat} (z : Fin n) (x : Config p c1 n)
    (w : List (Fin n)) (h : LongBarrierWord z x w) :
    barrierStock (run x w) z =
      OpenQueue.runReal (barrierStock x z) (observeBarrier z x w) := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih =>
    have hparts : LongBarrier x z ∧ LongBarrierWord z (step x e) w := h
    simp only [run, observeBarrier, OpenQueue.runReal]
    rw [← barrierStock_step x z e hparts.1]
    exact ih (step x e) hparts.2

/-- With reset to 00, every real ingress in the segment is counted by the
ideal queue. The stronger same-mark inclusion is `barrierCoupled_step`. -/
theorem barrierRun_dominates {p c1 n : Nat} (z : Fin n) (x : Config p c1 n)
    (w : List (Fin n)) (h : LongBarrierWord z x w) :
    Below (OpenQueue.runIdeal OpenQueue.empty (observeBarrier z x w))
        (barrierStock (run x w) z) ∧
      OpenQueue.realIngresses (barrierStock x z) (observeBarrier z x w) ≤
      OpenQueue.idealIngresses OpenQueue.empty (observeBarrier z x w) := by
  rw [barrierStock_run z x w h]
  exact OpenQueue.run_below_and_ingresses _ _ _ (OpenQueue.empty_below _)

/-- The actual outlet cannot be identified with the always-open ideal map
when the second and third stocks are both 1, even on a covered long cut. -/
theorem barrierOutlet_not_ideal {p c1 n : Nat} (x : Config p c1 n)
    (z : Fin n) (h : LongBarrier x z)
    (hb : (barrierStock x z).second = true)
    (hc : barrierAccept x z = false) :
    barrierStock (step x (rightNeighbor (rightNeighbor z))) z ≠
      idealStep (barrierStock x z) .outlet := by
  have hbond : barrierBond z (rightNeighbor (rightNeighbor z)) = .outlet := by
    obtain ⟨_, hz, ha⟩ := barrierBondsDistinct h.size z
    unfold barrierBond
    rw [if_neg (Ne.symm hz), if_neg (Ne.symm ha), if_pos rfl]
  rw [barrierStock_step x z _ h, hbond, hc]
  intro he
  have hh := congrArg OpenQueue.StockPair.second he
  simp [idealStep, realStep, hb] at hh

end L4

