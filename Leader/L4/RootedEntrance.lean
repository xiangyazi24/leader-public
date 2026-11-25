import Leader.L4.EntranceQuiet
import Leader.L4.FreshSeparation

/-! The physical rooted entrance does not need MCOV at the initial
cut, or a nondivisibility assumption at any cut. -/
namespace L4.RootedEntrance

def RootNonempty {p c n : Nat} (x : Config p c n) : Prop :=
  ∃ e, EffectiveRootOn x e

def MarkNonempty {p c n : Nat} (x : Config p c n) : Prop :=
  ∃ e, (x e).mark = true

private theorem notLoop {n : Nat} (hn : 4 ≤ n) (e : Fin n) : rightNeighbor e ≠ e := by
  intro h
  have he : liftedSite e 1 = liftedSite e 0 := by simpa [liftedSite_succ,liftedSite_zero] using h
  have hh := liftedSite_inj e (by omega : 1<n) (by omega : 0<n) he
  omega

theorem rootNonempty_of_mark {p c n : Nat} {x : Config p c n} (h : MarkNonempty x) :
    RootNonempty x := by
  obtain ⟨e,he⟩ := h
  exact ⟨e,.inr (.inl he)⟩

theorem mark_iff_root_of_cover {p c n : Nat} (x : Config p c n) (hm : MCOV x) :
    MarkNonempty x ↔ RootNonempty x := by
  refine ⟨rootNonempty_of_mark,?_⟩
  rintro ⟨e,h⟩
  refine ⟨e,?_⟩
  rcases h with h | h | h
  · exact hm e (.inl h)
  · exact h
  · exact hm e (.inr h)

private theorem r0_residue {p c : Nat} (u v : Site p c) :
    (materialize u v).residue = u.residue := by unfold materialize; split <;> rfl

private theorem r0_cover {p c : Nat} (u v : Site p c) :
    (v.leader = true ∨ v.residue ≠ nextResidue (materialize u v).residue) →
      (materialize u v).mark = true := by
  rw [r0_residue]
  intro hd
  rcases hd with h | h <;> simp [materialize,h,defect]

private theorem materialize_of_mark {p c : Nat} (a b : Site p c) (h : a.mark = true) :
    materialize a b = a := by
  cases a
  simp_all [materialize]

private theorem r0_idem {p c : Nat} (u v : Site p c) :
    materialize (materialize u v) v = materialize u v := by
  by_cases h : (materialize u v).mark = true
  · exact materialize_of_mark _ _ h
  · have ha : (materialize u v).mark = false := Bool.eq_false_iff.mpr h
    have hl : v.leader = false := by
      apply Bool.eq_false_iff.mpr
      exact fun hh => h (r0_cover u v (.inl hh))
    have hv : v.residue = nextResidue (materialize u v).residue := by
      by_cases he : v.residue = nextResidue (materialize u v).residue
      · exact he
      · exact (h (r0_cover u v (.inr he))).elim
    have hd : defect (materialize u v) v = false := by unfold defect; rw [hv]; simp only [beq_self_eq_true,Bool.not_true]
    unfold materialize
    change (if v.leader || (materialize u v).mark || defect (materialize u v) v then _ else _) = _
    rw [hl,ha,hd]
    rfl

/-- The selected bond's raw old mark can be written by R0 before any
cover hypothesis. Otherwise the only way to clear a mark is P3, which
writes a real mark to the next bond on the same service. -/
theorem raw_pair_marks {p c : Nat} (u v : Site p c) :
    if geometricPay u v then
      (pairStep u v).1.mark = false ∧ (pairStep u v).2.mark = true
    else (pairStep u v).1.mark = (materialize u v).mark ∧
      (pairStep u v).2.mark = v.mark := by
  have hp : pairStep (materialize u v) v = pairStep u v := by
    have h : stepPrefix (materialize u v) v = stepPrefix u v := by
      simp [stepPrefix,r0_idem]
    simp [pairStep,h]
  have hg : geometricPay (materialize u v) v = geometricPay u v := by
    simp [geometricPay,r0_idem]
  have h := covered_pair_marks (materialize u v) v (r0_cover u v)
  rw [hp,hg] at h
  by_cases he : geometricPay u v = true
  · rw [if_pos he] at h ⊢
    exact ⟨h.2.1,h.2.2⟩
  · rw [if_neg he] at h ⊢
    exact h

private theorem pay_gives_mark {p c n : Nat} (hn : 4 ≤ n) (x : Config p c n)
    (e : Fin n) (h : geometricPay (x e) (x (rightNeighbor e)) = true) :
    MarkNonempty (step x e) := by
  have hh := raw_pair_marks (x e) (x (rightNeighbor e))
  rw [if_pos h] at hh
  exact ⟨rightNeighbor e,by simpa [step,notLoop hn e] using hh.2⟩

private theorem no_pay_marks {p c n : Nat} (hn : 4 ≤ n) (x : Config p c n) (e : Fin n)
    (hp : geometricPay (x e) (x (rightNeighbor e)) = false) :
    (step x e e).mark = (materialize (x e) (x (rightNeighbor e))).mark ∧
    ∀ f, f ≠ e → (step x e f).mark = (x f).mark := by
  have hh := raw_pair_marks (x e) (x (rightNeighbor e))
  rw [if_neg (by simp [hp])] at hh
  refine ⟨by simpa [step] using hh.1,?_⟩
  intro f hf
  by_cases he : f = rightNeighbor e
  · subst f; simpa [step,notLoop hn e] using hh.2
  · simp only [step,if_neg hf,if_neg he]

/-- Once explicit, a carrier exists forever, even from unnormalized
scratch and when the ring is flat or p divides n. -/
theorem mark_nonempty_step {p c n : Nat} (hn : 4 ≤ n) (x : Config p c n)
    (e : Fin n) (h : MarkNonempty x) : MarkNonempty (step x e) := by
  by_cases hp : geometricPay (x e) (x (rightNeighbor e)) = true
  · exact pay_gives_mark hn x e hp
  · have hh := no_pay_marks hn x e (Bool.eq_false_iff.mpr hp)
    obtain ⟨f,hf⟩ := h
    by_cases he : f = e
    · subst f
      refine ⟨e,?_⟩
      rw [hh.1]
      simp [materialize,hf]
    · exact ⟨f,(hh.2 f he).trans hf⟩

private theorem no_pay_residues {p c n : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (e : Fin n)
    (hp : geometricPay (x e) (x (rightNeighbor e)) = false) (i : Fin n) :
    (step x e i).residue = (x i).residue := by
  by_cases he : i = e
  · subst i
    simpa [step] using (pair_geometric_fields (x e) (x (rightNeighbor e))).1
  · by_cases he' : i = rightNeighbor e
    · subst i
      have h := (pair_geometric_fields (x e) (x (rightNeighbor e))).2.2
      rw [if_neg (by simp [hp])] at h
      simpa [step,notLoop hn e] using h
    · simp only [step,if_neg he,if_neg he']

/-- The exact pre-cover union (explicit mark, native leader, residue
defect) cannot disappear. An uncovered root whose selected mark could
be paid is materialized by R0 first, and leaves a marked successor. -/
theorem root_nonempty_step {p c n : Nat} (hn : 4 ≤ n) (x : Config p c n)
    (e : Fin n) (h : RootNonempty x) : RootNonempty (step x e) := by
  by_cases hP : geometricPay (x e) (x (rightNeighbor e)) = true
  · exact rootNonempty_of_mark (pay_gives_mark hn x e hP)
  have hp := Bool.eq_false_iff.mpr hP
  have hh := no_pay_marks hn x e hp
  obtain ⟨f,hf⟩ := h
  by_cases hE : f = e
  · subst f
    have hM : (materialize (x e) (x (rightNeighbor e))).mark = true := by
      rcases hf with hu | hu | hu
      · exact r0_cover _ _ (.inl hu)
      · simp [materialize,hu]
      · exact r0_cover _ _ (.inr (by simpa only [r0_residue] using hu))
    exact rootNonempty_of_mark ⟨e,hh.1.trans hM⟩
  · refine ⟨f,?_⟩
    rcases hf with hL | hM | hD
    · apply Or.inl
      have hR : rightNeighbor f ≠ rightNeighbor e := fun H =>
        hE (FreshSeparation.succ_inj H)
      by_cases hX : rightNeighbor f = e
      · rw [hX] at hL ⊢
        simpa [step] using (pair_geometric_fields (x e) (x (rightNeighbor e))).2.1.trans hL
      · simpa only [step,if_neg hX,if_neg hR] using hL
    · exact .inr (.inl ((hh.2 f hE).trans hM))
    · exact .inr (.inr (by
        rw [no_pay_residues hn x e hp (rightNeighbor f), no_pay_residues hn x e hp f]
        exact hD))

theorem root_nonempty_run {p c n : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (w : List (Fin n)) (h : RootNonempty x) :
    RootNonempty (run x w) := by
  induction w generalizing x with
  | nil => exact h
  | cons e w ih => exact ih (step x e) (root_nonempty_step hn x e h)

theorem rooted_of_not_dvd {p c n : Nat} (hn : 0<n) (x : Config p c n) (hnd : ¬ p ∣ n) :
    RootNonempty x := by
  classical
  by_cases h : RootNonempty x
  · exact h
  · have hm : MCOV x := fun e hr => False.elim (h ⟨e,by
        rcases hr with hl | hd
        · exact Or.inl hl
        · exact Or.inr (Or.inr hd)⟩)
    exact rootNonempty_of_mark (covered_mark_exists_of_not_dvd x ⟨0,hn⟩ hm hnd)

/-- Ordered cover from arbitrary *rooted* scratch. The generated cut
carries both covers and a real mark, even on a divisible ring. The
post-cover theorem does not get to assume a later lucky seed. -/
theorem rooted_after_cover_bound {p c n : Nat} (hn : 4 ≤ n)
    (target : Config p c n → Prop) (B : Nat)
    (hpost : ∀ y, MCOV y → COV y → MarkNonempty y →
      IIDExpectedHittingTimeAtMost step target y B)
    (x : Config p c n) (hx : RootNonempty x) :
    IIDExpectedHittingTimeAtMost step target x (n*n+B) := by
  let good := fun y : List (Fin n) × Config p c n =>
    EntranceCover.coverInvariant y ∧ RootNonempty y.2
  apply EntranceCover.orderedAllEdges_then_physical step target good B
  · intro y e hy
    exact ⟨EntranceCover.coverInvariant_step hn y e hy.1,
      root_nonempty_step hn y.2 e hy.2⟩
  · intro y hy
    have h := (EntranceCover.coverInvariant_endpoint y).mp hy.1
    exact hpost y h.1 h.2 ((mark_iff_root_of_cover y h.1).mpr hy.2)
  · refine ⟨?_,hx⟩
    intro i hi
    exact (hi (List.mem_ofFn.mpr ⟨i,rfl⟩)).elim

theorem rooted_cover_expected {p c n : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (hx : RootNonempty x) :
    IIDExpectedHittingTimeAtMost step (fun y => MCOV y ∧ COV y ∧ MarkNonempty y) x (n*n) := by
  have h := rooted_after_cover_bound hn (fun y => MCOV y ∧ COV y ∧ MarkNonempty y) 0
    (fun y hm hc hr t => by rw [iidHitCost_of_target _ _ _ ⟨hm,hc,hr⟩]; exact Nat.zero_le _) x hx
  simpa only [Nat.add_zero] using h

open EntranceCover in
/-- Observer form of the rooted cover glue for the all-tag entrance.
The cover-completing mark is not counted again after observer launch. -/
theorem rooted_after_cover_observer_bound {β : Type} {p c1 n : Nat} (hn : 4 ≤ n)
    (second : β → Fin n → β) (init : Config p c1 n → β) (target : β → Prop)
    (physical : Config p c1 n → Prop) (project : β → Config p c1 n)
    (hinit : ∀ x, project (init x) = x)
    (hstep : ∀ y e, project (second y e) = step (project y) e)
    (hhit : ∀ y, target y → physical (project y))
    (B : Nat)
    (hpost : ∀ x, MCOV x → COV x → MarkNonempty x → IIDExpectedHittingTimeAtMost second target (init x) B)
    (x : Config p c1 n) (hx : RootNonempty x) :
    IIDExpectedHittingTimeAtMost step physical x (n * n + B) := by
  let visit := List.ofFn (fun e : Fin n => e)
  let proj : Sum (List (Fin n) × Config p c1 n) β → Config p c1 n :=
    fun y => match y with | .inl z => z.2 | .inr z => project z
  have hstart (v : List (Fin n)) (x : Config p c1 n) :
      proj (startStage init v x) = x := by
    cases v <;> simp [startStage,proj,hinit]
  have hproj (y : Sum (List (Fin n) × Config p c1 n) β) (e : Fin n) :
      proj (stagedStep step second init y e) = step (proj y) e := by
    cases y with
    | inr y => exact hstep y e
    | inl z => obtain ⟨v,y⟩ := z; exact hstart (advance v e) (step y e)
  have hphys : ∀ y, stagedTarget (n := n) (α := Config p c1 n) target y → physical (proj y) := by
    intro y hy; cases y with
    | inl z => exact hy.elim
    | inr z => exact hhit z hy
  intro t
  let good := fun z : List (Fin n) × Config p c1 n => coverInvariant z ∧ RootNonempty z.2
  have haux := stagedCover_then step second init target good B
    (fun y e h => ⟨coverInvariant_step hn y e h.1,root_nonempty_step hn y.2 e h.2⟩)
    (fun y hy => let h := (coverInvariant_endpoint y).mp hy.1
      hpost y h.1 h.2 ((mark_iff_root_of_cover y h.1).mpr hy.2))
    visit x ⟨(by intro i hi; exact (hi (List.mem_ofFn.mpr ⟨i,rfl⟩)).elim),hx⟩ t
  have hh := iidHitCost_le_of_projection step (stagedStep step second init) physical
    (stagedTarget target) proj hproj hphys t (startStage init visit x)
  have hc := Nat.le_trans hh haux
  rw [hstart] at hc
  simpa [visit] using hc

/-- The complementary decoded-rootless set stays rootless on *every*
mark even with arbitrary stock, noncanonical rails, signals, and bullets.
This is why an arbitrary-start extension across divisible rings is
false: the rooted premise is exact, not a technical convenience. -/
theorem root_empty_step {p c n : Nat} (hn : 4 ≤ n) (x : Config p c n)
    (e : Fin n) (h : ¬ RootNonempty x) : ¬ RootNonempty (step x e) := by
  have fields (f : Fin n) : (x f).mark = false ∧
      (x (rightNeighbor f)).residue = nextResidue (x f).residue ∧
      (x (rightNeighbor f)).leader = false := by
    have hf : ¬ EffectiveRootOn x f := fun H => h ⟨f,H⟩
    exact (by
      refine ⟨Bool.eq_false_iff.mpr (fun H => hf (.inr (.inl H))), ?_, ?_⟩
      · by_cases he : (x (rightNeighbor f)).residue = nextResidue (x f).residue
        · exact he
        · exact (hf (.inr (.inr he))).elim
      · exact Bool.eq_false_iff.mpr (fun H => hf (.inl H)))
  have ho := fields e
  have hg := ordinary_pair_geometry _ _ ho.1 ho.2.1 ho.2.2
  have stable (i : Fin n) :
      (step x e i).leader = (x i).leader ∧
      (step x e i).mark = (x i).mark ∧
      (step x e i).residue = (x i).residue := by
    by_cases he : i=e
    · subst i; simpa [step] using hg.1
    · by_cases hr : i=rightNeighbor e
      · subst i
        simpa [step,notLoop hn e] using And.intro hg.2.1 (And.intro hg.2.2.1 hg.2.2.2.1)
      · simp only [step,if_neg he,if_neg hr,and_self]
  rintro ⟨f,hf⟩
  apply h
  refine ⟨f,?_⟩
  unfold EffectiveRootOn at hf ⊢
  rwa [(stable f).2.1,(stable f).2.2,(stable (rightNeighbor f)).1,(stable (rightNeighbor f)).2.2] at hf

theorem root_empty_run {p c n : Nat} (hn : 4 ≤ n) (x : Config p c n)
    (w : List (Fin n)) (h : ¬ RootNonempty x) : ¬ RootNonempty (run x w) := by
  induction w generalizing x with
  | nil => exact h
  | cons e w ih => exact ih (step x e) (root_empty_step hn x e h)

def flatUnrooted4 : Config 2 12 4 := fun i =>
  { residue := ⟨i.val%2, by omega⟩, mark := false, leader := false, bullet := .none,
    shield := false, signal := .zero, stock := false, source := .off, rail := .e }

theorem flatUnrooted4_never_safe (w : List (Fin 4)) : ¬ SafeOneLeader (run flatUnrooted4 w) := by
  have h : ¬ RootNonempty flatUnrooted4 := by
    intro h
    obtain ⟨i,hi⟩ := h
    have hh : ∀ j : Fin 4, ¬ EffectiveRootOn flatUnrooted4 j := by
      unfold EffectiveRootOn
      decide
    exact hh i hi
  intro hs
  obtain ⟨i,hi⟩ := hs
  have hL : (run flatUnrooted4 w i).leader = true := (hi [] i).mpr rfl
  let e := liftedSite i (4-1)
  have he : rightNeighbor e = i := by
    rw [show rightNeighbor e = liftedSite i 4 by
      exact (liftedSite_succ i 3).symm, liftedSite_full]
  exact root_empty_run (by decide) flatUnrooted4 w h ⟨e,.inl (he.symm ▸ hL)⟩

end L4.RootedEntrance
