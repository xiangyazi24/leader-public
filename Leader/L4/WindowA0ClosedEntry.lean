import Leader.L4.WindowA0IH
import Leader.L4.WindowA0Ledger

namespace L4.WindowA0ClosedEntry
open SevenTagCharge WindowFourHeadTrace WindowA0Route

/-- A full tagged A0 state and its clockwise drained-gap coordinate.
The coordinate is bookkeeping only; the old tag slots determine
the top and right head of the physical cut. -/
structure State (p c n : Nat) where
  tag : WindowA0Ledger.State p c n
  gap : Nat

def cut {p c n : Nat} (x : State p c n) : WindowA0IH.Cut p c n :=
  ⟨x.tag.ledger.config,rightNeighbor x.tag.iSlot,x.gap,x.tag.reason.isSome⟩

def next {p c n : Nat} (S : WindowA0Ledger.Scope n) (x : State p c n) (e : Fin n) :
    State p c n :=
  let y := WindowA0Ledger.next S x.tag e
  ⟨y, if y.reason.isSome then x.gap
      else x.gap-(if moves x.tag.ledger e x.tag.iSlot then 1 else 0)⟩

def Admitted {p c n : Nat} (z0 : Config p c n) (S : WindowA0Ledger.Scope n)
    (J : Fin n) (H : Nat) (x : State p c n) : Prop :=
  WindowA0Ledger.done x.tag ∨
    (WindowA0IH.Live J H (cut x) ∧ WindowA0Ledger.Live z0 S x.tag ∧
      rightNeighbor x.tag.jSlot=J)

private theorem cold_done {p c n : Nat} {x : WindowA0Ledger.State p c n}
    (h : ¬WindowA0Ledger.done x) : x.reason=none := by
  cases hr : x.reason
  · rfl
  · exact (h (by simp [WindowA0Ledger.done,hr])).elim

private theorem incoming_top {n : Nat} (a : Fin n) :
    GGStage.incoming (rightNeighbor a) 0=a := by
  apply FreshSeparation.succ_inj
  rw [GGStage.incoming_right,liftedSite_zero]

theorem close {p c n : Nat} {z0 : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat) (x : State p c n)
    (e : Fin n) (old : Admitted z0 S J H x) :
    Admitted z0 S J H (next S x e) := by
  let z := x.tag.ledger
  let top := rightNeighbor x.tag.iSlot
  let m := if moves z e x.tag.iSlot then 1 else 0
  by_cases hD : WindowA0Ledger.done (WindowA0Ledger.next S x.tag e)
  · exact .inl hD
  have hold : ¬WindowA0Ledger.done x.tag := by
    intro h
    apply hD
    unfold WindowA0Ledger.done at *
    rw [WindowA0Ledger.terminal_sticky S x.tag e h]
    exact h
  obtain ⟨hi,hg,hJ⟩ := old.resolve_left hold
  have hg0 := hg
  obtain ⟨hv,hStart,hI,hJtag,hK,hGhostI,hGhostJ⟩ := hg
  have hr : routeTwo S.group S.iTag S.jTag z e=.keep := by
    exact Classical.byContradiction (fun he =>
       hD ((WindowA0Ledger.physical_exit_iff S x.tag e hStart).mpr he))
  have hN : WindowA0Ledger.next S x.tag e =
      ⟨advance z e,landing z e x.tag.iSlot,landing z e x.tag.jSlot,
        landing z e x.tag.kSlot,none⟩ := by
    simp [WindowA0Ledger.next,hStart,z,hr]
  have hMove : (GGStage.moved z.config top e 0).toNat=m := by
    unfold m GGStage.moved moves
    rw [incoming_top]
    by_cases he : e=x.tag.iSlot
    · have ht : (e == x.tag.iSlot)=true := beq_iff_eq.mpr he
      rw [ht]
      simp only [Bool.true_and]
      by_cases hp : geometricPay (z.config e) (z.config (rightNeighbor e))=true
      · simp [hp]; exact he
      · simp [Bool.eq_false_iff.mpr hp]
    · simp [he,show (e == x.tag.iSlot)=false from Bool.eq_false_iff.mpr (fun h => he (beq_iff_eq.mp h))]
  have hIHead : rightNeighbor (landing z e x.tag.iSlot)=liftedSite top m := by
    unfold landing m
    by_cases hd : moves z e x.tag.iSlot
    · simp [hd,top,liftedSite_succ,liftedSite_zero]
    · simp [hd,top,liftedSite_zero]
  have hJSlot : x.tag.jSlot=GGStage.incoming top x.gap := by
    apply FreshSeparation.succ_inj
    rw [GGStage.incoming_right]
    exact hJ.trans hi.fixedRight.symm
  have hjPos : x.gap>0 := hi.gapPos
  have hmJ : (z.config (GGStage.incoming top x.gap)).mark=true := by
    rw [←hJSlot]
    simpa [hJtag] using (hv.covers x.tag.jSlot).symm
  have hnJ : GGStage.moved z.config top e x.gap=false := by
    apply (WindowA0Drained.drained_step hn z.config top e hjPos hi.markTop hmJ hi.empty _).1
    intro i hh
    cases i with
    | zero => simpa only [liftedSite_zero] using hGhostI
    | succ i =>
      apply Bool.eq_false_iff.mpr
      intro hL
      have hm := hi.mc (liftedSite top i) (.inl (by rwa [←liftedSite_succ]))
      have H : (z.config (liftedSite top i)).mark=false := hi.openBonds i hh
      change (z.config (liftedSite top i)).mark=true at hm
      rw [H] at hm
      cases hm
  have noPayJ : ¬moves z e x.tag.jSlot := by
    rintro ⟨he,hp⟩
    have h : GGStage.moved z.config top e x.gap=true := by
      unfold GGStage.moved
      rw [←hJSlot]
      exact Bool.and_eq_true_iff.mpr ⟨beq_iff_eq.mpr he,hp⟩
    rw [hnJ] at h
    cases h
  have hJB : rightNeighbor (landing z e x.tag.jSlot)=J := by
    simpa only [landing,if_neg noPayJ] using hJ
  have hLive := (WindowA0Ledger.live_or_terminal hn S x.tag e hg0).resolve_left hD
  refine .inr ⟨?_,hLive,?_⟩
  · have hStop : (cut x).stopped=false := by simp [cut,hStart]
    let y := WindowA0IH.advance (fun _ _ => false) (cut x) e
    have topGhost : (step z.config e (liftedSite top m)).leader=false := by
      have h := hLive.2.2.2.2.2.1
      rw [hN] at h
      simpa only [hIHead,SevenTagCharge.advance] using h
    have rightGhost : (step z.config e (WindowA0IH.target (cut x))).leader=false := by
      have h := hLive.2.2.2.2.2.2
      rw [hN] at h
      have H := hi.fixedRight
      rw [H]
      simpa only [hJB,SevenTagCharge.advance] using h
    have ret : GGStage.retires z.config top e 0=false := by
      unfold GGStage.retires
      cases he : GGStage.moved z.config top e 0
      · rfl
      · have hm := Bool.and_eq_true_iff.mp he
        have hit := beq_iff_eq.mp hm.1
        rw [incoming_top] at hit
        have ht : z.slots e=some S.iTag := hit.symm ▸ hI
        have hR := WindowScopedSupplier.tracked_no_retirement_of_group_keep S.group z e S.iTag S.iIn
          ht (empty_group_loss_of_two_keep z S.group S.iTag S.jTag e hr)
        change (geometricPay (z.config e) (z.config (rightNeighbor e)) && (z.config (rightNeighbor e)).mark)=false at hR
        rw [hm.2,hit,Bool.true_and] at hR
        simpa only [he,liftedSite_zero,Bool.true_and] using hR
    have yEq : y=cut (next S x e) := by
      unfold y WindowA0IH.advance
      rw [if_neg (show ¬(cut x).stopped=true by simp [hStop])]
      have hstop : GGStage.retires (cut x).config (cut x).top e 0=false := ret
      have hM : (GGStage.moved (cut x).config (cut x).top e 0).toNat=m := hMove
      simp only [hstop,hM,Bool.or_false,Bool.false_or]
      change (⟨step z.config e,liftedSite top m,x.gap-m,
        (step z.config e (liftedSite top m)).leader ||
        (step z.config e (WindowA0IH.target (cut x))).leader⟩ : WindowA0IH.Cut p c n)=_
      rw [topGhost,rightGhost]
      simp only [cut,next,hN,Option.isSome_none]
      rw [hIHead]
      rfl
    have yLive := WindowA0IH.close hn (fun _ _ => false) J H (cut x) e (.inr hi)
    change WindowA0IH.I_H J H y at yLive
    rw [yEq] at yLive
    exact yLive.resolve_left (by simpa [cut,next,WindowA0Ledger.done] using hD)
  · change rightNeighbor (WindowA0Ledger.next S x.tag e).jSlot=J
    rw [hN]
    exact hJB

theorem close_word {p c n : Nat} {z0 : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat) (x : State p c n)
    (w : List (Fin n)) (old : Admitted z0 S J H x) :
    Admitted z0 S J H (GGTiming.runMarks (next S) x w) := by
  induction w generalizing x with
  | nil => exact old
  | cons e w ih => exact ih _ (close hn S J H x e old)

theorem projects {p c n : Nat} (S : WindowA0Ledger.Scope n) (x : State p c n)
    (w : List (Fin n)) :
    (GGTiming.runMarks (next S) x w).tag.ledger=observe x.tag.ledger w := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih =>
    change (GGTiming.runMarks (next S) (next S x e) w).tag.ledger=_
    rw [ih]
    change observe (WindowA0Ledger.next S x.tag e).ledger w=observe (advance x.tag.ledger e) w
    rw [WindowA0Ledger.physical_step]

end L4.WindowA0ClosedEntry
