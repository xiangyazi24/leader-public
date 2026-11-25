import Leader.L4.WindowA0ForeignBirth
import Leader.L4.WindowScopedRoute

namespace L4.WindowA0Route
open SevenTagCharge WindowLocal

/-- Entry routing uses both designated candidates. A group loss
detected in the first lookup wins before either candidate's birth. -/
def routeTwo {p c n : Nat} (g : List (Fin n)) (a b : Fin n)
    (z : Ledger p c n) (e : Fin n) : Event n :=
  let r := route g [] (some a) z e
  if r=.keep then route g [] (some b) z e else r

theorem keep_iff {p c n : Nat} (g : List (Fin n)) (a b : Fin n)
    (z : Ledger p c n) (e : Fin n) :
    routeTwo g a b z e=.keep ↔
      route g [] (some a) z e=.keep ∧ route g [] (some b) z e=.keep := by
  unfold routeTwo
  by_cases h : route g [] (some a) z e=.keep <;> simp [h]

theorem selected_loss_first {p c n : Nat} (g : List (Fin n)) (a b k : Fin n)
    (z : Ledger p c n) (e : Fin n) (h : selectedGroupLoss g z e=some k) :
    routeTwo g a b z e=.reward k := by
  have hr : route g [] (some a) z e=.reward k := by unfold route; rw [h]
  unfold routeTwo
  rw [hr,if_neg (by intro h; cases h)]

theorem observed_keeps_exterior_birth :
    routeTwo [0,2,4,6,8,10,12] 2 4 (initial WindowA0ForeignBirth.tape) 14=.keep := by
  apply (keep_iff _ _ _ _ _).mpr
  decide

/-- An A0 ghost remains a ghost at the *new* head on a keep; a
selected transfer cannot be mistaken for a birth of the old resident. -/
theorem ghost_after_keep {p c n : Nat} {z0 : Config p c n} (hn : 4≤n)
    (z : Ledger p c n) (g : List (Fin n)) (a s e : Fin n)
    (hz : Valid z z0) (ha : a∈g) (hslot : z.slots s=some a)
    (hg : (z.config (rightNeighbor s)).leader=false)
    (hk : route g [] (some a) z e=.keep) :
    let t := if e=s then landingSlot z.config e else s
    (step z.config e (rightNeighbor t)).leader=false := by
  let x := z.config
  by_cases he : e=s
  · subst e
    have hNo : selectedGroupLoss g z s=none := by
      unfold route at hk
      split at hk
      · cases hk
      · assumption
    have hNoR := WindowScopedSupplier.tracked_no_retirement_of_group_keep g z s a ha hslot hNo
    by_cases hp : geometricPay (x s) (x (rightNeighbor s))=true
    · have hb := FreshTimerEpoch.paid_landing_off hn x s hz.markCover hz.sourceCover hp hNoR
      simp only [if_true,landingSlot,show geometricPay (z.config s) (z.config (rightNeighbor s))=true from hp]
      exact hb.2.1
    · simp only [if_true,landingSlot,show geometricPay (z.config s) (z.config (rightNeighbor s))=false from Bool.eq_false_iff.mpr hp, Bool.false_eq_true, if_false]
      apply Bool.eq_false_iff.mpr
      intro hl
      have hBorn : birthAt x s=true := by simp [birthAt,x,hg,hl]
      have hh := (target_birth_result hn g [] z s a hz.markCover hz.sourceCover hslot hBorn).1
      rw [hk] at hh
      cases hh
  · simp only [if_neg he]
    have hr : rightNeighbor s≠rightNeighbor e := by
      intro h
      exact he (FreshSeparation.succ_inj h).symm
    by_cases hq : rightNeighbor s=e
    · rw [hq] at hg ⊢
      have H := (pair_geometric_fields (z.config e) (z.config (rightNeighbor e))).2.1
      simpa only [step,if_pos rfl] using H.trans hg
    · simpa [step,hq,hr] using hg

theorem empty_group_loss_of_two_keep {p c n : Nat} (z : Ledger p c n)
    (g : List (Fin n)) (a b e : Fin n) (h : routeTwo g a b z e=.keep) :
    selectedGroupLoss g z e=none := by
  cases he : selectedGroupLoss g z e with
  | none => rfl
  | some k => rw [selected_loss_first g a b k z e he] at h; cases h

/-- The literal three-head preparation is a sound projection on every
raw keep of the full group router. Foreign events cannot cause the
local A0 monitor to set its stopped bit. -/
theorem gg_step_of_two_keep {p c n : Nat} {z0 : Config p c n} (hn : 4≤n)
    (z : Ledger p c n) (g : List (Fin n)) (a b cTag base e : Fin n)
    (H : GGStage.Heads) (hz : Valid z z0)
    (ha : a∈g) (hb : b∈g) (hc : cTag∈g)
    (hA : z.slots (GGStage.incoming base H.i)=some a)
    (hB : z.slots (GGStage.incoming base H.j)=some b)
    (hC : z.slots (GGStage.incoming base H.k)=some cTag)
    (gi : (z.config (liftedSite base H.i)).leader=false)
    (gj : (z.config (liftedSite base H.j)).leader=false)
    (hk : routeTwo g a b z e=.keep) :
    let lift := fun d => d+(GGStage.moved z.config base e d).toNat
    GGStage.advance base (GGStage.init z.config H) e =
      GGStage.init (advance z e).config ⟨lift H.i,lift H.j,lift H.k⟩ := by
  let x := z.config
  let lift := fun d => d+(GGStage.moved x base e d).toNat
  have empty := empty_group_loss_of_two_keep z g a b e hk
  have ret (d : Nat) (tag : Fin n) (ht : tag∈g)
      (hs : z.slots (GGStage.incoming base d)=some tag) :
      GGStage.retires x base e d=false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have h' := Bool.and_eq_true_iff.mp h
    have hm := Bool.and_eq_true_iff.mp h'.1
    have he := beq_iff_eq.mp hm.1
    have hSlotE : z.slots e=some tag := he.symm ▸ hs
    have Hret := WindowScopedSupplier.tracked_no_retirement_of_group_keep g z e tag ht hSlotE empty
    change (geometricPay (x e) (x (rightNeighbor e)) && (x (rightNeighbor e)).mark)=false at Hret
    rw [hm.2,he,GGStage.incoming_right,h'.2] at Hret
    cases Hret
  have land (d : Nat) :
      rightNeighbor (if e=GGStage.incoming base d then landingSlot x e else GGStage.incoming base d)=
        liftedSite base (lift d) := by
    unfold lift GGStage.moved
    by_cases he : e=GGStage.incoming base d
    · subst e
      cases hp : geometricPay (x (GGStage.incoming base d))
          (x (rightNeighbor (GGStage.incoming base d)))
      · have hh := hp
        rw [GGStage.incoming_right] at hh
        simp [landingSlot,hh,GGStage.incoming_right]
      · have hh := hp
        rw [GGStage.incoming_right] at hh
        simp [landingSlot,hh,GGStage.incoming_right,liftedSite_succ]
    · have hex : (e == GGStage.incoming base d)=false :=
        Bool.eq_false_iff.mpr (fun H => he (beq_iff_eq.mp H))
      simp [he,hex,GGStage.incoming_right]
  have gI := ghost_after_keep hn z g a (GGStage.incoming base H.i) e hz ha hA
    (by simpa only [GGStage.incoming_right] using gi) ((keep_iff g a b z e).mp hk).1
  have gJ := ghost_after_keep hn z g b (GGStage.incoming base H.j) e hz hb hB
    (by simpa only [GGStage.incoming_right] using gj) ((keep_iff g a b z e).mp hk).2
  dsimp only at gI gJ
  rw [land H.i] at gI
  rw [land H.j] at gJ
  change (step x e (liftedSite base (lift H.i))).leader=false at gI
  change (step x e (liftedSite base (lift H.j))).leader=false at gJ
  unfold GGStage.advance
  change (if _ then _ else if GGStage.retires x base e H.i ||
      GGStage.retires x base e H.j || GGStage.retires x base e H.k ||
      (step x e (liftedSite base (lift H.i))).leader ||
      (step x e (liftedSite base (lift H.j))).leader then _ else _) = _
  simp only [GGStage.init,ret H.i a ha hA,ret H.j b hb hB,ret H.k cTag hc hC,
    gI,gJ,Bool.false_or,Bool.false_eq_true,if_false]
  rfl

#print axioms gg_step_of_two_keep
#print axioms ghost_after_keep
#print axioms keep_iff
#print axioms selected_loss_first
#print axioms observed_keeps_exterior_birth
end L4.WindowA0Route
