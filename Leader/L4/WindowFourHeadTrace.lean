import Leader.L4.WindowFourHeadStock

namespace L4.WindowFourHeadTrace
open WindowFourHeadStock RearFrontStock SevenTagCharge RankPhysical

/-- Three consecutive lifted slots relevant to stock accounting. j is
J's incoming slot, k is K's, and w is strictly between them. The fourth
head, the living supplier of J, lies outside this tracked inventory. -/
structure Cut {p c n : Nat} (z : Ledger p c n) (j w k a b cTag : Fin n)
    (b0 d : Nat) : Prop where
  jTag : z.slots j=some a
  wTag : z.slots w=some b
  kTag : z.slots k=some cTag
  wLift : liftedSite (rightNeighbor j) b0=w
  kLift : liftedSite (rightNeighbor j) d=k
  wBefore : b0<d
  width : d+1<n
  ghostJ : (z.config (rightNeighbor j)).leader=false
  ghostW : (z.config (rightNeighbor w)).leader=false
  noOther : ∀ i, i<d → i≠b0 →
    (z.config (liftedSite (rightNeighbor j) i)).mark=false

theorem Cut.nonliving {p c n : Nat} {z : Ledger p c n} {j w k a b cTag : Fin n}
    {b0 d : Nat} (h : Cut z j w k a b cTag b0 d) (mc : MCOV z.config) :
    ∀ i, InRear (rightNeighbor j) d i → (z.config i).leader=false := by
  rintro i ⟨l,hl,rfl⟩
  cases l with
  | zero => simpa [liftedSite_zero] using h.ghostJ
  | succ l =>
    by_cases hb : l=b0
    · subst l
      simpa [liftedSite_succ,h.wLift] using h.ghostW
    · apply Bool.eq_false_iff.mpr
      intro hL
      have hm := mc (liftedSite (rightNeighbor j) l)
        (.inl (by simpa [liftedSite_succ] using hL))
      rw [h.noOther l (by omega) hb] at hm
      cases hm

private theorem no_loop {n : Nat} (hn : 4≤n) (e : Fin n) : e≠rightNeighbor e := by
  intro h
  have hh : liftedSite e 0=liftedSite e 1 := by simpa [liftedSite_succ,liftedSite_zero] using h
  have H := liftedSite_inj e (by omega : 0<n) (by omega : 1<n) hh
  omega

/-- A paid tracked slot must transfer to an empty target under the
actual selected-group loss test, not a global no-retirement premise. -/
theorem tracked_paid_transfer {p c n : Nat} (hn : 4≤n)
    (z : Ledger p c n) (g : List (Fin n)) (e a : Fin n)
    (ht : Covers z.config z.slots)
    (ha : a∈g) (hs : z.slots e=some a)
    (hKeep : WindowLocal.selectedGroupLoss g z e=none)
    (hp : geometricPay (z.config e) (z.config (rightNeighbor e))=true) :
    z.slots (rightNeighbor e)=none ∧ (advance z e).slots (rightNeighbor e)=some a := by
  have hR := WindowScopedSupplier.tracked_no_retirement_of_group_keep g z e a ha hs hKeep
  have hm : (z.config (rightNeighbor e)).mark=false := by simpa [retirement,hp] using hR
  have H := (ht (rightNeighbor e)).trans hm
  have hnone : z.slots (rightNeighbor e)=none := by
    cases h : z.slots (rightNeighbor e) <;> simp_all
  refine ⟨hnone,?_⟩
  change slotsStep z.config z.slots e (rightNeighbor e)=some a
  rw [show slotsStep z.config z.slots e = SevenTagCharge.move z.slots e by simp [slotsStep,hp]]
  rw [(paid_mover_or_resident hn z.slots e).2,hnone,hs]
  rfl

/-- On a retained mark, every observed slot keeps its tag or the paid
mover transfers one site. Exterior arrivals into an occupied tracked
slot keep the resident. -/
theorem tracked_landing {p c n : Nat} (hn : 4≤n)
    (z : Ledger p c n) (g : List (Fin n)) (e s a : Fin n)
    (ht : Covers z.config z.slots) (ha : a∈g) (hs : z.slots s=some a)
    (hk : WindowLocal.selectedGroupLoss g z e=none) :
    (advance z e).slots
      (if e=s ∧ geometricPay (z.config e) (z.config (rightNeighbor e))=true
        then rightNeighbor s else s)=some a := by
  by_cases hp : geometricPay (z.config e) (z.config (rightNeighbor e))=true
  · by_cases he : e=s
    · subst s
      simpa [hp] using (tracked_paid_transfer hn z g e a ht ha hs hk hp).2
    · simp only [he,false_and,if_false]
      change slotsStep z.config z.slots e s=some a
      simp only [slotsStep,hp,if_true,SevenTagCharge.move,Ne.symm he,if_false]
      split <;> simp [hs]
  · have hf := Bool.eq_false_iff.mpr hp
    simp [advance,slotsStep,hf,hs]

/-- Actual literal classification. The boolean selected loss test is the
only retirement filter. None of the premises forbids exterior births,
deaths or retirements. -/
theorem classify {p c n : Nat} (hn : 4≤n)
    (z : Ledger p c n) (g : List (Fin n)) (e j w k a b cTag : Fin n)
    (b0 d : Nat) (h : Cut z j w k a b cTag b0 d)
    (mc : MCOV z.config) (ht : Covers z.config z.slots)
    (_hKeep : WindowLocal.selectedGroupLoss g z e=none) :
    let r := rightNeighbor j
    let pay := geometricPay (z.config e) (z.config (rightNeighbor e))=true
    let r' := if e=j ∧ pay then rightNeighbor r else r
    let d' := if e=j ∧ pay then d-1 else if e=k ∧ pay then d+1 else d
    let credit := if e=w ∧ pay then 1 else 0
    Row z.config r e d r' d' credit := by
  classical
  let r := rightNeighbor j
  have nj (i : Nat) (hi : i<n-1) : liftedSite r i≠j := by
    intro he
    have hE : liftedSite r (i+1)=r := by rw [liftedSite_succ,he]
    have HH := liftedSite_inj r (by omega : i+1<n) (by omega : 0<n)
      (hE.trans (liftedSite_zero r).symm)
    omega
  have jw : w≠j := by rw [←h.wLift]; exact nj _ (by have := h.width; have := h.wBefore; omega)
  have jk : k≠j := by rw [←h.kLift]; exact nj _ (by have := h.width; omega)
  have wk : w≠k := by
    rw [←h.wLift,←h.kLift]
    intro he
    have hh := liftedSite_inj r (by have := h.wBefore; have := h.width; omega : b0<n)
      (by have := h.width; omega : d<n) he
    have := h.wBefore
    omega
  by_cases hp : geometricPay (z.config e) (z.config (rightNeighbor e))=true
  · by_cases hj : e=j
    · subst e
      simp only [hp,and_true,if_neg (Ne.symm jw)]
      exact .jPaid (by have := h.width; omega) (by have := h.wBefore; omega) rfl
        (by rw [h.kLift]; exact Ne.symm jk)
    · by_cases he : e=w
      · subst e
        simp only [hp,and_true,if_neg hj,if_neg wk]
        have ha : InRear r d w := ⟨b0,by have := h.wBefore; omega,h.wLift⟩
        have hb : InRear r d (rightNeighbor w) := ⟨b0+1,by have := h.wBefore; omega,
          by rw [liftedSite_succ,h.wLift]⟩
        have hm : (z.config w).mark=true := by simpa [h.wTag] using (ht w).symm
        exact .wPaid ha hb (h.nonliving mc w ha) hm hp
      · by_cases he' : e=k
        · subst e
          simp only [hp,and_true,if_neg hj,if_neg he]
          have ha : InRear r d k := ⟨d,Nat.le_refl _,h.kLift⟩
          have hm : (z.config k).mark=true := by simpa [h.kTag] using (ht k).symm
          exact .kPaid h.width h.kLift.symm (h.nonliving mc k ha) hm hp
        · simp only [hp,and_true,if_neg hj,if_neg he,if_neg he']
          exact .stationary (h.nonliving mc) (fun hR =>
            False.elim (hj (FreshSeparation.succ_inj hR)))
  · simp only [hp,Bool.false_eq_true,and_false,if_false]
    exact .stationary (h.nonliving mc) (fun hR => by
      have he : e=j := FreshSeparation.succ_inj hR
      subst e
      simpa [h.jTag] using (ht j).symm)

#print axioms tracked_landing
#print axioms classify

/-- All literal tag landings and the stock charge refer to the same
selected old edge and the same completed pair. -/
theorem tagged_charge {p c n : Nat} (hn : 4≤n)
    (z : Ledger p c n) (g : List (Fin n)) (e j w k a b cTag : Fin n)
    (b0 d : Nat) (h : Cut z j w k a b cTag b0 d)
    (mc : MCOV z.config) (ht : Covers z.config z.slots)
    (hj : a∈g) (hw : b∈g) (hk : cTag∈g)
    (hKeep : WindowLocal.selectedGroupLoss g z e=none) :
    let pay := geometricPay (z.config e) (z.config (rightNeighbor e))=true
    let j' := if e=j ∧ pay then rightNeighbor j else j
    let w' := if e=w ∧ pay then rightNeighbor w else w
    let k' := if e=k ∧ pay then rightNeighbor k else k
    let d' := if e=j ∧ pay then d-1 else if e=k ∧ pay then d+1 else d
    let credit : Nat := if e=w ∧ pay then 1 else 0
    (advance z e).slots j'=some a ∧
    (advance z e).slots w'=some b ∧
    (advance z e).slots k'=some cTag ∧
    rearInventory (advance z e).config (rightNeighbor j') d' + (credit : Int) ≤
      rearInventory z.config (rightNeighbor j) d := by
  have H := (classify hn z g e j w k a b cTag b0 d h mc ht hKeep).charge hn
  refine ⟨tracked_landing hn z g e j a ht hj h.jTag hKeep,
    tracked_landing hn z g e w b ht hw h.wTag hKeep,
    tracked_landing hn z g e k cTag ht hk h.kTag hKeep,?_⟩
  by_cases he : e=j ∧ geometricPay (z.config e) (z.config (rightNeighbor e))=true
  · simpa only [if_pos he,SevenTagCharge.advance] using H
  · simpa only [if_neg he,SevenTagCharge.advance] using H

#print axioms tagged_charge

/-- Physical old-edge displacement flag for a named slot. -/
def moves {p c n : Nat} (z : Ledger p c n) (e s : Fin n) : Prop :=
  e=s ∧ geometricPay (z.config e) (z.config (rightNeighbor e))=true

instance {p c n : Nat} (z : Ledger p c n) (e s : Fin n) : Decidable (moves z e s) := by
  unfold moves
  infer_instance

def landing {p c n : Nat} (z : Ledger p c n) (e s : Fin n) : Fin n :=
  if moves z e s then rightNeighbor s else s

def widthAfter {p c n : Nat} (z : Ledger p c n) (e j k : Fin n) (d : Nat) : Nat :=
  if moves z e j then d-1 else if moves z e k then d+1 else d

/-- This observer always advances the actual ledger. A witness is needed
only that the designated premark shadow is still a ghost cut. The
post-ledger tags and inventory coordinates are computed, never chosen. -/
inductive GhostTrace {p c n : Nat} (g : List (Fin n)) (a b cTag : Fin n) :
    Ledger p c n → Fin n → Fin n → Fin n → Nat → List (Fin n) → Nat → Prop where
  | nil {z j w k d} : GhostTrace g a b cTag z j w k d [] 0
  | cons {z j w k d e tape tally} :
      (∃ b0, Cut z j w k a b cTag b0 d) →
      MCOV z.config → Covers z.config z.slots →
      WindowLocal.selectedGroupLoss g z e = none →
      GhostTrace g a b cTag (advance z e) (landing z e j) (landing z e w)
        (landing z e k) (widthAfter z e j k d) tape tally →
      GhostTrace g a b cTag z j w k d (e::tape) ((if moves z e w then 1 else 0)+tally)

theorem GhostTrace.stock_bound {p c n : Nat} (hn : 4≤n)
    {g : List (Fin n)} {a b cTag j w k : Fin n} {d : Nat} {z : Ledger p c n}
    {tape : List (Fin n)} {tally : Nat} (h : GhostTrace g a b cTag z j w k d tape tally) :
    (tally : Int) ≤ rearInventory z.config (rightNeighbor j) d := by
  induction h with
  | nil => exact (rearInventory_interval _ _ _).1
  | @cons z j w k d e tape tally hcut mc cov hk hw ih =>
    obtain ⟨b0,hs⟩ := hcut
    have H := (classify hn z g e j w k a b cTag b0 d hs mc cov hk).charge hn
    have hStep :
        rearInventory (advance z e).config (rightNeighbor (landing z e j))
          (widthAfter z e j k d) + ((if moves z e w then 1 else 0 : Nat) : Int) ≤
          rearInventory z.config (rightNeighbor j) d := by
      unfold landing widthAfter
      by_cases he : moves z e j
      · rw [if_pos he, if_pos he]
        have he' : e=j ∧ geometricPay (z.config e) (z.config (rightNeighbor e))=true := he
        simpa only [if_pos he',moves,SevenTagCharge.advance] using H
      · rw [if_neg he, if_neg he]
        have he' : ¬(e=j ∧ geometricPay (z.config e) (z.config (rightNeighbor e))=true) := he
        simpa only [if_neg he',moves,SevenTagCharge.advance] using H
    omega

theorem GhostTrace.count_le_size {p c n : Nat} (hn : 4≤n)
    {g : List (Fin n)} {a b cTag j w k : Fin n} {d : Nat} {z : Ledger p c n}
    {tape : List (Fin n)} {tally : Nat} (h : GhostTrace g a b cTag z j w k d tape tally) :
    tally ≤ d+1 := by
  have h1 := h.stock_bound hn
  have h2 := interval_size_cap z.config (rightNeighbor j) d
  omega

#print axioms GhostTrace.count_le_size
end L4.WindowFourHeadTrace
