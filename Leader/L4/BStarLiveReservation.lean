import Leader.L4.BStarReceiptKey

namespace L4.BStarLiveReservation

/-- Only a read still awaiting its owner's publication is a live
reservation. Earlier values at the same numerical key from before
custody do not enter this cut state. -/
def Pending {Owner : Type} (read : Nat→Option (Owner×Bool))
    (pub : Nat→Owner→Prop) (stop : Nat) (i : Owner) (b : Bool) : Prop :=
  ∃ t, t<stop ∧ read t=some (i,b) ∧ ∀ j,t≤j → j<stop → ¬pub j i

theorem pending_positions_unique {Owner : Type} (read : Nat→Option (Owner×Bool))
    (pub : Nat→Owner→Prop) (stop : Nat) (i : Owner)
    (separate : ∀ a b p q, a<b → b<stop →
      read a=some (i,p) → read b=some (i,q) → ∃ j,a≤j ∧ j<b ∧ pub j i)
    {a b : Nat} {p q : Bool}
    (ha : a<stop) (hb : b<stop)
    (ra : read a=some (i,p)) (rb : read b=some (i,q))
    (pa : ∀ j,a≤j → j<stop → ¬pub j i)
    (pb : ∀ j,b≤j → j<stop → ¬pub j i) :
    a=b := by
  rcases Nat.lt_trichotomy a b with ab|eq|ba
  · obtain ⟨j,aj,jb,hj⟩ := separate a b p q ab hb ra rb
    exact (pa j aj (Nat.lt_trans jb hb) hj).elim
  · exact eq
  · obtain ⟨j,bj,ja,hj⟩ := separate b a q p ba ha rb ra
    exact (pb j bj (Nat.lt_trans ja ha) hj).elim

theorem pending_bits_unique {Owner : Type} (read : Nat→Option (Owner×Bool))
    (pub : Nat→Owner→Prop) (stop : Nat) (i : Owner)
    (separate : ∀ a b p q, a<b → b<stop →
      read a=some (i,p) → read b=some (i,q) → ∃ j,a≤j ∧ j<b ∧ pub j i)
    {p q : Bool} (a : Pending read pub stop i p) (b : Pending read pub stop i q) :
    p=q := by
  obtain ⟨m,hm,R,H⟩ := a
  obtain ⟨n,hn,S,K⟩ := b
  have eq := pending_positions_unique read pub stop i separate hm hn R S H K
  rw [eq] at R
  exact congrArg Prod.snd (Option.some.inj (R.symm.trans S))

noncomputable def reserved {Owner : Type} (read : Nat→Option (Owner×Bool))
    (pub : Nat→Owner→Prop) (stop : Nat) (i : Owner) : Option Bool := by
  classical
  exact if h : ∃ b,Pending read pub stop i b then some (Classical.choose h) else none

/-- The reservation is measurable in the raw past: changing either tape
after the stop does not change it. -/
theorem reserved_past {Owner : Type} (r s : Nat→Option (Owner×Bool))
    (p q : Nat→Owner→Prop) (stop : Nat) (i : Owner)
    (read : ∀ t,t<stop → r t=s t) (pub : ∀ t,t<stop → (p t i↔q t i)) :
    reserved r p stop i=reserved s q stop i := by
  have K : Pending r p stop i=Pending s q stop i := by
    funext b
    apply propext
    constructor
    · intro h
      obtain ⟨t,ht,F,N⟩ := h
      exact ⟨t,ht,(read t ht).symm.trans F,fun j tj js A=>N j tj js ((pub j js).mpr A)⟩
    · intro h
      obtain ⟨t,ht,F,N⟩ := h
      exact ⟨t,ht,(read t ht).trans F,fun j tj js A=>N j tj js ((pub j js).mp A)⟩
  unfold reserved
  rw [K]

/-- A genuinely authenticated old read that survives to a publication
after the cut equals the cut's retained bit, whenever two admitted
reads at that owner before the cut have an intervening publication. -/
theorem receipt_uses_reserved {Owner : Type} (read : Nat→Option (Owner×Bool))
    (pub : Nat→Owner→Prop) (stop : Nat) (i : Owner)
    (separate : ∀ a b p q, a<b → b<stop →
      read a=some (i,p) → read b=some (i,q) → ∃ j,a≤j ∧ j<b ∧ pub j i)
    (atRead atWrite : Nat) (b : Bool) (earlier : atRead<stop) (later : stop≤atWrite)
    (readOk : read atRead=some (i,b)) (before : ∀ j,atRead≤j → j<atWrite → ¬pub j i) :
    reserved read pub stop i=some b := by
  have P : Pending read pub stop i b :=
    ⟨atRead,earlier,readOk,fun j ro js=>before j ro (Nat.lt_of_lt_of_le js later)⟩
  have H : ∃ bit,Pending read pub stop i bit := ⟨b,P⟩
  have E := pending_bits_unique read pub stop i separate (Classical.choose_spec H) P
  unfold reserved
  rw [dif_pos H,E]

end L4.BStarLiveReservation
