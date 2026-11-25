import Leader.L4.WindowA0StockDrain
import Leader.L4.WindowFourHeadCut
import Leader.L4.RestartGeometry

namespace L4.WindowA0StockCap
open SevenTagCharge WindowA0StockDrain WindowFourHeadTrace WindowFourHeadCut

private theorem incomingSucc {n : Nat} (base : Fin n) (i : Nat) :
    GGStage.incoming base (i+1)=rightNeighbor (GGStage.incoming base i) := by
  apply FreshSeparation.succ_inj
  rw [GGStage.incoming_right,liftedSite_succ,GGStage.incoming_right]

private theorem liftIncoming {n : Nat} (base : Fin n) (i l : Nat) :
    liftedSite (liftedSite base i) l=GGStage.incoming base (i+l+1) := by
  apply FreshSeparation.succ_inj
  rw [GGStage.incoming_right,←liftedSite_succ,RestartGeometry.lift_add,Nat.add_assoc]

private theorem movedFlag {p c n : Nat} (z : Ledger p c n) (base e : Fin n) (i : Nat) :
    GGStage.moved z.config base e i =
      decide (moves z e (GGStage.incoming base i)) := by
  unfold GGStage.moved
  unfold moves
  by_cases he : e=GGStage.incoming base i
  · simp [he]
  · have hbeq : (e == GGStage.incoming base i)=false :=
      Bool.eq_false_iff.mpr (fun h => he (beq_iff_eq.mp h))
    simp [he,hbeq]

private theorem landing_incoming {p c n : Nat} (z : Ledger p c n) (base e : Fin n) (i : Nat) :
    landing z e (GGStage.incoming base i) =
      GGStage.incoming base (i+(GGStage.moved z.config base e i).toNat) := by
  unfold landing
  rw [movedFlag]
  split
  · rename_i h
    simp [h,incomingSucc]
  · rename_i h
    simp [h]

/-- Rebase the absolute A0 cursor into the exact moving stock cut. -/
def rebase {p c n : Nat} (base : Fin n) (z : WindowA0StockDrain.Cursor p c n) :
    WindowFourHeadCut.Cursor p c n :=
  ⟨z.ledger,GGStage.incoming base z.heads.i,GGStage.incoming base z.heads.j,
    GGStage.incoming base z.heads.k,z.heads.j-z.heads.i-1,z.heads.k-z.heads.i-1⟩

private theorem ordered_slots {n : Nat} {base : Fin n}
    {i j : Nat} (hi : i<j) (hij : j<i+n) :
    GGStage.incoming base i≠GGStage.incoming base j := by
  intro he
  have H := congrArg rightNeighbor he
  rw [GGStage.incoming_right,GGStage.incoming_right,
    show j=i+(j-i) by omega,← RestartGeometry.lift_add] at H
  have h := liftedSite_inj (liftedSite base i) (show 0<n by omega)
    (show j-i<n by omega) ((liftedSite_zero _).trans H)
  omega

theorem cut_of_ambient {p c n : Nat} {x : Config p c n} (a b k base : Fin n)
    (z : WindowA0StockDrain.Cursor p c n)
    (hz : Continuing x a b k base z) (h : GGStage.AmbientConsecutive z.ledger.config base z.heads) :
    let q := rebase base z
    Cut q.ledger q.j q.w q.k a b k q.index q.width := by
  obtain ⟨ij,jk,kn,_,_,_,h1,h2⟩ := h
  let i := z.heads.i
  let j := z.heads.j
  let l := z.heads.k
  change i<j at ij
  change j<l at jk
  change l<i+n at kn
  refine ⟨hz.2.1,hz.2.2.1,hz.2.2.2.1,?_,?_,by dsimp [rebase]; omega,
    by dsimp [rebase]; omega,?_,?_,?_⟩
  · change liftedSite (rightNeighbor (GGStage.incoming base i)) (j-i-1)=GGStage.incoming base j
    rw [GGStage.incoming_right,liftIncoming,show i+(j-i-1)+1=j by omega]
  · change liftedSite (rightNeighbor (GGStage.incoming base i)) (l-i-1)=GGStage.incoming base l
    rw [GGStage.incoming_right,liftIncoming,show i+(l-i-1)+1=l by omega]
  · simpa [rebase,GGStage.incoming_right] using hz.2.2.2.2.1
  · simpa [rebase,GGStage.incoming_right] using hz.2.2.2.2.2
  · intro t ht hne
    change t<l-i-1 at ht
    change t≠j-i-1 at hne
    change (z.ledger.config (liftedSite (rightNeighbor (GGStage.incoming base i)) t)).mark=false
    rw [GGStage.incoming_right,liftIncoming]
    apply Bool.eq_false_iff.mpr
    intro hm
    have lx : i+t+1≠j := by omega
    by_cases hh : i+t+1<j
    · exact h1 _ (by omega) hh hm
    · exact h2 _ (by omega) (by omega) hm

private theorem noexit_prefix {p c n : Nat} (g : List (Fin n)) (a b base : Fin n)
    (z : WindowA0StockDrain.Cursor p c n) (w : List (Fin n))
    (h : (tape g a b base z w).exit=none) : z.exit=none := by
  induction w generalizing z with
  | nil => exact h
  | cons e w ih =>
    have H := ih _ h
    cases hz : z.exit with
    | none => rfl
    | some t => simp [next,hz] at H

private theorem relative_update {p c n : Nat} (z : Ledger p c n) (base e : Fin n)
    (i j : Nat) (h : i<j) (hs : GGStage.incoming base i ≠ GGStage.incoming base j)
    (hPost : i+(GGStage.moved z.config base e i).toNat <
      j+(GGStage.moved z.config base e j).toNat) :
    (j+(GGStage.moved z.config base e j).toNat) -
        (i+(GGStage.moved z.config base e i).toNat)-1 =
      (if moves z e (GGStage.incoming base i) then (j-i-1)-1
       else if moves z e (GGStage.incoming base j) then (j-i-1)+1 else j-i-1) := by
  rw [movedFlag,movedFlag]
  rw [movedFlag,movedFlag] at hPost
  by_cases hi : moves z e (GGStage.incoming base i)
  · have hj : ¬moves z e (GGStage.incoming base j) := fun hj => hs (hi.1.symm.trans hj.1)
    simp [hi,hj] at hPost ⊢
    omega
  · by_cases hj : moves z e (GGStage.incoming base j)
    · simp [hi,hj] at hPost ⊢
      omega
    · simp [hi,hj]

/-- Exact commuting square from the original A0 absolute-coordinate
cursor to the stock ledger's relative physical cursor. -/
theorem rebase_keep {p c n : Nat} {x : Config p c n} (hn : 4≤n)
    (g : List (Fin n)) (a b k base : Fin n) (z : WindowA0StockDrain.Cursor p c n) (e : Fin n)
    (ha : a∈g) (hb : b∈g) (hk : k∈g) (hz : z.exit=none)
    (hr : WindowA0Route.routeTwo g a b z.ledger e=.keep)
    (hc : Continuing x a b k base z)
    (hij : z.heads.i<z.heads.j) (hjk : z.heads.j<z.heads.k)
    (hspan : z.heads.k<z.heads.i+n) :
    let t := next g a b base z e
    rebase base t = tick (rebase base z) e ∧
    t.heads.i<t.heads.j ∧ t.heads.j<t.heads.k := by
  obtain ⟨H,_⟩ := exact_keep g a b base z e hz hr
  have ht := continuing_keep hn g a b k base z e hc ha hb hk hz hr
  let i := z.heads.i
  let j := z.heads.j
  let l := z.heads.k
  let M := fun i => i+(GGStage.moved z.ledger.config base e i).toNat
  have sij : GGStage.incoming base i≠GGStage.incoming base j :=
    ordered_slots hij (by change j<i+n; change l<i+n at hspan; change j<l at hjk; omega)
  have sjk : GGStage.incoming base j≠GGStage.incoming base l :=
    ordered_slots hjk (by change l<j+n; change l<i+n at hspan; change i<j at hij; omega)
  have sik : GGStage.incoming base i≠GGStage.incoming base l :=
    ordered_slots (Nat.lt_trans hij hjk) hspan
  have ab : a≠b := fun he => sij (hc.1.unique _ _ a hc.2.1 (he.symm ▸ hc.2.2.1))
  have bk : b≠k := fun he => sjk (hc.1.unique _ _ b hc.2.2.1 (he.symm ▸ hc.2.2.2.1))
  have hi : M i<M j := by
    have ne : M i≠M j := by
      intro he
      have hj := ht.2.2.1
      have hi := ht.2.1
      rw [H] at hi hj
      change (next g a b base z e).ledger.slots (GGStage.incoming base (M i))=some a at hi
      change (next g a b base z e).ledger.slots (GGStage.incoming base (M j))=some b at hj
      rw [he, hj] at hi
      exact ab (Option.some.inj hi).symm
    have hbd : (GGStage.moved z.ledger.config base e i).toNat≤1 := by
      cases GGStage.moved z.ledger.config base e i <;> decide
    change i<j at hij
    dsimp [M] at ne ⊢
    omega
  have hj : M j<M l := by
    have ne : M j≠M l := by
      intro he
      have hj := ht.2.2.1
      have hi := ht.2.2.2.1
      rw [H] at hi hj
      change (next g a b base z e).ledger.slots (GGStage.incoming base (M l))=some k at hi
      change (next g a b base z e).ledger.slots (GGStage.incoming base (M j))=some b at hj
      rw [he, hi] at hj
      exact bk (Option.some.inj hj).symm
    have hbd : (GGStage.moved z.ledger.config base e j).toNat≤1 := by
      cases GGStage.moved z.ledger.config base e j <;> decide
    change j<l at hjk
    dsimp [M] at ne ⊢
    omega
  refine ⟨?_,?_,?_⟩
  · unfold rebase tick
    rw [projection,H]
    congr 1
    · exact (landing_incoming z.ledger base e i).symm
    · exact (landing_incoming z.ledger base e j).symm
    · exact (landing_incoming z.ledger base e l).symm
    · exact relative_update z.ledger base e i j hij sij hi
    · exact relative_update z.ledger base e i l (Nat.lt_trans hij hjk) sik (Nat.lt_trans hi hj)
  · change (next g a b base z e).heads.i<(next g a b base z e).heads.j
    rw [H]
    exact hi
  · change (next g a b base z e).heads.j<(next g a b base z e).heads.k
    rw [H]
    exact hj

theorem actual_ghost_trace {p c n : Nat} {x : Config p c n} (hn : 4≤n)
    (g : List (Fin n)) (a b k base : Fin n) (ha : a∈g) (hb : b∈g) (hk : k∈g)
    (z : WindowA0StockDrain.Cursor p c n) (w : List (Fin n))
    (hc : Continuing x a b k base z)
    (hij : z.heads.i<z.heads.j) (hjk : z.heads.j<z.heads.k)
    (hC : let q := rebase base z; Cut q.ledger q.j q.w q.k a b k q.index q.width)
    (hE : (tape g a b base z w).exit=none) :
    GhostKeep g (rebase base z) w ∧
      (tape g a b base z w).heads.j-z.heads.j = totalW (rebase base z) w := by
  induction w generalizing z with
  | nil => exact ⟨.nil, Nat.sub_self _⟩
  | cons e w ih =>
    let t := next g a b base z e
    have ht : (tape g a b base t w).exit=none := hE
    have h0 := noexit_prefix g a b base z (e::w) hE
    have h1 := noexit_prefix g a b base t w ht
    have hr : WindowA0Route.routeTwo g a b z.ledger e=.keep := by
      by_cases hr : WindowA0Route.routeTwo g a b z.ledger e=.keep
      · exact hr
      · simp [t,next,h0,hr] at h1
    have hspan : z.heads.k<z.heads.i+n := by
      have H := hC.width
      change z.heads.k-z.heads.i-1+1<n at H
      omega
    obtain ⟨hrb,hi,hj⟩ := rebase_keep hn g a b k base z e ha hb hk h0 hr hc hij hjk hspan
    change rebase base t = tick (rebase base z) e at hrb
    have hc' := continuing_keep hn g a b k base z e hc ha hb hk h0 hr
    have loss := WindowA0Route.empty_group_loss_of_two_keep z.ledger g a b e hr
    have htJ : ((tick (rebase base z) e).ledger.config
        (rightNeighbor (tick (rebase base z) e).j)).leader=false := by
      rw [← hrb]
      simpa [rebase,GGStage.incoming_right] using hc'.2.2.2.2.1
    have htW : ((tick (rebase base z) e).ledger.config
        (rightNeighbor (tick (rebase base z) e).w)).leader=false := by
      rw [← hrb]
      simpa [rebase,GGStage.incoming_right] using hc'.2.2.2.2.2
    let q := rebase base z
    have hC' : let q := rebase base t; Cut q.ledger q.j q.w q.k a b k q.index q.width := by
      change Cut (rebase base t).ledger (rebase base t).j (rebase base t).w (rebase base t).k
        a b k (rebase base t).index (rebase base t).width
      rw [hrb]
      exact cut_step hn q.ledger g e q.j q.w q.k a b k q.index q.width hC
        hc.1.markCover hc.1.covers ha hb hk loss htJ htW
    obtain ⟨out,H⟩ := ih t hc' hi hj hC' ht
    refine ⟨.cons loss htJ htW (hrb ▸ out),?_⟩
    change (tape g a b base t w).heads.j-z.heads.j =
      wCharge (rebase base z) e + totalW (tick (rebase base z) e) w
    rw [←hrb,←H]
    have hm := j_mono_tape g a b base t w
    have hJ : t.heads.j=z.heads.j+wCharge (rebase base z) e := by
      change (next g a b base z e).heads.j=z.heads.j+wCharge (rebase base z) e
      rw [(exact_keep g a b base z e h0 hr).1]
      unfold wCharge
      dsimp only
      change z.heads.j+(GGStage.moved z.ledger.config base e z.heads.j).toNat = _
      rw [movedFlag]
      change z.heads.j+(decide (moves z.ledger e (GGStage.incoming base z.heads.j))).toNat =
        z.heads.j+(if moves z.ledger e (GGStage.incoming base z.heads.j) then 1 else 0)
      split <;> simp_all
    omega

/-- Discharges the paid cap for an arbitrary actual matching A0 cut. -/
theorem paid_cap_of_ambient {p c n : Nat} {x : Config p c n} (hn : 4≤n)
    (g : List (Fin n)) (a b k base : Fin n) (ha : a∈g) (hb : b∈g) (hk : k∈g)
    (z : WindowA0StockDrain.Cursor p c n)
    (hc : Continuing x a b k base z)
    (hA : GGStage.AmbientConsecutive z.ledger.config base z.heads)
    (w : List (Fin n)) (h : ¬drained base (tape g a b base z w)) :
    (tape g a b base z w).heads.j-z.heads.j≤z.heads.k-z.heads.i := by
  have hE : (tape g a b base z w).exit=none := by
    cases he : (tape g a b base z w).exit with
    | none => rfl
    | some v => exact (h (.inl (by simp [he]))).elim
  have hCut := cut_of_ambient a b k base z hc hA
  obtain ⟨hw,he⟩ := actual_ghost_trace hn g a b k base ha hb hk z w hc hA.1 hA.2.1 hCut hE
  rw [he]
  have H := retained_ghost_progress_cap hn g a b k ha hb hk x (rebase base z) w hw hc.1 hCut
  change totalW (rebase base z) w ≤ z.heads.k-z.heads.i-1+1 at H
  have hi := hA.1
  have hj := hA.2.1
  omega

open WindowSpan in
theorem entry_paid_cap {p c n : Nat} (hn : 4≤n) (x : Config p c n)
    (i : Fin (RankPhysical.rank x)) (hm : MCOV x) (hc : COV x)
    (short : 2*span x i+2<n)
    (h1 : (x (rootSite x (liftedSite i 1))).leader=false)
    (h2 : (x (rootSite x (liftedSite i 2))).leader=false) :
    let g := window7 (WindowRoster.roster x) i
    let tag := fun j : Nat => WindowRoster.roster x (liftedSite i j)
    let z := entryCursor x i
    let base := entryBase x i
    ∀ w, ¬drained base (tape g (tag 1) (tag 2) base z w) →
      (tape g (tag 1) (tag 2) base z w).heads.j-z.heads.j≤z.heads.k-z.heads.i := by
  obtain ⟨H,ha,hb,hk,_⟩ := entry_continuing x i hm hc short h1 h2
  have E := WindowA0.a0_initialCut x i hm hc short h1 h2
  exact paid_cap_of_ambient hn _ _ _ _ _ ha hb hk _ H E.2.2.2.1

end L4.WindowA0StockCap
