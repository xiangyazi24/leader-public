import Leader.L4.WindowA0PausedDAG
import Leader.L4.WindowA0StockCap
import Leader.L4.WindowScopedSupplier

/-! The closed two-ghost stock cut is not the emitting supplier cut.
These bridge lemmas use a shared fixed predecessor base and track an
extra resident separately from conserved original stock. -/
namespace L4.WindowA0Entry
open WindowA0StockDrain

/-- An identity/conservative first cut cannot satisfy the source-injection
field on a genuine vacant source activation. -/
theorem no_direct_realStep {width : Nat} {stock : Nat → Bool} {R R' : Nat → Nat}
    (vacant : stock 1=false) (closed : R' 1=R 1) :
    ¬FIFOCompare.RealStep width 0 stock R R' := by
  intro h
  have hz := h.source rfl vacant
  omega

def origin {n : Nat} (b : Fin n) : Fin n := RearTrace.predecessor b

theorem lift_origin_succ {n : Nat} (b : Fin n) (j : Nat) :
    liftedSite (origin b) (j+1)=liftedSite b j := by
  have H : liftedSite (origin b) 1=b := by
    rw [show (1:Nat)=0+1 by rfl,liftedSite_succ,liftedSite_zero]
    exact RearTrace.right_predecessor b
  rw [show j+1=1+j by omega,←RestartGeometry.lift_add,H]

theorem incoming_origin {n : Nat} (b : Fin n) (j : Nat) :
    GGStage.incoming b j=liftedSite (origin b) j := by
  apply FreshSeparation.succ_inj
  rw [GGStage.incoming_right,←liftedSite_succ,lift_origin_succ]

def coordinates {p c n : Nat} (z : Cursor p c n) (extra : Bool) (spent : Nat) :
    WindowA0MaskedTrace.Cursor := ⟨z.heads.i+1,z.heads.j+1,extra,spent⟩

theorem payment_exact {p c n : Nat} (x : Config p c n) (b e : Fin n) (j : Nat) :
    WindowA0MaskedTrace.paymentAt x (origin b) e (j+1)=GGStage.moved x b e j := by
  simp [WindowA0MaskedTrace.paymentAt,GGStage.moved,incoming_origin]

/-- Both masked head coordinates are the actual shifted absolute heads.
The masked residue flag and spend count evolve on the old pair. -/
theorem coordinates_keep {p c n : Nat} (g : List (Fin n)) (a b base e : Fin n)
    (z : Cursor p c n) (extra : Bool) (spent : Nat) (h : z.exit=none)
    (he : WindowA0Route.routeTwo g a b z.ledger e=.keep) :
    let q := WindowA0MaskedTrace.tick z.ledger.config (origin base) e (coordinates z extra spent)
    q=coordinates (next g a b base z e) q.extra q.spent := by
  have H := (exact_keep g a b base z e h he).1
  unfold coordinates WindowA0MaskedTrace.tick
  dsimp only
  rw [H, payment_exact, payment_exact]
  congr 1 <;> dsimp only <;> omega

/-- Build the physical row interface from an actual tagged relative cut
and the fixed bound on the absolute ghost-door displacement. -/
theorem good_of_cut {p c n : Nat} {x : Config p c n}
    (a b k base : Fin n) (z : Cursor p c n) (width : Nat)
    (extra : Bool) (spent : Nat) (hv : Continuing x a b k base z)
    (hI : z.heads.i<z.heads.j) (hK : z.heads.j<z.heads.k)
    (hWidth : width<n) (hfit : z.heads.j+1≤width)
    (hExtra : extra=true → (z.ledger.config (GGStage.incoming base z.heads.j)).stock=true)
    (hC : let w := WindowA0StockCap.rebase base z
          WindowFourHeadTrace.Cut w.ledger w.j w.w w.k a b k w.index w.width) :
    WindowA0MaskedTrace.Good z.ledger.config (origin base) width (coordinates z extra spent) := by
  let i := z.heads.i
  let j := z.heads.j
  let l := z.heads.k
  have hM (d : Nat) (tag : Fin n) (hT : z.ledger.slots (GGStage.incoming base d)=some tag) :
      (z.ledger.config (liftedSite (origin base) d)).mark=true := by
    have H := (hv.1.covers (GGStage.incoming base d)).symm
    rw [hT, incoming_origin] at H
    exact H
  refine ⟨hWidth,by simp [coordinates], by simpa [coordinates] using hI,hfit,?_,?_,?_,?_,?_,?_⟩
  · simpa only [coordinates,Nat.add_sub_cancel] using hM _ _ hv.2.1
  · simpa only [coordinates,Nat.add_sub_cancel] using hM _ _ hv.2.2.1
  · rw [show (coordinates z extra spent).J=j+1 by rfl,lift_origin_succ]
    exact hv.2.2.2.2.2
  · intro d hd hd'
    have hd0 : i+1≤d := hd
    have hd1 : d<j := by change d+1<j+1 at hd'; omega
    have he : liftedSite (origin base) d=liftedSite (rightNeighbor (GGStage.incoming base i)) (d-i-1) := by
      rw [GGStage.incoming_right,RestartGeometry.lift_add]
      exact (congrArg (liftedSite (origin base)) (show d=i+(d-i-1)+1 by omega)).trans (lift_origin_succ _ _)
    rw [he]
    have hi' : z.heads.i<z.heads.j := hI
    have hk' : z.heads.j<z.heads.k := hK
    exact hC.noOther (d-i-1) (by dsimp [WindowA0StockCap.rebase]; change i<j at hi'; change j<l at hk'; omega)
      (by dsimp [WindowA0StockCap.rebase]; change i<j at hi'; omega)
  · intro d hd hd'
    have hd0 : i+1≤d := hd
    have hd1 : d<j+1 := hd'
    have he : liftedSite (origin base) d=liftedSite (rightNeighbor (GGStage.incoming base i)) (d-i-1) := by
      rw [GGStage.incoming_right,RestartGeometry.lift_add]
      exact (congrArg (liftedSite (origin base)) (show d=i+(d-i-1)+1 by omega)).trans (lift_origin_succ _ _)
    have hk' : j<l := hK
    apply hC.nonliving hv.1.markCover
    exact ⟨d-i-1,by dsimp [WindowA0StockCap.rebase]; omega,he.symm⟩
  · intro hx
    rw [show (coordinates z extra spent).J-1=j by simp [coordinates,j],←incoming_origin]
    exact hExtra hx

open SevenTagCharge

structure Framed {p c n : Nat} (initial : Config p c n)
    (a b k base : Fin n) (z : Cursor p c n) : Prop where
  cont : Continuing initial a b k base z
  ij : z.heads.i<z.heads.j
  jk : z.heads.j<z.heads.k
  cut : let q := WindowA0StockCap.rebase base z
        WindowFourHeadTrace.Cut q.ledger q.j q.w q.k a b k q.index q.width

theorem framed_keep {p c n : Nat} {initial : Config p c n} (hn : 4≤n)
    (g : List (Fin n)) (a b k base : Fin n) (z : Cursor p c n) (e : Fin n)
    (ha : a∈g) (hb : b∈g) (hk : k∈g) (hz : z.exit=none)
    (he : WindowA0Route.routeTwo g a b z.ledger e=.keep)
    (old : Framed initial a b k base z) :
    Framed initial a b k base (next g a b base z e) := by
  let q := WindowA0StockCap.rebase base z
  let t := next g a b base z e
  have hSpan : z.heads.k<z.heads.i+n := by
    have h := old.cut.width
    have hi := old.ij
    have hj := old.jk
    change z.heads.k-z.heads.i-1+1<n at h
    omega
  obtain ⟨hr,hi,hj⟩ := WindowA0StockCap.rebase_keep hn g a b k base z e ha hb hk hz he
    old.cont old.ij old.jk hSpan
  have cont := continuing_keep hn g a b k base z e old.cont ha hb hk hz he
  let u := WindowFourHeadCut.tick q e
  have E : WindowA0StockCap.rebase base t=u := hr
  have hJ : (u.ledger.config (rightNeighbor u.j)).leader=false := by
    rw [← E]
    simpa [WindowA0StockCap.rebase,GGStage.incoming_right] using cont.2.2.2.2.1
  have hW : (u.ledger.config (rightNeighbor u.w)).leader=false := by
    rw [← E]
    simpa [WindowA0StockCap.rebase,GGStage.incoming_right] using cont.2.2.2.2.2
  refine ⟨cont,hi,hj,?_⟩
  change WindowFourHeadTrace.Cut (WindowA0StockCap.rebase base t).ledger
    (WindowA0StockCap.rebase base t).j (WindowA0StockCap.rebase base t).w
    (WindowA0StockCap.rebase base t).k a b k
    (WindowA0StockCap.rebase base t).index (WindowA0StockCap.rebase base t).width
  rw [E]
  exact WindowFourHeadCut.cut_step hn q.ledger g e q.j q.w q.k a b k q.index q.width old.cut
    old.cont.1.markCover old.cont.1.covers ha hb hk
    (WindowA0Route.empty_group_loss_of_two_keep z.ledger g a b e he) hJ hW

theorem actual_order {p c n : Nat} {initial : Config p c n} (hn : 4≤n)
    (g : List (Fin n)) (a b k base : Fin n) (z : Cursor p c n) (e : Fin n)
    (extra : Bool) (spent : Nat) (ha : a∈g) (hb : b∈g) (hk : k∈g) (hz : z.exit=none)
    (he : WindowA0Route.routeTwo g a b z.ledger e=.keep)
    (old : Framed initial a b k base z) :
    let q := WindowA0MaskedTrace.tick z.ledger.config (origin base) e (coordinates z extra spent)
    q.I<q.J := by
  dsimp only
  rw [coordinates_keep g a b base e z extra spent hz he]
  change (next g a b base z e).heads.i+1<(next g a b base z e).heads.j+1
  exact Nat.succ_lt_succ (framed_keep hn g a b k base z e ha hb hk hz he old).ij

theorem paid_le_of_noexit {p c n : Nat} {initial : Config p c n} (hn : 4≤n)
    (g : List (Fin n)) (a b k base : Fin n) (z : Cursor p c n)
    (ha : a∈g) (hb : b∈g) (hk : k∈g) (h : Framed initial a b k base z)
    (w : List (Fin n)) (he : (tape g a b base z w).exit=none) :
    (tape g a b base z w).heads.j-z.heads.j≤z.heads.k-z.heads.i := by
  obtain ⟨H,W⟩ := WindowA0StockCap.actual_ghost_trace hn g a b k base ha hb hk
    z w h.cont h.ij h.jk h.cut he
  rw [W]
  have B := WindowFourHeadCut.retained_ghost_progress_cap hn g a b k ha hb hk
    initial (WindowA0StockCap.rebase base z) w H h.cont.1 h.cut
  change WindowFourHeadCut.totalW (WindowA0StockCap.rebase base z) w ≤ z.heads.k-z.heads.i-1+1 at B
  have hi := h.ij
  have hj := h.jk
  omega

open WindowA0MaskedTrace WindowA0PausedDAG FIFOCompare in
structure Observer (p c n : Nat) where
  real : WindowA0StockDrain.Cursor p c n
  extra : Bool
  spent : Nat

open WindowA0MaskedTrace WindowA0PausedDAG FIFOCompare in
def clockNext {p c n : Nat} (g : List (Fin n)) (a b base : Fin n)
    (z : Observer p c n) (e : Fin n) : Observer p c n :=
  let y := WindowA0StockDrain.next g a b base z.real e
  let q := tick z.real.ledger.config (origin base) e (coordinates z.real z.extra z.spent)
  ⟨y,q.extra,q.spent⟩

open WindowA0MaskedTrace WindowA0PausedDAG FIFOCompare in
def cutsAt {p c n : Nat} (base : Fin n) (m : Nat) (z : Observer p c n) (i : Nat) : Nat :=
  let q := coordinates z.real z.extra z.spent
  cuts (m+1) (WindowA0Masked.stock z.real.ledger.config (origin base) q.I q.J q.extra) q.spent (i+1)

def height {p c n : Nat} (base : Fin n) (m P : Nat) (z : Observer p c n) (i : Nat) : Nat :=
  if z.real.exit.isSome then P else cutsAt base m z i

structure Setup {p c n : Nat} (initial : Config p c n) (g : List (Fin n))
    (a b k base : Fin n) (m : Nat) (z₀ : Cursor p c n) where
  hn : 4≤n
  width : m+1<n
  left_mem : a∈g
  middle_mem : b∈g
  right_mem : k∈g
  fit : ∀ w, (tape g a b base z₀ w).exit=none →
    (tape g a b base z₀ w).heads.j+1≤m+1

def TraceGood {p c n : Nat} (initial : Config p c n) (g : List (Fin n))
    (a b k base : Fin n) (m P : Nat) (z₀ : Cursor p c n) (z : Observer p c n) : Prop :=
  (∃ w, z.real=tape g a b base z₀ w) ∧
    (z.real.exit.isSome=true ∨
      Framed initial a b k base z.real ∧
      (z.extra=true → pending base z.real) ∧ cutsAt base m z 0=P)

variable {p c n m P : Nat} {initial : Config p c n} {g : List (Fin n)}
  {a b k base : Fin n} {z₀ : Cursor p c n}

private theorem terminal_stays (z : Observer p c n) (e : Fin n) (h : z.real.exit.isSome=true) :
    (clockNext g a b base z e).real.exit.isSome=true := by
  change (WindowA0StockDrain.next g a b base z.real e).exit.isSome=true
  simp [WindowA0StockDrain.next,h]

private theorem noexit_forces_keep (z : Observer p c n) (e : Fin n)
    (h : (clockNext g a b base z e).real.exit=none) :
    z.real.exit=none ∧ WindowA0Route.routeTwo g a b z.real.ledger e=.keep := by
  change (WindowA0StockDrain.next g a b base z.real e).exit=none at h
  cases he : z.real.exit with
  | some r => simp [WindowA0StockDrain.next,he] at h
  | none =>
    refine ⟨rfl,?_⟩
    by_cases hR : WindowA0Route.routeTwo g a b z.real.ledger e=.keep
    · exact hR
    · simp [WindowA0StockDrain.next,he,hR] at h

open WindowA0MaskedTrace in
theorem masked_good (S : Setup initial g a b k base m z₀) (z : Observer p c n)
    (h : TraceGood initial g a b k base m P z₀ z) (he : z.real.exit=none) :
    Good z.real.ledger.config (origin base) (m+1) (coordinates z.real z.extra z.spent) := by
  obtain ⟨w,hw⟩ := h.1
  have H := h.2.resolve_left (by simp [he])
  have H' : z.real.heads.j+1≤m+1 := by
    rw [hw]
    exact S.fit w (hw ▸ he)
  exact good_of_cut _ _ _ _ _ _ _ _ H.1.cont H.1.ij H.1.jk S.width H' H.2.1 H.1.cut

private theorem cut_bound (z : Observer p c n)
    (h : cutsAt base m z 0=P) (i : Nat) : cutsAt base m z i≤P := by
  induction i with
  | zero => exact Nat.le_of_eq h
  | succ i ih =>
    have H := FIFOCompare.cuts_adjacent_all (m+1)
      (WindowA0Masked.stock z.real.ledger.config (origin base)
        (coordinates z.real z.extra z.spent).I (coordinates z.real z.extra z.spent).J z.extra)
      z.spent (i+1)
    change cutsAt base m z i = _+cutsAt base m z (i+1) at H
    omega

theorem mask_next (z : Observer p c n) (e : Fin n)
    (h : (clockNext g a b base z e).real.exit=none) :
    let q := coordinates z.real z.extra z.spent
    let q' := WindowA0MaskedTrace.tick z.real.ledger.config (origin base) e q
    coordinates (clockNext g a b base z e).real (clockNext g a b base z e).extra
      (clockNext g a b base z e).spent = q' := by
  obtain ⟨ho,hr⟩ := noexit_forces_keep z e h
  exact (coordinates_keep g a b base e z.real z.extra z.spent ho hr).symm

theorem mask_config (z : Observer p c n) (e : Fin n) :
    (clockNext g a b base z e).real.ledger.config=step z.real.ledger.config e := by
  exact congrArg Ledger.config (projection g a b base z.real e)

open WindowA0MaskedTrace FIFOCompare in
theorem cut_step_literal (S : Setup initial g a b k base m z₀)
    (z : Observer p c n) (e : Fin n)
    (h : TraceGood initial g a b k base m P z₀ z)
    (hN : (clockNext g a b base z e).real.exit=none) :
    let y := clockNext g a b base z e
    Framed initial a b k base y.real ∧
      (y.extra=true → pending base y.real) ∧
      cutsAt base m z 0=cutsAt base m y 0 ∧
      ∀ i, cutsAt base m z i≤cutsAt base m y i := by
  let y := clockNext g a b base z e
  obtain ⟨he,hr⟩ := noexit_forces_keep z e hN
  have old := (h.2.resolve_left (by simp [he])).1
  let q := coordinates z.real z.extra z.spent
  let t := tick z.real.ledger.config (origin base) e q
  have T : coordinates y.real y.extra y.spent=tick z.real.ledger.config (origin base) e q := mask_next z e hN
  have Q := masked_good S z h he
  have hOrd : t.I<t.J := actual_order S.hn g a b k base z.real e z.extra z.spent
    S.left_mem S.middle_mem S.right_mem he hr old
  refine ⟨framed_keep S.hn g a b k base z.real e S.left_mem S.middle_mem S.right_mem he hr old,?_,?_⟩
  · intro hX
    have F := extra_persists S.hn z.real.ledger.config (origin base) e (m+1) q Q
    have E : t.extra=true := hX
    have TT := F E
    rw [←mask_config (g:=g) (a:=a) (b:=b) (base:=base) z e,←T] at TT
    change (y.real.ledger.config (liftedSite (origin base) (y.real.heads.j+1-1))).stock=true at TT
    change (y.real.ledger.config (GGStage.incoming base y.real.heads.j)).stock=true
    simpa only [Nat.add_sub_cancel,←incoming_origin] using TT
  · have F := physical_heights S.hn z.real.ledger.config (origin base) e (m+1) q
      Q old.cont.1.markCover hOrd
    dsimp only at F
    rw [←mask_config (g:=g) (a:=a) (b:=b) (base:=base) z e,←T] at F
    exact ⟨F.1,fun i => F.2 (i+1)⟩

theorem traceGood_keep (S : Setup initial g a b k base m z₀) (z : Observer p c n)
    (e : Fin n) (h : TraceGood initial g a b k base m P z₀ z) :
    TraceGood initial g a b k base m P z₀ (clockNext g a b base z e) := by
  obtain ⟨w,hw⟩ := h.1
  refine ⟨⟨w++[e],?_⟩,?_⟩
  · change WindowA0StockDrain.next g a b base z.real e=tape g a b base z₀ (w++[e])
    rw [hw]
    exact (tape_append g a b base z₀ w e).symm
  · cases he : (clockNext g a b base z e).real.exit with
    | some r => exact .inl (by simp)
    | none =>
      have H := cut_step_literal S z e h he
      have ho := (noexit_forces_keep z e he).1
      exact .inr ⟨H.1,H.2.1,H.2.2.1.symm.trans (h.2.resolve_left (by simp [ho])).2.2⟩

open WindowA0PausedDAG WindowA0MaskedTrace FIFOCompare in
theorem gatedRules (S : Setup initial g a b k base m z₀) :
    GatedRules (clockNext g a b base) (TraceGood initial g a b k base m P z₀)
      (fun z => canServe base z.real) (height base m P) m P (liftedSite (origin base)) := by
  constructor
  · intro z e i hz _
    cases hE : (clockNext g a b base z e).real.exit with
    | some r =>
      simp only [height,hE,Option.isSome_some,if_true]
      split
      · exact Nat.le_refl _
      · rename_i hh
        exact cut_bound z ((hz.2.resolve_left hh).2.2) i
    | none =>
      have hO := (noexit_forces_keep z e hE).1
      simp only [height,hE,hO,Option.isSome_none,Bool.false_eq_true,if_false]
      exact (cut_step_literal S z e hz hE).2.2.2 i
  · intro z i v hz he hi hv hp hl hr
    let e := liftedSite (origin base) i
    let y := clockNext g a b base z e
    cases hE : y.real.exit with
    | some r =>
      change v≤height base m P y i
      simp only [height,hE,Option.isSome_some,if_true]
      exact hp
    | none =>
      have hO := (noexit_forces_keep z e hE).1
      have H := hz.2.resolve_left (by simp [hO])
      let q := coordinates z.real z.extra z.spent
      let t := tick z.real.ledger.config (origin base) e q
      have E : coordinates y.real y.extra y.spent=tick z.real.ledger.config (origin base) e q := mask_next z e hE
      have hO' : WindowA0Route.routeTwo g a b z.real.ledger e=.keep :=
        (noexit_forces_keep z e hE).2
      have ord : t.I<t.J := actual_order S.hn g a b k base z.real e z.extra z.spent
        S.left_mem S.middle_mem S.right_mem hO hO' H.1
      have pause : (z.real.ledger.config (liftedSite (origin base) (q.J-1))).stock=false := by
        change (z.real.ledger.config (liftedSite (origin base) (z.real.heads.j+1-1))).stock=false
        simpa [canServe,Nat.add_sub_cancel,incoming_origin] using he
      have source : P≤cutsAt base m z 0 := Nat.le_of_eq H.2.2.symm
      have left (h : 0<i) : v≤cutsAt base m z (i-1) := by
        simpa [height,hO] using hl h
      have right (h : i<m) : v-1≤cutsAt base m z (i+1) := by
        simpa [height,hO] using hr h
      have F := unpaused_commit S.hn z.real.ledger.config (origin base) m P i v q
        (masked_good S z hz hO) H.1.cont.1.markCover pause hi hv hp source left right ord
      change v≤height base m P y i
      simp only [height,hE,Option.isSome_none,Bool.false_eq_true,if_false]
      dsimp only at F
      rw [←mask_config (g:=g) (a:=a) (b:=b) (base:=base) z e,←E] at F
      exact F

open WindowA0PausedDAG WindowA0MaskedTrace FIFOCompare in
theorem discharge (S : Setup initial g a b k base m z₀) (z : Observer p c n)
    (h : TraceGood initial g a b k base m P z₀ z)
    (hp : ¬pending base z.real) (hout : P≤height base m P z m) :
    drained base z.real := by
  cases he : z.real.exit with
  | some r => exact .inl (by simp [he])
  | none =>
    have HH := h.2.resolve_left (by simp [he])
    have H := masked_good S z h he
    let q := coordinates z.real z.extra z.spent
    have pause : (z.real.ledger.config (liftedSite (origin base) (q.J-1))).stock=false := by
      apply Bool.eq_false_iff.mpr
      intro hh
      apply hp
      change (z.real.ledger.config (GGStage.incoming base z.real.heads.j)).stock=true
      simpa only [q,coordinates,Nat.add_sub_cancel,←incoming_origin] using hh
    have out : P≤cutsAt base m z m := by simpa [height,he] using hout
    have H' := drained_of_outlet z.real.ledger.config (origin base) m P q H pause HH.2.2 out
    exact .inr ⟨hp,fun j hj hJ => by
      have hh := H' (j+1) (Nat.succ_le_succ hj) (Nat.succ_lt_succ hJ)
      rwa [lift_origin_succ] at hh⟩

open FIFOCompare in
private theorem stock_count (width end_ : Nat) (stock : Nat → Bool)
    (h : ∀ i, end_≤i → stock i=false) (start : Nat) :
    tailSlots width stock start≤end_-start := by
  rw [tailSlots.eq_1]
  by_cases H : start<width
  · rw [if_pos H]
    have ih := stock_count width end_ stock h (start+1)
    by_cases he : end_≤start
    · rw [h start he]
      simp only [Bool.toNat_false,Nat.zero_add]
      omega
    · have B : (stock start).toNat≤1 := by cases stock start <;> decide
      omega
  · rw [if_neg H]
    exact Nat.zero_le _
termination_by width-start
decreasing_by omega

open WindowA0PausedDAG WindowA0MaskedTrace FIFOCompare WindowSpan in
/-- Concrete first stock-cut mean for the seven-tag A0 entry. The
analytical clock is paused by the old stocked J slot; the actual
ring and the original-byte counters always process every raw letter. -/
theorem entry_drain (hn : 4≤n) (x : Config p c n)
    (i : Fin (RankPhysical.rank x)) (hm : MCOV x) (hc : COV x) (short : 2*span x i+2<n)
    (h1 : (x (rootSite x (liftedSite i 1))).leader=false)
    (h2 : (x (rootSite x (liftedSite i 2))).leader=false) :
    let g := window7 (WindowRoster.roster x) i
    let tag := fun j : Nat => WindowRoster.roster x (liftedSite i j)
    let z := entryCursor x i
    let base := entryBase x i
    IIDExpectedHittingTimeAtMost RootedAssembly.wordNext
      (fun w => drained base (tape g (tag 1) (tag 2) base z w)) [] (17*n*(span x i+1)) := by
  dsimp only
  let g := window7 (WindowRoster.roster x) i
  let tag := fun j : Nat => WindowRoster.roster x (liftedSite i j)
  let z := entryCursor x i
  let base := entryBase x i
  let u := z.heads.k-z.heads.i
  let m := 2*u
  let seed : Observer p c n := ⟨z,false,0⟩
  let P := cutsAt base m seed 0
  obtain ⟨C,ha,hb,hk,hu⟩ := entry_continuing x i hm hc short h1 h2
  have A := WindowA0.a0_initialCut x i hm hc short h1 h2
  have hA : GGStage.AmbientConsecutive z.ledger.config base z.heads := A.2.2.2.1
  have F : Framed x (tag 1) (tag 2) (tag 3) base z :=
    ⟨C,hA.1,hA.2.1,WindowA0StockCap.cut_of_ambient _ _ _ _ _ C hA⟩
  have hz0 : z.heads.i=0 := rfl
  have hJ0 : z.heads.j≤u := by
    have h := F.jk
    unfold u
    omega
  have S : Setup x g (tag 1) (tag 2) (tag 3) base m z := by
    refine ⟨hn,?_,ha,hb,hk,?_⟩
    · change m+1<n
      have hU : u≤span x i := hu
      unfold m
      omega
    · intro w he
      have hh := paid_le_of_noexit hn g (tag 1) (tag 2) (tag 3) base z ha hb hk F w he
      change (tape g (tag 1) (tag 2) base z w).heads.j-z.heads.j≤u at hh
      unfold m
      omega
  have HP : P≤u := by
    let s := WindowA0Masked.stock z.ledger.config (origin base) (z.heads.i+1) (z.heads.j+1) false
    have hS (j : Nat) (h : z.heads.j+1≤j) : s j=false := by
      simp [s,WindowA0Masked.stock,show ¬j<z.heads.j+1 by omega]
    change 0+tailSlots (m+1) s 1≤u
    have H := stock_count (m+1) (z.heads.j+1) s hS 1
    omega
  have hg : TraceGood x g (tag 1) (tag 2) (tag 3) base m P z seed :=
    ⟨⟨[],rfl⟩,.inr ⟨F,by intro h; contradiction,rfl⟩⟩
  exact entry_drain_of_gated_rows hn x i hm hc short h1 h2 m P (liftedSite (origin base))
    (clockNext g (tag 1) (tag 2) base) Observer.real seed
    (TraceGood x g (tag 1) (tag 2) (tag 3) base m P z) (height base m P) HP (Nat.le_refl _)
    rfl (fun _ _ => rfl) (gatedRules S) (traceGood_keep S) hg (discharge S)

end L4.WindowA0Entry
