import Leader.L4.WindowA0Route
import Leader.L4.WindowA0
import Leader.L4.GGPreparation
import Leader.L4.SupplierPause

/-! Physical scoped A0 stock preparation observer. The outgoing ledger
never freezes; only coordinates and first exit reason are latched. -/
namespace L4.WindowA0StockDrain
open SevenTagCharge WindowLocal WindowA0Route

structure Cursor (p c n : Nat) where
  ledger : Ledger p c n
  heads : GGStage.Heads
  exit : Option (Event n)

def next {p c n : Nat} (g : List (Fin n)) (a b base : Fin n)
    (z : Cursor p c n) (e : Fin n) : Cursor p c n :=
  let y := advance z.ledger e
  if z.exit.isSome then ⟨y,z.heads,z.exit⟩ else
    let r := routeTwo g a b z.ledger e
    if r = .keep then
      let H := z.heads
      let lift := fun d => d+(GGStage.moved z.ledger.config base e d).toNat
      ⟨y,⟨lift H.i,lift H.j,lift H.k⟩,none⟩
    else ⟨y,z.heads,some r⟩

theorem projection {p c n : Nat} (g : List (Fin n)) (a b base : Fin n)
    (z : Cursor p c n) (e : Fin n) :
    (next g a b base z e).ledger = advance z.ledger e := by
  unfold next
  split <;> try rfl
  dsimp only
  split <;> rfl

def pending {p c n : Nat} (base : Fin n) (z : Cursor p c n) : Prop :=
  (z.ledger.config (GGStage.incoming base z.heads.j)).stock=true

instance {p c n : Nat} (base : Fin n) (z : Cursor p c n) : Decidable (pending base z) :=
  inferInstanceAs (Decidable ((z.ledger.config (GGStage.incoming base z.heads.j)).stock=true))

def drained {p c n : Nat} (base : Fin n) (z : Cursor p c n) : Prop :=
  z.exit.isSome=true ∨ (¬pending base z ∧
    ∀ d, z.heads.i≤d → d<z.heads.j → (z.ledger.config (liftedSite base d)).stock=false)

def Continuing {p c n : Nat} (initial : Config p c n) (a b k base : Fin n)
    (z : Cursor p c n) : Prop :=
  Valid z.ledger initial ∧
  z.ledger.slots (GGStage.incoming base z.heads.i)=some a ∧
  z.ledger.slots (GGStage.incoming base z.heads.j)=some b ∧
  z.ledger.slots (GGStage.incoming base z.heads.k)=some k ∧
  (z.ledger.config (liftedSite base z.heads.i)).leader=false ∧
  (z.ledger.config (liftedSite base z.heads.j)).leader=false

def credit {p c n : Nat} (j₀ u : Nat) (z : Cursor p c n) : Nat :=
  if z.exit.isSome then 0 else u+1-(z.heads.j-j₀)

theorem exact_keep {p c n : Nat} (g : List (Fin n)) (a b base : Fin n)
    (z : Cursor p c n) (e : Fin n) (h : z.exit=none)
    (he : routeTwo g a b z.ledger e=.keep) :
    (next g a b base z e).heads =
      ⟨z.heads.i+(GGStage.moved z.ledger.config base e z.heads.i).toNat,
       z.heads.j+(GGStage.moved z.ledger.config base e z.heads.j).toNat,
       z.heads.k+(GGStage.moved z.ledger.config base e z.heads.k).toNat⟩ ∧
    (next g a b base z e).exit=none := by simp [next,h,he]

theorem credit_nonincrease {p c n : Nat} (g : List (Fin n)) (a b base : Fin n)
    (j₀ u : Nat) (z : Cursor p c n) (e : Fin n) :
    credit j₀ u (next g a b base z e)≤credit j₀ u z := by
  cases hz : z.exit with
  | some val => simp [credit,next,hz]
  | none =>
    by_cases he : routeTwo g a b z.ledger e=.keep
    · obtain ⟨H,E⟩ := exact_keep g a b base z e hz he
      simp only [credit,hz,E,Option.isSome_none,Bool.false_eq_true,if_false,H]
      omega
    · simp [credit,next,hz,he]

/-- Any stocked incoming bond of a named ghost pays under the native
row. This does not depend on whether that stock came from within the
window or is a newly exposed old head. -/
theorem marked_ghost_stock_pays {p c : Nat} (u v : Site p c)
    (hm : u.mark=true) (hL : v.leader=false) (hs : u.stock=true) :
    geometricPay u v=true := by
  have hm0 : materialize u v = u := by cases u; simp_all [materialize]
  have hpay : payer u=true := by simp [payer,hs]
  have ha : (fireInitiator u).mark = true ∧ payer (fireInitiator u) = true := by
    unfold fireInitiator
    split <;> exact ⟨hm,hpay⟩
  unfold geometricPay native
  rw [hm0]
  have hv : fireResponder v = v := by simp [fireResponder,hL]
  rw [hv]
  have hi (a : Site p c) : impact a v = (a,v) := by simp [impact,hL]
  rw [hi]
  generalize fireInitiator u = a at ha ⊢
  simp only [pinned,ha.1,hL,Bool.not_false,Bool.and_true]
  cases hb : !(a.bullet == .none) <;>
    simp [followerBullet,hb,ha.1,hL,payer] <;> simpa only [payer,Bool.or_eq_true] using ha.2

theorem pending_nomination {p c n : Nat} {initial : Config p c n}
    (g : List (Fin n)) (a b k base : Fin n) (j₀ u : Nat) (z : Cursor p c n)
    (hc : Continuing initial a b k base z) (hz : z.exit=none)
    (h₀ : j₀≤z.heads.j) (hcap : z.heads.j-j₀≤u)
    (hp : pending base z) :
    credit j₀ u (next g a b base z (GGStage.incoming base z.heads.j))+1≤credit j₀ u z := by
  let e := GGStage.incoming base z.heads.j
  have hGhost : (z.ledger.config (rightNeighbor e)).leader=false := by
    rw [GGStage.incoming_right]
    exact hc.2.2.2.2.2
  have hM : (z.ledger.config e).mark=true := by
    have H := hc.1.covers e
    have K : z.ledger.slots e=some b := hc.2.2.1
    simpa [K] using H.symm
  have hPay := marked_ghost_stock_pays _ _ hM hGhost hp
  by_cases he : routeTwo g a b z.ledger e=.keep
  · obtain ⟨H,E⟩ := exact_keep g a b base z e hz he
    have hMoves : GGStage.moved z.ledger.config base e z.heads.j=true := by
      simp [GGStage.moved,e,hPay]
    change credit j₀ u (next g a b base z e)+1≤credit j₀ u z
    simp only [credit,hz,E,Option.isSome_none,Bool.false_eq_true,if_false,H,hMoves,Bool.toNat_true]
    omega
  · simp [credit,next,hz,he,e]
    omega

#print axioms projection
#print axioms pending_nomination

private theorem notLoop {n : Nat} (hn : 4≤n) (e : Fin n) : rightNeighbor e≠e := by
  intro h
  have E : liftedSite e 1=liftedSite e 0 := by simpa [liftedSite_zero,liftedSite_succ] using h
  have := liftedSite_inj e (by omega : 1<n) (by omega : 0<n) E
  omega

theorem followed_slot {p c n : Nat} {initial : Config p c n} (hn : 4≤n)
    (g : List (Fin n)) (z : Ledger p c n) (base e tag : Fin n) (d : Nat)
    (hv : Valid z initial) (hg : tag∈g) (hs : z.slots (GGStage.incoming base d)=some tag)
    (he : selectedGroupLoss g z e=none) :
    (advance z e).slots
      (GGStage.incoming base (d+(GGStage.moved z.config base e d).toNat))=some tag := by
  let u := GGStage.incoming base d
  have succ : GGStage.incoming base (d+1)=rightNeighbor u := by
    apply FreshSeparation.succ_inj
    rw [GGStage.incoming_right, liftedSite_succ]
    dsimp [u]
    rw [GGStage.incoming_right]
  by_cases hp : geometricPay (z.config e) (z.config (rightNeighbor e))=true
  · by_cases h : e=u
    · have hSlots : z.slots e=some tag := h.symm ▸ hs
      have hR := WindowScopedSupplier.tracked_no_retirement_of_group_keep g z e tag hg hSlots he
      have hm : (z.config (rightNeighbor e)).mark=false := by
        simpa [RankPhysical.retirement,hp] using hR
      have hvac : z.slots (rightNeighbor e)=none := by
        cases H : z.slots (rightNeighbor e) with
        | none => rfl
        | some val =>
          have H' := hv.covers (rightNeighbor e)
          simp [H,hm] at H'
      have hMove : GGStage.moved z.config base e d=true := by
        have hh : (e == GGStage.incoming base d)=true := beq_iff_eq.mpr h
        simp [GGStage.moved,hh,hp]
      rw [hMove]
      change slotsStep z.config z.slots e (GGStage.incoming base (d+1))=some tag
      rw [succ,←h]
      simp [slotsStep,hp,SevenTagCharge.move,notLoop hn e,hvac,hSlots]
    · have hMove : GGStage.moved z.config base e d=false := by
        have H : (e == GGStage.incoming base d)=false :=
          Bool.eq_false_iff.mpr (fun H => h (beq_iff_eq.mp H))
        simp [GGStage.moved,H]
      rw [hMove]
      change slotsStep z.config z.slots e u=some tag
      simp only [slotsStep,hp,if_true,SevenTagCharge.move,if_neg (Ne.symm h)]
      split
      · simp [show z.slots u=some tag from hs]
      · exact hs
  · have hf := Bool.eq_false_iff.mpr hp
    have hMove : GGStage.moved z.config base e d=false := by simp [GGStage.moved,hf]
    rw [hMove]
    change slotsStep z.config z.slots e u=some tag
    simpa [slotsStep,hf] using hs

theorem continuing_keep {p c n : Nat} {initial : Config p c n} (hn : 4≤n)
    (g : List (Fin n)) (a b k base : Fin n) (z : Cursor p c n) (e : Fin n)
    (h : Continuing initial a b k base z) (ha : a∈g) (hb : b∈g) (hk : k∈g)
    (hz : z.exit=none) (he : routeTwo g a b z.ledger e=.keep) :
    Continuing initial a b k base (next g a b base z e) := by
  obtain ⟨H,_⟩ := exact_keep g a b base z e hz he
  unfold Continuing
  rw [projection,H]
  have hG := empty_group_loss_of_two_keep z.ledger g a b e he
  have ghost (tag : Fin n) (d : Nat) (ha : tag∈g)
      (hs : z.ledger.slots (GGStage.incoming base d)=some tag)
      (hg : (z.ledger.config (liftedSite base d)).leader=false)
      (he : route g [] (some tag) z.ledger e=.keep) :
      ((advance z.ledger e).config
        (liftedSite base (d+(GGStage.moved z.ledger.config base e d).toNat))).leader=false := by
    have h0 := ghost_after_keep hn z.ledger g tag (GGStage.incoming base d) e h.1 ha hs
      ((GGStage.incoming_right base d).symm ▸ hg) he
    have hr : rightNeighbor (if e=GGStage.incoming base d then landingSlot z.ledger.config e
        else GGStage.incoming base d)=
        liftedSite base (d+(GGStage.moved z.ledger.config base e d).toNat) := by
      by_cases hE : e=GGStage.incoming base d
      · subst e
        cases hP : geometricPay (z.ledger.config (GGStage.incoming base d))
          (z.ledger.config (rightNeighbor (GGStage.incoming base d)))
        · have hh := hP
          rw [GGStage.incoming_right] at hh
          simp [landingSlot,GGStage.moved,hh,GGStage.incoming_right]
        · have hh := hP
          rw [GGStage.incoming_right] at hh
          simp [landingSlot,GGStage.moved,hh,GGStage.incoming_right,liftedSite_succ]
      · have hh : (e == GGStage.incoming base d)=false :=
          Bool.eq_false_iff.mpr (fun hh => hE (beq_iff_eq.mp hh))
        simp [hE,hh,GGStage.moved,GGStage.incoming_right]
    dsimp only at h0
    rwa [hr] at h0
  refine ⟨valid_step hn z.ledger initial e h.1,
    followed_slot hn g z.ledger base e a _ h.1 ha h.2.1 hG,
    followed_slot hn g z.ledger base e b _ h.1 hb h.2.2.1 hG,
    followed_slot hn g z.ledger base e k _ h.1 hk h.2.2.2.1 hG,?_,?_⟩
  · exact ghost a _ ha h.2.1 h.2.2.2.2.1 ((keep_iff g a b z.ledger e).mp he).1
  · exact ghost b _ hb h.2.2.1 h.2.2.2.2.2 ((keep_iff g a b z.ledger e).mp he).2

#print axioms followed_slot
#print axioms continuing_keep

open RootedAssembly

def tape {p c n : Nat} (g : List (Fin n)) (a b base : Fin n)
    (z : Cursor p c n) (w : List (Fin n)) :=
  GGTiming.runMarks (next g a b base) z w

theorem tape_append {p c n : Nat} (g : List (Fin n)) (a b base : Fin n)
    (z : Cursor p c n) (w : List (Fin n)) (e : Fin n) :
    tape g a b base z (wordNext w e)=next g a b base (tape g a b base z w) e :=
  GGTiming.runMarks_append _ _ _ _

theorem exit_or_continuing_step {p c n : Nat} {initial : Config p c n} (hn : 4≤n)
    (g : List (Fin n)) (a b k base : Fin n) (z : Cursor p c n) (e : Fin n)
    (ha : a∈g) (hb : b∈g) (hk : k∈g)
    (h : z.exit.isSome=true ∨ Continuing initial a b k base z) :
    (next g a b base z e).exit.isSome=true ∨
      Continuing initial a b k base (next g a b base z e) := by
  cases hz : z.exit with
  | some r => exact .inl (by simp [next,hz])
  | none =>
    by_cases he : routeTwo g a b z.ledger e=.keep
    · exact .inr (continuing_keep hn g a b k base z e
        (h.resolve_left (by simp [hz])) ha hb hk hz he)
    · exact .inl (by simp [next,hz,he])

theorem exit_or_continuing_tape {p c n : Nat} {initial : Config p c n} (hn : 4≤n)
    (g : List (Fin n)) (a b k base : Fin n) (z : Cursor p c n)
    (ha : a∈g) (hb : b∈g) (hk : k∈g)
    (h : z.exit.isSome=true ∨ Continuing initial a b k base z) (w : List (Fin n)) :
    (tape g a b base z w).exit.isSome=true ∨
      Continuing initial a b k base (tape g a b base z w) := by
  induction w generalizing z with
  | nil => exact h
  | cons e w ih => exact ih _ (exit_or_continuing_step hn g a b k base z e ha hb hk h)

theorem j_mono_step {p c n : Nat} (g : List (Fin n)) (a b base : Fin n)
    (z : Cursor p c n) (e : Fin n) :
    z.heads.j≤(next g a b base z e).heads.j := by
  unfold next
  split
  · exact Nat.le_refl _
  · dsimp only
    split
    · exact Nat.le_add_right _ _
    · exact Nat.le_refl _

theorem j_mono_tape {p c n : Nat} (g : List (Fin n)) (a b base : Fin n)
    (z : Cursor p c n) (w : List (Fin n)) :
    z.heads.j≤(tape g a b base z w).heads.j := by
  induction w generalizing z with
  | nil => exact Nat.le_refl _
  | cons e w ih => exact Nat.le_trans (j_mono_step g a b base z e) (ih _)

abbrev PathList (n : Nat) := List (List (Fin n))

/-- Freeze only the virtual paths on a pending old-head reservation. The
decision uses the old stock; in particular the selected physical mark
always advances the ledger. -/
def drainPaths {p c n : Nat} (g : List (Fin n)) (a b base : Fin n)
    (z : Cursor p c n) (P : PathList n) : List (Fin n) → PathList n
  | [] => P
  | e::w =>
    let Q := if (z.ledger.config (GGStage.incoming base z.heads.j)).stock then P
      else GGTiming.advance P e
    drainPaths g a b base (next g a b base z e) Q w

theorem path_append {p c n : Nat} (g : List (Fin n)) (a b base : Fin n)
    (z : Cursor p c n) (P : PathList n) (w : List (Fin n)) (e : Fin n) :
    drainPaths g a b base z P (wordNext w e)=
      if pending base (tape g a b base z w) then drainPaths g a b base z P w
      else GGTiming.advance (drainPaths g a b base z P w) e := by
  induction w generalizing z P with
  | nil => rfl
  | cons i w ih => exact ih _ _

/-- The actual remaining physical obligations for the A0 stock cut:
an original-byte cap for surviving J and the fixed-sink exclusion DAG
comparison when no reservation is active. The local physical facts
and pause scheduling are proved outside this certificate. -/
structure StockCutCertificate {p c n : Nat} (g : List (Fin n)) (a b base : Fin n)
    (z : Cursor p c n) (u : Nat) where
  paths : PathList n
  L : Nat
  depth : L≤4*u+2
  length_bound : ∀ P ∈ paths, P.length≤L
  count : paths.length≤2^(L+1)
  paid_cap : ∀ w, ¬drained base (tape g a b base z w) →
    (tape g a b base z w).heads.j-z.heads.j≤u
  completion : ∀ w, ¬pending base (tape g a b base z w) →
    GGTiming.finished (drainPaths g a b base z paths w) →
      drained base (tape g a b base z w)

theorem mean_of_certificate {p c n : Nat} {initial : Config p c n}
    (hn : 4≤n) (g : List (Fin n)) (a b k base : Fin n) (z : Cursor p c n)
    (ha : a∈g) (hb : b∈g) (hk : k∈g)
    (h : z.exit.isSome=true ∨ Continuing initial a b k base z)
    (u : Nat) (C : StockCutCertificate g a b base z u) :
    IIDExpectedHittingTimeAtMost wordNext (fun w => drained base (tape g a b base z w))
      [] (17*n*(u+1)) := by
  let done := fun w => drained base (tape g a b base z w)
  let paused := fun w => pending base (tape g a b base z w)
  let paths := drainPaths g a b base z C.paths
  let pc := fun w => credit z.heads.j u (tape g a b base z w)
  have hCost := GGPause.hittingTime_with_pauses wordNext done paths pc paused (fun _ => True)
    (fun _ _ _ => trivial) (fun w e _ _ => by
      dsimp [pc]
      rw [tape_append]
      exact credit_nonincrease g a b base z.heads.j u _ e)
    (fun w _ ht hp => ⟨fun hF => ht (C.completion w hp hF),fun e => by
      unfold paths
      rw [path_append,if_neg hp]⟩)
    (fun w _ ht hp => by
      let y := tape g a b base z w
      have he : y.exit=none := by
        cases hh : y.exit
        · rfl
        · exact (ht (.inl (by change y.exit.isSome=true; simp [hh]))).elim
      have hCont : Continuing initial a b k base y :=
        (exit_or_continuing_tape hn g a b k base z ha hb hk h w).resolve_left (by
          change y.exit.isSome≠true
          simp [he])
      refine ⟨⟨GGStage.incoming base y.heads.j,?_⟩,fun e => ?_⟩
      · dsimp [pc]
        rw [tape_append]
        exact pending_nomination g a b k base z.heads.j u y hCont he
          (j_mono_tape g a b base z w) (C.paid_cap w ht) hp
      · unfold paths
        rw [path_append,if_pos hp])
  intro t
  have hp := GGTiming.pathClock_expected (show 0<n by omega) C.paths C.L C.length_bound C.count t
  have hB : 4*n*(C.L+1)+n*pc []≤17*n*(u+1) := by
    have hC : pc []≤u+1 := by
      change credit z.heads.j u z≤u+1
      unfold credit
      split <;> omega
    calc
      _ = n*(4*(C.L+1)+pc []) := by simp only [Nat.mul_add]; ac_rfl
      _ ≤ n*(17*(u+1)) := Nat.mul_le_mul_left n (by have := C.depth; omega)
      _ = _ := by ac_rfl
  apply Nat.le_trans (hCost t [] trivial)
  exact Nat.le_trans (Nat.add_le_add_right hp _) (by
    rw [←Nat.add_mul]
    exact Nat.mul_le_mul_right _ hB)

#print axioms tape_append
#print axioms path_append
#print axioms mean_of_certificate

open WindowSpan

abbrev entryBase {p c n : Nat} (x : Config p c n) (i : Fin (RankPhysical.rank x)) :=
  rootSite x (liftedSite i 1)

def entryCursor {p c n : Nat} (x : Config p c n)
    (i : Fin (RankPhysical.rank x)) : Cursor p c n :=
  ⟨initial x,WindowA0.heads x (liftedSite i 1),none⟩

theorem entry_continuing {p c n : Nat} (x : Config p c n) (i : Fin (RankPhysical.rank x))
    (hm : MCOV x) (hc : COV x) (short : 2*span x i+2<n)
    (h1 : (x (rootSite x (liftedSite i 1))).leader=false)
    (h2 : (x (rootSite x (liftedSite i 2))).leader=false) :
    let g := window7 (WindowRoster.roster x) i
    let tag := fun j : Nat => WindowRoster.roster x (liftedSite i j)
    Continuing x (tag 1) (tag 2) (tag 3) (entryBase x i) (entryCursor x i) ∧
    tag 1∈g ∧ tag 2∈g ∧ tag 3∈g ∧
      (entryCursor x i).heads.k-(entryCursor x i).heads.i≤span x i := by
  let g := window7 (WindowRoster.roster x) i
  let q := liftedSite i 1
  let tag := fun j : Nat => WindowRoster.roster x (liftedSite i j)
  have m1 : tag 1∈g :=
    List.mem_map.mpr ⟨(1 : Fin 7),List.mem_finRange _,rfl⟩
  have m2 : tag 2∈g :=
    List.mem_map.mpr ⟨(2 : Fin 7),List.mem_finRange _,rfl⟩
  have m3 : tag 3∈g :=
    List.mem_map.mpr ⟨(3 : Fin 7),List.mem_finRange _,rfl⟩
  have H := WindowA0.a0_initialCut x i hm hc short h1 h2
  have e1 : GGStage.incoming (entryBase x i) 0=tag 1 := by
    apply FreshSeparation.succ_inj
    rw [GGStage.incoming_right,liftedSite_zero]
    rfl
  have one : spanK x q 1=gap x q := by
    rw [show (1:Nat)=0+1 from rfl, spanK_succ,liftedSite_zero]
    change 0+gap x q=gap x q
    exact Nat.zero_add _
  have e2 : GGStage.incoming (entryBase x i) (gap x q)=tag 2 := by
    apply FreshSeparation.succ_inj
    rw [GGStage.incoming_right,←one,at_rootSpanK,liftedSite_succ,liftedSite_zero]
    change rootSite x (rightNeighbor (liftedSite i 1))=rightNeighbor (tag 2)
    rw [←liftedSite_succ]
    rfl
  have two : spanK x q 2=gap x q+gap x (rightNeighbor q) := by
    rw [show (2:Nat)=1+1 from rfl,spanK_succ,one,liftedSite_succ,liftedSite_zero]
  have e3 : GGStage.incoming (entryBase x i) (gap x q+gap x (rightNeighbor q))=tag 3 := by
    apply FreshSeparation.succ_inj
    rw [GGStage.incoming_right,←two,at_rootSpanK]
    change rootSite x (liftedSite (liftedSite i 1) 2)=rootSite x (liftedSite i 3)
    congr 1
    rw [show (2:Nat)=1+1 from rfl,liftedSite_succ,liftedSite_succ,liftedSite_zero,
      ←liftedSite_succ,←liftedSite_succ]
  change Continuing x (tag 1) (tag 2) (tag 3) (entryBase x i) (entryCursor x i) ∧
    tag 1∈g ∧ tag 2∈g ∧ tag 3∈g ∧ _
  refine ⟨⟨valid_init x hm hc,?_,?_,?_,H.2.2.2.2.1,H.2.2.2.2.2⟩,m1,m2,m3,?_⟩
  · change initSlots x (GGStage.incoming (entryBase x i) 0)=some (tag 1)
    rw [e1]
    exact window7_init_tag x i _ m1
  · change initSlots x (GGStage.incoming (entryBase x i) (gap x q))=some (tag 2)
    rw [e2]
    exact window7_init_tag x i _ m2
  · change initSlots x (GGStage.incoming (entryBase x i)
      (gap x q+gap x (rightNeighbor q)))=some (tag 3)
    rw [e3]
    exact window7_init_tag x i _ m3
  · change gap x q+gap x (rightNeighbor q)-0≤span x i
    rw [Nat.sub_zero]
    have hh : rightNeighbor q=liftedSite i 2 := (liftedSite_succ i 1).symm
    rw [hh]
    exact two_entry_gaps_le x i

#print axioms entry_continuing
end L4.WindowA0StockDrain
