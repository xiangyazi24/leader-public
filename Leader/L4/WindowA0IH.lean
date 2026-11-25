import Leader.L4.WindowA0Drained
import Leader.L4.WindowA0Route

/-! Physically closed drained A0 segment. Slots are rebased on the
actual moving ghost and no rail cleanliness is assumed at entry. -/
namespace L4.WindowA0IH
open GGStage

structure Cut (p c n : Nat) where
  config : Config p c n
  top : Fin n
  gap : Nat
  stopped : Bool

def target {p c n : Nat} (s : Cut p c n) : Fin n := liftedSite s.top s.gap

structure Live {p c n : Nat} (J : Fin n) (H : Nat) (s : Cut p c n) : Prop where
  bounded : s.gap ≤ H
  gapPos : 0 < s.gap
  noWrap : s.gap < n
  fixedRight : target s = J
  mc : MCOV s.config
  cv : COV s.config
  markTop : (s.config (incoming s.top 0)).mark = true
  markRight : (s.config (liftedSite s.top (s.gap-1))).mark = true
  openBonds : ∀ k, k+1 < s.gap → (s.config (liftedSite s.top k)).mark=false
  topGhost : (s.config s.top).leader=false
  rightGhost : (s.config J).leader=false
  empty : ∀ k, k<s.gap → (s.config (liftedSite s.top k)).stock=false

def I_H {p c n : Nat} (J : Fin n) (H : Nat) (s : Cut p c n) : Prop :=
  s.stopped=true ∨ Live J H s

theorem incoming_succ_lift {n : Nat} (b : Fin n) (k : Nat) :
    incoming b (k+1)=liftedSite b k := by
  apply FreshSeparation.succ_inj
  rw [incoming_right,←liftedSite_succ]

theorem incoming_top {n : Nat} (b : Fin n) :
    (incoming b 0).val=(b.val+(n-1))%n := by
  simp [incoming,liftedSite]

private theorem interior_empty_leader {p c n : Nat} {J : Fin n} {H : Nat} {s : Cut p c n}
    (h : Live J H s) (k : Nat) (hk : k<s.gap) :
    (s.config (liftedSite s.top k)).leader=false := by
  cases k with
  | zero => simpa [liftedSite_zero] using h.topGhost
  | succ k =>
    by_cases hb : (s.config (liftedSite s.top (k+1))).leader=true
    · have hh := h.mc (liftedSite s.top k) (.inl (by rwa [←liftedSite_succ]))
      have hz := h.openBonds k hk
      rw [hz] at hh
      contradiction
    · exact Bool.eq_false_iff.mpr hb

/-- The physical pair is always executed. A selected loss furnished by
the router is an additional early stop, not a masked physical step. -/
def advance {p c n : Nat} (early : Cut p c n → Fin n → Bool)
    (s : Cut p c n) (e : Fin n) : Cut p c n :=
  let y := step s.config e
  if s.stopped then {s with config := y} else
    let d := (moved s.config s.top e 0).toNat
    let top := liftedSite s.top d
    let quit := early s e || retires s.config s.top e 0 || (y top).leader ||
      (y (target s)).leader
    ⟨y,top,s.gap-d,quit⟩

theorem stopped_sticky {p c n : Nat} (early : Cut p c n → Fin n → Bool)
    (s : Cut p c n) (e : Fin n) (h : s.stopped=true) :
    (advance early s e).stopped=true := by simp [advance,h]

theorem config_projection {p c n : Nat} (early : Cut p c n → Fin n → Bool)
    (s : Cut p c n) (e : Fin n) :
    (advance early s e).config=step s.config e := by
  unfold advance
  split <;> rfl

private theorem marked_survives {p c n : Nat} (hn : 4≤n)
    (x : Config p c n) (mc : MCOV x) (e b : Fin n)
    (hm : (x b).mark=true)
    (hno : e=b → geometricPay (x e) (x (rightNeighbor e))=false) :
    (step x e b).mark=true := by
  rw [covered_step_mark hn x mc]
  by_cases h : geometricPay (x e) (x (rightNeighbor e))=true
  · have hn' : b≠e := by intro he; rw [hno he.symm] at h; contradiction
    simp [h,hn',hm]
  · simp [Bool.eq_false_iff.mpr h,hm]

theorem close {p c n : Nat} (hn : 4≤n) (early : Cut p c n → Fin n → Bool)
    (J : Fin n) (H : Nat) (s : Cut p c n) (e : Fin n)
    (old : I_H J H s) : I_H J H (advance early s e) := by
  by_cases oldStop : s.stopped=true
  · exact .inl (stopped_sticky early s e oldStop)
  have lf := old.resolve_left oldStop
  let x := s.config
  let b := s.top
  let h := s.gap
  let y := step x e
  let d := (moved x b e 0).toNat
  let b' := liftedSite b d
  let stop := early s e || retires x b e 0 || (y b').leader || (y (target s)).leader
  have next : advance early s e = ⟨y,b',h-d,stop⟩ := by
    simp [advance,Bool.eq_false_iff.mpr oldStop,x,b,h,y,d,b',stop]
  rw [next]
  by_cases hs : stop=true
  · exact .inl hs
  have hsf := Bool.eq_false_iff.mpr hs
  have stops : retires x b e 0=false ∧ (y b').leader=false ∧ (y (target s)).leader=false := by
    change (early s e || retires x b e 0 || (y b').leader || (y (target s)).leader)=false at hsf
    simp only [Bool.or_eq_false_iff] at hsf
    exact ⟨hsf.1.1.2,hsf.1.2,hsf.2⟩
  have hmJ : (x (incoming b h)).mark=true := by
    have hh : h = (h-1)+1 := by have := lf.gapPos; omega
    rw [hh,incoming_succ_lift]
    exact lf.markRight
  obtain ⟨noJ,emptyNew⟩ := WindowA0Drained.drained_after_top_rebase hn x b e lf.gapPos
    lf.markTop hmJ lf.empty (fun k hk => interior_empty_leader lf k hk)
  change moved x b e h=false at noJ
  have dd : d≤1 := by unfold d; cases moved x b e 0 <;> decide
  have hD : d<h := by
    have hpos : 0<h := lf.gapPos
    by_cases hp : d=1
    · by_cases ok : d<h
      · exact ok
      · exfalso
        have hh : h=1 := by omega
        have hM : moved x b e 0=true := by
          cases he : moved x b e 0 <;> simp [d,he] at hp ⊢
        have mb : (x b).mark=true := by
          have q := lf.markRight
          change (x (liftedSite b (h-1))).mark=true at q
          simpa [hh,liftedSite_zero] using q
        have hr := stops.1
        simp [retires,hM,liftedSite_zero,mb] at hr
    · omega
  have newRight : liftedSite b' (h-d) = target s := by
    rw [RestartGeometry.lift_add,show d+(h-d)=h by omega]
    rfl
  have bnd : h<n := lf.noWrap
  have newMarkRight : (y (liftedSite b' ((h-d)-1))).mark=true := by
    rw [RestartGeometry.lift_add,show d+(h-d-1)=h-1 by omega]
    apply marked_survives hn x lf.mc e _ lf.markRight
    intro he
    by_cases pay : geometricPay (x e) (x (rightNeighbor e))=true
    · have ee : e=incoming b h := by
        rw [he,show h=(h-1)+1 by omega,incoming_succ_lift]
      have hM : moved x b e h=true := Bool.and_eq_true_iff.mpr ⟨beq_iff_eq.mpr ee,pay⟩
      rw [hM] at noJ
      contradiction
    · exact Bool.eq_false_iff.mpr pay
  have newMarkTop : (y (incoming b' 0)).mark=true := by
    by_cases hd : d=0
    · have hZero : moved x b e 0=false := by cases he : moved x b e 0 <;> simp [d,he] at hd ⊢
      change (y (incoming (liftedSite b d) 0)).mark=true
      rw [hd,liftedSite_zero]
      apply marked_survives hn x lf.mc e _ lf.markTop
      intro he
      change e=incoming b 0 at he
      unfold moved at hZero
      simpa [beq_iff_eq.mpr he] using hZero
    · have hd1 : d=1 := by omega
      have hM : moved x b e 0=true := by
        cases he : moved x b e 0 <;> simp [d,he] at hd1 ⊢
      have he : e=incoming b 0 := beq_iff_eq.mp (Bool.and_eq_true_iff.mp hM).1
      have pay := (Bool.and_eq_true_iff.mp hM).2
      have hr : rightNeighbor e=b := by rw [he,incoming_right,liftedSite_zero]
      have hh : incoming b' 0=b := by
        apply FreshSeparation.succ_inj
        rw [incoming_right,liftedSite_zero]
        change liftedSite b d=rightNeighbor b
        rw [hd1]
        simpa [liftedSite_zero] using liftedSite_succ b 0
      have hne : b≠e := by
        intro heq
        have H := liftedSite_inj b (by omega : 1<n) (by omega : 0<n)
          (by simpa [liftedSite_succ,liftedSite_zero,←heq] using hr)
        omega
      rw [hh,covered_step_mark hn x lf.mc,if_pos pay]
      simp [hne,hr]
  have newOpen : ∀ k, k+1<h-d → (y (liftedSite b' k)).mark=false := by
    intro k hk
    rw [RestartGeometry.lift_add,covered_step_mark hn x lf.mc]
    have hOld : (x (liftedSite b (d+k))).mark=false := lf.openBonds _ (by omega)
    by_cases pay : geometricPay (x e) (x (rightNeighbor e))=true
    · rw [if_pos pay]
      by_cases he : liftedSite b (d+k)=e
      · simp [he]
      · rw [if_neg he]
        by_cases hr : liftedSite b (d+k)=rightNeighbor e
        · exfalso
          cases hnum : d+k with
          | zero =>
            have hz : d=0 := by omega
            have hE : e=incoming b 0 := FreshSeparation.succ_inj
              ((by simpa [hnum,liftedSite_zero] using hr.symm : rightNeighbor e=b).trans
                (by rw [incoming_right,liftedSite_zero]))
            have hmove : moved x b e 0=true := Bool.and_eq_true_iff.mpr ⟨beq_iff_eq.mpr hE,pay⟩
            simp [d,hmove] at hz
          | succ j =>
            have hE : e=liftedSite b j := FreshSeparation.succ_inj
              (by simpa [hnum,liftedSite_succ] using hr.symm)
            have m := RearTrace.paid_was_marked lf.mc e pay
            have nMark := lf.openBonds j (by omega)
            rw [hE,nMark] at m
            contradiction
        · simpa [hr] using hOld
    · simp [Bool.eq_false_iff.mpr pay,hOld]
  have cov := EntranceCover.cover_closed hn x e ⟨lf.mc,lf.cv⟩
  refine .inr ⟨?_,?_,?_,newRight.trans lf.fixedRight,cov.1,cov.2,
    newMarkTop,newMarkRight,newOpen,stops.2.1,lf.fixedRight ▸ stops.2.2,emptyNew⟩
  · exact Nat.le_trans (Nat.sub_le _ _) lf.bounded
  · change 0<h-d; omega
  · change h-d<n; omega

theorem incoming_rebase {n : Nat} (b : Fin n) (i k : Nat) :
    incoming (liftedSite b i) k = incoming b (i+k) := by
  apply FreshSeparation.succ_inj
  rw [incoming_right,incoming_right,RestartGeometry.lift_add]

theorem moved_rebase {p c n : Nat} (x : Config p c n) (b e : Fin n) (i k : Nat) :
    moved x (liftedSite b i) e k = moved x b e (i+k) := by
  simp only [moved,incoming_rebase]

theorem retires_rebase {p c n : Nat} (x : Config p c n) (b e : Fin n) (i k : Nat) :
    retires x (liftedSite b i) e k = retires x b e (i+k) := by
  simp only [retires,moved_rebase,RestartGeometry.lift_add]

/-- Erase the rightmost GG witness from the live record and rebase
at its current first head. GG preserves the two-head invariant even
though it may stop early on a third-head retirement. -/
def fromGG {p c n : Nat} (base : Fin n) (s : GGStage.Obs p c n) : Cut p c n :=
  ⟨s.config,liftedSite base s.heads.i,s.heads.j-s.heads.i,s.stopped⟩

/-- The actual drained cut supplies the initial I_H predicate, with
the current physical second head fixed as J. No rail invariant is
required; the stock cut includes the first head itself. -/
theorem fromGG_entry {p c n : Nat} (base : Fin n) (s : GGStage.Obs p c n)
    (H : Nat) (hB : s.heads.j-s.heads.i≤H)
    (hGeom : AmbientConsecutive s.config base s.heads)
    (hc : MCOV s.config ∧ COV s.config)
    (hI : (s.config (liftedSite base s.heads.i)).leader=false)
    (hJ : (s.config (liftedSite base s.heads.j)).leader=false)
    (hDrain : Drained base s) :
    I_H (liftedSite base s.heads.j) H (fromGG base s) := by
  by_cases hStop : s.stopped=true
  · exact .inl hStop
  obtain ⟨hij,hjk,hki,hmI,hmJ,_,openIJ,_⟩ := hGeom
  have hGap : s.heads.i+(s.heads.j-s.heads.i)=s.heads.j := by omega
  refine .inr ⟨hB,by change 0<s.heads.j-s.heads.i; omega,
    by change s.heads.j-s.heads.i<n; omega,?_,hc.1,hc.2,?_,?_,?_,hI,hJ,?_⟩
  · change liftedSite (liftedSite base s.heads.i) (s.heads.j-s.heads.i) = _
    rw [RestartGeometry.lift_add,hGap]
  · change (s.config (incoming (liftedSite base s.heads.i) 0)).mark=true
    rwa [incoming_rebase,Nat.add_zero]
  · change (s.config (liftedSite (liftedSite base s.heads.i)
      (s.heads.j-s.heads.i-1))).mark=true
    rw [←incoming_succ_lift,incoming_rebase,
      show s.heads.i+(s.heads.j-s.heads.i-1+1)=s.heads.j by omega]
    exact hmJ
  · intro k hk
    change k+1<s.heads.j-s.heads.i at hk
    change (s.config (liftedSite (liftedSite base s.heads.i) k)).mark=false
    have no := openIJ (s.heads.i+(k+1)) (by omega) (by omega)
    unfold rootAt at no
    rw [←incoming_rebase,incoming_succ_lift] at no
    exact Bool.eq_false_iff.mpr no
  · intro k hk
    change k<s.heads.j-s.heads.i at hk
    change (s.config (liftedSite (liftedSite base s.heads.i) k)).stock=false
    rw [RestartGeometry.lift_add]
    exact (hDrain.resolve_left hStop) _ (by omega) (by omega)

#print axioms fromGG_entry

theorem fromGG_close {p c n : Nat} (hn : 4≤n)
    (base J e : Fin n) (H : Nat) (s : GGStage.Obs p c n)
    (h : I_H J H (fromGG base s)) :
    I_H J H (fromGG base (GGStage.advance base s e)) := by
  by_cases hs : s.stopped=true
  · exact .inl (by simp [fromGG,GGStage.advance,hs])
  let i := s.heads.i
  let j := s.heads.j
  let b := liftedSite base i
  let d := (moved s.config base e i).toNat
  let x := s.config
  let y := step x e
  have live := h.resolve_left (show ¬(fromGG base s).stopped=true from hs)
  have hij : i<j := by have h := live.gapPos; change 0<j-i at h; omega
  have hR : target (fromGG base s)=liftedSite base j := by
    change liftedSite (liftedSite base i) (j-i)=liftedSite base j
    rw [RestartGeometry.lift_add,show i+(j-i)=j by omega]
  have hmR : (x (incoming b (j-i))).mark=true := by
    have hh : j-i=(j-i-1)+1 := by omega
    rw [hh,incoming_succ_lift]
    exact live.markRight
  obtain ⟨hNo,_⟩ := WindowA0Drained.drained_step hn x b e
    (show 0<j-i by omega) live.markTop hmR live.empty
    (fun k hk => interior_empty_leader live k hk)
  rw [moved_rebase,show i+(j-i)=j by omega] at hNo
  have hrJ : retires x base e j=false := by simp [retires,hNo]
  let E : Cut p c n → Fin n → Bool := fun _ f => retires x base f s.heads.k
  let stop := retires x base e i || retires x base e s.heads.k ||
       (y (liftedSite base (i+d))).leader || (y (liftedSite base j)).leader
  have comp :
      advance E (fromGG base s) e =
      ⟨y,liftedSite base (i+d),j-i-d,stop⟩ := by
    have hD : moved x b e 0 = moved x base e i := by
      rw [moved_rebase,Nat.add_zero]
    have hT : retires x b e 0 = retires x base e i := by
      rw [retires_rebase,Nat.add_zero]
    have hstop :
        (retires x base e s.heads.k || retires x b e 0 ||
        (y (liftedSite b (moved x b e 0).toNat)).leader || (y (target (fromGG base s))).leader) = stop := by
      rw [hT,hD,RestartGeometry.lift_add,hR]
      simp only [stop,d]
      rw [Bool.or_comm (retires x base e s.heads.k) (retires x base e i)]
    unfold advance
    rw [if_neg (show (fromGG base s).stopped ≠ true from hs)]
    change (⟨y,liftedSite b (moved x b e 0).toNat,j-i-(moved x b e 0).toNat,
        retires x base e s.heads.k || retires x b e 0 ||
        (y (liftedSite b (moved x b e 0).toNat)).leader || (y (target (fromGG base s))).leader⟩
        : Cut p c n)=_
    rw [hstop,hD,RestartGeometry.lift_add]
  have closed := close hn E J H (fromGG base s) e h
  rw [comp] at closed
  unfold GGStage.advance
  rw [if_neg hs]
  change I_H J H (fromGG base
    (if retires x base e i || retires x base e j || retires x base e s.heads.k ||
        (y (liftedSite base (i+d))).leader ||
        (y (liftedSite base (j+(moved x base e j).toNat))).leader
      then ⟨y,s.heads,true⟩
      else ⟨y,⟨i+d,j+(moved x base e j).toNat,
        s.heads.k+(moved x base e s.heads.k).toNat⟩,false⟩))
  rw [hrJ,hNo]
  simp only [Bool.or_false,Bool.toNat_false,Nat.add_zero]
  change I_H J H (fromGG base (if stop then _ else _))
  split
  · exact .inl rfl
  · rename_i ht
    have ht' : stop=false := Bool.eq_false_iff.mpr ht
    have he : j-(i+d) = j-i-d := by omega
    simpa only [ht',fromGG,he] using closed

/-- Iteration on the actual three-head GG observer and unchanged label
word. Every prefix before stopping has an empty, shrinking segment. -/
theorem fromGG_word {p c n : Nat} (hn : 4≤n)
    (base J : Fin n) (H : Nat) (w : List (Fin n)) (s : GGStage.Obs p c n)
    (h : I_H J H (fromGG base s)) :
    I_H J H (fromGG base (GGTiming.runMarks (GGStage.advance base) s w)) := by
  induction w generalizing s with
  | nil => exact h
  | cons e w ih => exact ih _ (fromGG_close hn base J e H s h)

/-- Iteration on the projected physical cuts; cut predicates are sticky,
while the concrete configuration still takes every mark of the word. -/
theorem cut_word {p c n : Nat} (hn : 4≤n) (early : Cut p c n → Fin n → Bool)
    (J : Fin n) (H : Nat) (w : List (Fin n)) (s : Cut p c n) (h : I_H J H s) :
    I_H J H (GGTiming.runMarks (advance early) s w) := by
  induction w generalizing s with
  | nil => exact h
  | cons e w ih => exact ih _ (close hn early J H s e h)

#print axioms fromGG_word
#print axioms cut_word
/-- Adjoin the exact original seven-tag ledger without perturbing
any physical marks. A route decision is read on the old ledger, but
its next config and the geometric cut use the same completed row. -/
structure Routed (p c n : Nat) where
  cut : Cut p c n
  ledger : SevenTagCharge.Ledger p c n
  sync : cut.config=ledger.config

def routedNext {p c n : Nat} (group : List (Fin n)) (a b : Fin n)
    (s : Routed p c n) (e : Fin n) : Routed p c n :=
  let early : Cut p c n → Fin n → Bool :=
    fun _ f => decide (WindowA0Route.routeTwo group a b s.ledger f ≠ .keep)
  ⟨advance early s.cut e,SevenTagCharge.advance s.ledger e,
    (config_projection early s.cut e).trans
      (congrArg (fun x => step x e) s.sync)⟩

theorem routed_close {p c n : Nat} (hn : 4≤n)
    (group : List (Fin n)) (a b J : Fin n) (H : Nat) (s : Routed p c n)
    (e : Fin n) (h : I_H J H s.cut) :
    I_H J H (routedNext group a b s e).cut :=
  close hn _ J H s.cut e h

theorem routed_word {p c n : Nat} (hn : 4≤n)
    (group : List (Fin n)) (a b J : Fin n) (H : Nat)
    (s : Routed p c n) (w : List (Fin n)) (h : I_H J H s.cut) :
    I_H J H (GGTiming.runMarks (routedNext group a b) s w).cut := by
  induction w generalizing s with
  | nil => exact h
  | cons e w ih => exact ih _ (routed_close hn group a b J H s e h)

theorem routed_projects {p c n : Nat}
    (group : List (Fin n)) (a b : Fin n) (s : Routed p c n) (w : List (Fin n)) :
    (GGTiming.runMarks (routedNext group a b) s w).ledger =
      GGTiming.runMarks SevenTagCharge.advance s.ledger w := by
  induction w generalizing s with
  | nil => rfl
  | cons e w ih => exact ih (routedNext group a b s e)

#print axioms routed_close
#print axioms routed_word
#print axioms routed_projects
#print axioms fromGG_close
#print axioms close
#print axioms config_projection
end L4.WindowA0IH
