import Leader.L4.PhysicalShortSheet
import Leader.L4.PhysicalShortMISGeometry
import Leader.L4.PhysicalCustodyH2Ready
import Leader.L4.ShortSheetRankClock
import Leader.L4.SelectedMISLayers
import Leader.L4.ShortReadCaptureGeometry
import Leader.L4.MonitorRawBridge

namespace L4.ShortMISEngine

open AllSizeProtocol PhysicalCustody PhysicalShortSheet
open BStarH6Ordinal ShortResetChart ShortResetCycle ShortLayerGeometry
open ShortHopSpacing

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- The actual immutable lower fibre and physical geometry of one
    current short sheet. No condition on current token/file/bank bytes. -/
structure Params (s n : Nat) where
  sheet : Sheet
  Lower : Raw s n → Prop
  lowerClosed : AllSizeComposition.Closed (rawNext s) Lower
  h : Fin n → Bool
  maskEq : ∀ x, Lower x → PhysicalShortSheet.mask sheet x=h
  hh : ∃ i,h i=true
  B : Nat
  room : 3*B<n
  gap : ∀ i,h i=true → ∃ d≤B, Gap h i d

variable {s n : Nat}

def Params.byte (P : Params s n) (x : Raw s n) (i : Fin n) : BitVec 96 :=
  bytes P.sheet (x i)

def Params.cacheOff (P : Params s n) (x : Raw s n) (i : Fin n) : Nat :=
  (ShortGeo.mis.off.read (P.byte x i)).toNat

def Params.cacheSucc (P : Params s n) (x : Raw s n) (i : Fin n) : BitVec 1 :=
  ShortGeo.mis.successor.read (P.byte x i)

def Params.wantSucc (P : Params s n) (i : Fin n) : BitVec 1 :=
  BitVec.ofNat 1 (P.h (rightNeighbor i)).toNat

def Cached (P : Params s n) (x : Raw s n) : Prop :=
  P.Lower x ∧ ∀ i, P.cacheOff x i=min 3 (ordinal P.h P.hh i) ∧
    P.cacheSucc x i=P.wantSucc i

def Precision (P : Params s n) (k : Nat) (x : Raw s n) : Prop :=
  ∀ i, min k (P.cacheOff x i)=min k (ordinal P.h P.hh i)

theorem Params.Bpos (P : Params s n) : 0<P.B := by
  obtain ⟨r,H⟩ := P.hh
  obtain ⟨d,D,F⟩ := P.gap r H
  have A := F.positive
  omega

theorem Params.nonself (P : Params s n) : 1<n := by
  have A := P.Bpos
  have B := P.room
  omega

theorem Params.sep (P : Params s n) (e : Fin n) :
    e≠rightNeighbor e :=
  edge_sep P.nonself e

theorem Params.off_bound (P : Params s n) (x : Raw s n) (i : Fin n) :
    P.cacheOff x i≤3 := by
  have A := (ShortGeo.mis.off.read (P.byte x i)).isLt
  change (ShortGeo.mis.off.read (P.byte x i)).toNat < 2^2 at A
  change (ShortGeo.mis.off.read (P.byte x i)).toNat≤3
  omega

/-! The four actual cache equations.  In particular we never apply
ShortSheetProjection.work_to_raw_field to an owned cache bit. -/

/-- Lift the literal old-pair refresh through the exact sheet
    projection. Geometry belongs to the joined patch. -/
theorem Params.pair_refresh (P : Params s n) (x : Raw s n)
    (X : P.Lower x) (e : Fin n) :
    ShortGeo.mis.Refresh 3 (P.h e,P.h (rightNeighbor e))
      (P.byte x e,P.byte x (rightNeighbor e))
      (P.byte (rawNext s x e) e,
        P.byte (rawNext s x e) (rightNeighbor e)) := by
  let r := rightNeighbor e
  let z := (P.byte x e,P.byte x r)
  let p := PhysicalShortSheet.pairStep (rows s) (P.h e,P.h r) z
  have A := PhysicalShortSheet.exact_raw_step P.sheet x e
  rw [P.maskEq x X] at A
  have L : P.byte (rawNext s x e) e=p.1 := by
    have K := congrFun A e
    simpa only [Params.byte,PhysicalShortSheet.sliceStep,if_pos rfl,p,z,r] using K
  have R : P.byte (rawNext s x e) r=p.2 := by
    have K := congrFun A r
    have ne : r≠e := Ne.symm (P.sep e)
    simpa only [Params.byte,PhysicalShortSheet.sliceStep,r,if_neg ne,if_true,p,z] using K
  -- CHECK: PhysicalShortSheet.lean:20–22 and
  -- AllSizeProtocol.lean:936–947. pairStep is literally the
  -- ShortGeo.mis.patches 3 wrapper with the actual work proposal.
  have H : ShortGeo.mis.Refresh 3 (P.h e,P.h r) z p :=
    ShortGeo.refresh ShortGeo.mis 3 (P.h e,P.h r) z
      ((rows s).mis (P.h e,P.h r) z)
  change ShortGeo.mis.Refresh 3 (P.h e,P.h r) z
    (P.byte (rawNext s x e) e,P.byte (rawNext s x e) r)
  rw [L,R]
  exact H

theorem Params.raw_refresh (P : Params s n) (x : Raw s n)
    (X : P.Lower x) (e : Fin n) :
    P.cacheSucc (rawNext s x e) e=P.wantSucc e ∧
    P.cacheOff (rawNext s x e) (rightNeighbor e)=
      (if P.h (rightNeighbor e) then 0 else
        min 3 ((if P.h e then 0 else min 3 (P.cacheOff x e))+1)) ∧
    P.cacheOff (rawNext s x e) e=P.cacheOff x e ∧
    P.cacheSucc (rawNext s x e) (rightNeighbor e)=
      P.cacheSucc x (rightNeighbor e) := by
  have A := P.pair_refresh x X e
  have R := congrArg BitVec.toNat A.2.1
  rw [ShortGeo.nextOff_nat _ _ _ _ (by decide)] at R
  -- CHECK: AllSizeProtocol.lean:406–423,428,936–941.
  -- The two remaining definitions reduce directly to cacheOff/
  -- wantSucc; cap 3 fits in the literal two-bit field.
  exact ⟨A.1,R,congrArg BitVec.toNat A.2.2.1,A.2.2.2⟩

theorem Params.remote_byte (P : Params s n) (x : Raw s n) (e i : Fin n)
    (L : i≠e) (R : i≠rightNeighbor e) :
    P.byte (rawNext s x e) i=P.byte x i := by
  have A := congrFun (PhysicalShortSheet.exact_raw_step P.sheet x e) i
  simpa only [Params.byte,PhysicalShortSheet.sliceStep,if_neg L,if_neg R] using A

theorem Params.off_hold (P : Params s n) (x : Raw s n)
    (X : P.Lower x) (e i : Fin n) (I : i≠rightNeighbor e) :
    P.cacheOff (rawNext s x e) i=P.cacheOff x i := by
  by_cases E : i=e
  · subst i
    exact (P.raw_refresh x X e).2.2.1
  · exact congrArg (fun b : BitVec 96 => (ShortGeo.mis.off.read b).toNat)
      (P.remote_byte x e i E I)

theorem Params.succ_hold (P : Params s n) (x : Raw s n)
    (X : P.Lower x) (e i : Fin n) (I : i≠e) :
    P.cacheSucc (rawNext s x e) i=P.cacheSucc x i := by
  by_cases E : i=rightNeighbor e
  · subst i
    exact (P.raw_refresh x X e).2.2.2
  · exact congrArg (fun b : BitVec 96 => ShortGeo.mis.successor.read b)
      (P.remote_byte x e i I E)

/-! All-mark precision induction. The ordinal counts physical sites
since the most recent h-header, not lower-root hops. -/

theorem Params.offset_mark (P : Params s n) (x : Raw s n)
    (X : P.Lower x) (e : Fin n) (k : Nat) (hk : k<3)
    (A : Precision P k x) :
    Precision P k (rawNext s x e) ∧
      ∀ i, (i=rightNeighbor e ∨
        min (k+1) (P.cacheOff x i)=min (k+1) (ordinal P.h P.hh i)) →
        min (k+1) (P.cacheOff (rawNext s x e) i)=
          min (k+1) (ordinal P.h P.hh i) := by
  have R := (P.raw_refresh x X e).2.1
  have S : min (k+1) (P.cacheOff (rawNext s x e) (rightNeighbor e))=
      min (k+1) (ordinal P.h P.hh (rightNeighbor e)) := by
    rw [R,ordinal_right]
    by_cases q : P.h (rightNeighbor e)=true
    · simp [q]
    · rw [if_neg q,if_neg q]
      by_cases a : P.h e=true
      · rw [if_pos a,(ordinal_zero P.h P.hh e).mpr a]
        omega
      · rw [if_neg a]
        have z := A e
        omega
  refine ⟨?_,?_⟩
  · intro i
    by_cases E : i=rightNeighbor e
    · subst i
      omega
    · rw [P.off_hold x X e i E]
      exact A i
  · intro i I
    rcases I with E|prior
    · subst i
      exact S
    · by_cases E : i=rightNeighbor e
      · subst i
        exact S
      · rwa [P.off_hold x X e i E]

/-- A whole actual word retains level k and upgrades each responder
    visited on that same word (or correct before the word). -/
theorem Params.offset_word (P : Params s n) (x : Raw s n)
    (X : P.Lower x) (w : List (Fin n)) (k : Nat) (hk : k<3)
    (A : Precision P k x) :
    P.Lower (rawRun x w) ∧ Precision P k (rawRun x w) ∧
      ∀ i, ((∃ e∈w,rightNeighbor e=i) ∨
        min (k+1) (P.cacheOff x i)=min (k+1) (ordinal P.h P.hh i)) →
        min (k+1) (P.cacheOff (rawRun x w) i)=
          min (k+1) (ordinal P.h P.hh i) := by
  induction w generalizing x with
  | nil =>
    refine ⟨X,A,?_⟩
    rintro i (⟨e,he,_⟩|prior)
    · cases he
    · exact prior
  | cons e w ih =>
    obtain ⟨prior,raise⟩ := P.offset_mark x X e k hk A
    obtain ⟨qn,pn,F⟩ := ih (rawNext s x e)
      (P.lowerClosed x e X) prior
    refine ⟨qn,pn,?_⟩
    intro i I
    apply F
    rcases I with ⟨f,hf,eq⟩|already
    · rcases List.mem_cons.mp hf with E|J
      · subst f
        exact .inr (raise i (.inl eq.symm))
      · exact .inl ⟨f,J,eq⟩
    · exact .inr (raise i (.inr already))

theorem Params.offset_cover (P : Params s n) (x : Raw s n)
    (X : P.Lower x) (w : List (Fin n)) (full : ∀ e,e∈w)
    (k : Nat) (hk : k<3) (A : Precision P k x) :
    P.Lower (rawRun x w) ∧ Precision P (k+1) (rawRun x w) := by
  have F := P.offset_word x X w k hk A
  exact ⟨F.1,fun i => F.2.2 i
    (.inl ⟨RearTrace.predecessor i,full _,RearTrace.right_predecessor i⟩)⟩

theorem Params.successor_word (P : Params s n) (x : Raw s n)
    (X : P.Lower x) (w : List (Fin n)) (i : Fin n)
    (A : i∈w ∨ P.cacheSucc x i=P.wantSucc i) :
    P.cacheSucc (rawRun x w) i=P.wantSucc i := by
  induction w generalizing x with
  | nil => exact A.resolve_left List.not_mem_nil
  | cons e w ih =>
    apply ih (rawNext s x e) (P.lowerClosed x e X)
    by_cases E : i=e
    · subst i
      exact .inr (P.raw_refresh x X e).1
    · rcases A with M|prior
      · exact .inl ((List.mem_cons.mp M).resolve_left E)
      · exact .inr ((P.succ_hold x X e i E).trans prior)

/-- Three full physical covers, not covers of compressed roots. -/
theorem Params.cached_from_covers (P : Params s n) (x : Raw s n)
    (X : P.Lower x) (u v w : List (Fin n))
    (U : ∀ e,e∈u) (V : ∀ e,e∈v) (W : ∀ e,e∈w) :
    Cached P (rawRun (rawRun (rawRun x u) v) w) := by
  obtain ⟨q1,A⟩ := P.offset_cover x X u U 0 (by decide)
    (by intro i; simp)
  obtain ⟨q2,B⟩ := P.offset_cover _ q1 v V 1 (by decide) A
  obtain ⟨q3,C⟩ := P.offset_cover _ q2 w W 2 (by decide) B
  refine ⟨q3,fun i=>⟨?_,P.successor_word _ q2 w i (.inl (W i))⟩⟩
  exact (Nat.min_eq_right (P.off_bound _ i)).symm.trans (C i)

/-- All-mark closure of the actual full cache. No separate
    stationary-controller assumption. -/
theorem Params.cached_closed (P : Params s n) (x : Raw s n)
    (e : Fin n) (A : Cached P x) : Cached P (rawNext s x e) := by
  have H : Precision P 2 x := by
    intro i
    rw [(A.2 i).1]
    omega
  have F := P.offset_mark x A.1 e 2 (by decide) H
  refine ⟨P.lowerClosed x e A.1,fun i=>⟨?_,?_⟩⟩
  · have Z : min (2+1) (P.cacheOff x i)=
        min (2+1) (ordinal P.h P.hh i) := by
      rw [(A.2 i).1]
      omega
    exact (Nat.min_eq_right (P.off_bound _ i)).symm.trans
      (F.2 i (.inr Z))
  · by_cases E : i=e
    · subst i
      exact (P.raw_refresh x A.1 e).1
    · exact (P.succ_hold x A.1 e i E).trans (A.2 i).2

/-! Expected cost on the physical alphabet. The three-cover
    observer records every actual mark, and hitting its endpoint
    implies Cached at zero further cost. -/

private theorem raw_word {s n : Nat} (x : Raw s n) (w : List (Fin n)) :
    L4.Height.runWord (rawNext s) x w=rawRun x w := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih => exact ih (rawNext s x e)

private theorem raw_append {s n : Nat} (x : Raw s n) (u v : List (Fin n)) :
    rawRun x (u++v)=rawRun (rawRun x u) v := by
  induction u generalizing x with
  | nil => rfl
  | cons e u ih => exact ih (rawNext s x e)

theorem Params.three_actual_sound (P : Params s n) (x y : Raw s n)
    (X : P.Lower x)
    (H : L4.Height.ThreeCoverClock.ThreeActualCovers (rawNext s) x y) :
    Cached P y := by
  obtain ⟨blocks,L,full,E⟩ := H
  obtain ⟨u,v,w,rfl⟩ : ∃ u v w,blocks=[u,v,w] := by
    cases blocks with
    | nil => cases L
    | cons u blocks =>
      cases blocks with
      | nil => cases L
      | cons v blocks =>
        cases blocks with
        | nil => cases L
        | cons w blocks =>
          cases blocks with
          | nil => exact ⟨u,v,w,rfl⟩
          | cons a blocks => simp at L
  rw [raw_word] at E
  simp only [List.flatten_cons,List.flatten_nil,List.append_nil,raw_append] at E
  exact E ▸ P.cached_from_covers x X u v w
    (full u (by simp)) (full v (by simp)) (full w (by simp))

theorem Params.cached_expected (P : Params s n) (x : Raw s n)
    (X : P.Lower x) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) (Cached P) x (3*n^2) := by
  have H : L4.Height.IIDExpectedHittingTimeAtMost (rawNext s)
      (L4.Height.ThreeCoverClock.ThreeActualCovers (rawNext s) x)
      x (3*n^2) :=
    L4.Height.ThreeCoverClock.three_full_covers_expected _ (by
      have := P.nonself
      omega) x
  have E := (MonitorRawBridge.height_iff_row (rawNext s)
    (L4.Height.ThreeCoverClock.ThreeActualCovers (rawNext s) x)
    x (3*n^2)).mp H
  rw [←Nat.add_zero (3*n^2)]
  apply AllSizeComposition.additive_stage (rawNext s)
    (L4.Height.ThreeCoverClock.ThreeActualCovers (rawNext s) x)
    (Cached P) (3*n^2) 0 x E
  intro y Y t
  have ready := P.three_actual_sound x y X Y
  cases t <;> simp [L4.iidHitCost,ready]

/-! The gate is evaluated on the actual current sheet and the
    frozen *eligibility* mask. It is not a predicate of selection
    from the same sheet. -/

theorem Params.cached_gate (P : Params s n) (x : Raw s n)
    (A : Cached P x) (i : Fin n) (p : Fin 3) :
    MISByteCodec.atGate (P.h i) (P.byte x i) p=true ↔
      p.val=1 ∧ P.h i=true := by
  have E : MISByteCodec.get (P.byte x i) 94 2 (by decide)=P.cacheOff x i := rfl
  have nonzero (H : P.h i=false) : P.cacheOff x i≠0 := by
    rw [(A.2 i).1]
    have B : ordinal P.h P.hh i≠0 :=
      fun Q=>Bool.noConfusion (H.symm.trans ((ordinal_zero P.h P.hh i).mp Q))
    omega
  cases H : P.h i with
  | false =>
    simp only [MISByteCodec.atGate,MISByteCodec.off,Bool.false_eq_true,
      if_false,E]
    simp [nonzero H]
  | true =>
    simp [MISByteCodec.atGate,MISByteCodec.off]

theorem Params.cached_gate_fin (P : Params s n) (x : Raw s n)
    (A : Cached P x) (i : Fin n) (p : Fin 3) :
    MISByteCodec.atGate (P.h i) (P.byte x i) p=true ↔
      p=1 ∧ P.h i=true := by
  rw [P.cached_gate x A i p]
  constructor
  · rintro ⟨J,H⟩
    exact ⟨Fin.ext J,H⟩
  · rintro ⟨J,H⟩
    exact ⟨congrArg Fin.val J,H⟩

theorem Params.cached_gate_actual (P : Params s n) (x : Raw s n)
    (A : Cached P x) (i : Fin n) (p : Fin 3) :
    MISByteCodec.atGate (mask P.sheet x i) (bytes P.sheet (x i)) p=true ↔
      p=1 ∧ mask P.sheet x i=true := by
  rw [P.maskEq x A.1]
  exact P.cached_gate_fin x A i p

/-! Static geometry: one chart uses three consecutive physical
    gaps. No use of 2-or-3 PHYSICAL gap for the higher sheets. -/

theorem Params.gapBounds (P : Params s n) : GapBounds P.h 1 P.B := by
  intro r R
  obtain ⟨d,D,F⟩ := P.gap r R
  exact ⟨d,F.positive,D,F⟩

noncomputable def Params.ring (P : Params s n) :
    ShortNORCover.Ring (ReportStaticSpacing.Lower P.h) :=
  SelectedRingGeometry.ring P.gapBounds P.hh (by
    have := P.room
    omega)

theorem Params.chart_exists (P : Params s n) (r : Fin n) (R : P.h r=true) :
    ∃ C : Chart P.h, C.root=r ∧ C.L≤3*P.B :=
  chart_of_successor_law P.room P.gap r R

private theorem lane_zero_iff (a b k : Nat) :
    lane a b k=0 ↔ k<a := by
  unfold lane
  by_cases A : k<a
  · simp [A]
  · by_cases B : k<a+b <;> simp [A,B]

private theorem lane_one_iff (a b k : Nat) :
    lane a b k=1 ↔ ¬ k<a ∧ k<a+b := by
  unfold lane
  by_cases A : k<a
  · simp [A]
  · by_cases B : k<a+b <;> simp [A,B]

/-- Stronger than an existential gate chart: every chart of this
    frozen mask has its unique real K1 gate at the first successor
    C.a. The arbitrary chart is compared to the three-gap chart
    of its own root, using the checked mask-parametric uniqueness. -/
theorem Params.chart_gate (P : Params s n) (C : Chart P.h) :
    0<C.a ∧ C.a+1<C.L ∧ C.L≤3*P.B ∧
      ∀ x, Cached P x → ∀ k, k<C.L →
        (MISByteCodec.atGate (P.h (nextAt C.root k))
          (P.byte x (nextAt C.root k)) (C.route.port k)=true ↔ k=C.a) := by
  obtain ⟨a,A,F⟩ := P.gap C.root C.rootHeader
  obtain ⟨b,B,G⟩ := P.gap (nextAt C.root a) F.atEnd
  obtain ⟨c,E,H⟩ := P.gap (nextAt (nextAt C.root a) b) G.atEnd
  have ap := F.positive
  have bp := G.positive
  have cp := H.positive
  have room := P.room
  let D : Chart P.h := chart_of_three C.rootHeader F G H (by omega)
  have U := ShortReadCaptureGeometry.chart_unique C D rfl
  have L : C.L=a+b+c := U.1
  have ports (k : Nat) (K : k<C.L) : C.route.port k=lane a b k :=
    U.2 k K
  have one : lane C.a C.b a=1 := by
    have Z := ports a (by omega)
    exact Z.trans (by simp [lane,show a<a+b by omega])
  have zero : lane C.a C.b (a-1)=0 := by
    have Z := ports (a-1) (by omega)
    exact Z.trans (by simp [lane,show a-1<a by omega])
  have q1 := (lane_one_iff C.a C.b a).mp one
  have q0 := (lane_zero_iff C.a C.b (a-1)).mp zero
  have ca : C.a=a := by omega
  refine ⟨by omega,by omega,by omega,?_⟩
  intro x X k K
  rw [P.cached_gate_fin x X _ _,ports k K,ca]
  by_cases Z : k=0
  · subst k
    simp [lane,ap,Nat.ne_of_lt ap]
  · have W := three_gap_exact F G H k (by omega) (by omega)
    rw [W,lane_one_iff]
    omega

/-- Exact existing SheetFiber interface, including its Fin-valued
    port equality. This proves geometry, not RankRows.descent. -/
theorem Params.sheet_fiber (P : Params s n) :
    ShortSheetRankClock.SheetFiber P.sheet P.h (Cached P) (3*P.B) :=
  ⟨P.cached_closed,fun x X => P.maskEq x X.1,
    P.cached_gate_fin,P.chart_exists⟩

/-- Frozen lower-layer conditions are all explicit inputs. -/
def Params.ofGapBounds (j : Sheet) (Q : Raw s n → Prop)
    (closed : AllSizeComposition.Closed (rawNext s) Q)
    (h : Fin n → Bool) (frozen : ∀ x,Q x → mask j x=h)
    (hh : ∃ i,h i=true) (L B : Nat) (G : GapBounds h L B)
    (room : 3*B<n) : Params s n where
  sheet := j
  Lower := Q
  lowerClosed := closed
  h := h
  maskEq := frozen
  hh := hh
  B := B
  room := room
  gap := fun i I => by
    obtain ⟨d,_,U,F⟩ := G i I
    exact ⟨d,U,F⟩

/-- Useful bundle consumed by the next D-parametric stage. -/
structure CacheFacts (P : Params s n) : Prop where
  coldMean : ∀ x,P.Lower x →
    L4.IIDExpectedHittingTimeAtMost (rawNext s) (Cached P) x (3*n^2)
  coldClosed : AllSizeComposition.Closed (rawNext s) (Cached P)
  fiber : ShortSheetRankClock.SheetFiber P.sheet P.h (Cached P) (3*P.B)

theorem Params.cacheFacts (P : Params s n) : CacheFacts P :=
  ⟨P.cached_expected,P.cached_closed,P.sheet_fiber⟩

/-! Concrete instances at the actual lower first-hit anchor.
    For MIS2/MIS3, Q is the prior permanent lower region with
    its actual mask frozen to the anchor. We do not assume
    anything about the current sheet's selected upper output. -/

def mis1Params (x0 : Raw s n) (M : H1.rawMaximal x0) (N : 9<n) :
    Params s n :=
  Params.ofGapBounds .mis1
    (fun x => H1.rawMaximal x ∧ mask .mis1 x=mask .mis1 x0)
    (fun x e X => ⟨H1.raw_h1_maximal_closed (by omega) x e X.1,
      (funext fun i => H1.raw_h1_selected_frozen (by omega) x e i X.1).trans X.2⟩)
    (mask .mis1 x0) (fun _ X=>X.2)
    (SelectedMISLayers.h1_nonempty M (by omega))
    2 3 (SelectedMISLayers.h1_gaps M) (by omega)

def mis2Params (x0 : Raw s n) (M : H1.rawMaximal x0)
    (C1 : SelectedMISLayers.Layer (SelectedMISLayers.h1_gaps M)
      (SelectedMISLayers.h2 x0))
    (Q : Raw s n → Prop) (closed : AllSizeComposition.Closed (rawNext s) Q)
    (frozen : ∀ x,Q x → mask .mis2 x=mask .mis2 x0)
    (N : 27<n) : Params s n :=
  Params.ofGapBounds .mis2 Q closed (mask .mis2 x0) frozen
    (SelectedMISLayers.layer_nonempty C1
      (SelectedMISLayers.h1_nonempty M (by omega)))
    4 9 (SelectedMISLayers.h2_gaps C1) (by omega)

def mis3Params (x0 : Raw s n) (M : H1.rawMaximal x0)
    (C1 : SelectedMISLayers.Layer (SelectedMISLayers.h1_gaps M)
      (SelectedMISLayers.h2 x0))
    (C2 : SelectedMISLayers.Layer (SelectedMISLayers.h2_gaps C1)
      (SelectedMISLayers.h3 x0))
    (Q : Raw s n → Prop) (closed : AllSizeComposition.Closed (rawNext s) Q)
    (frozen : ∀ x,Q x → mask .mis3 x=mask .mis3 x0)
    (N : 81<n) : Params s n :=
  Params.ofGapBounds .mis3 Q closed (mask .mis3 x0) frozen
    (SelectedMISLayers.layer_nonempty C2
      (SelectedMISLayers.layer_nonempty C1
        (SelectedMISLayers.h1_nonempty M (by omega))))
    8 27 (SelectedMISLayers.h3_gaps C2) (by omega)

/-- Regression: the new MIS1 certificate on a fixed H1 fibre
    is exactly the old H2Ready, intersected with that same fibre. -/
theorem mis1_cached_iff (x0 x : Raw s n)
    (M : H1.rawMaximal x0) (N : 9<n) :
    Cached (mis1Params x0 M N) x ↔
      H2Ready x ∧ mask .mis1 x=mask .mis1 x0 := by
  let P := mis1Params x0 M N
  let cert := fun h' : Fin n → Bool =>
    ∃ hh' : ∃ i,h' i=true,
      ∀ i,AllSizeS1Geometry.off (x i)=min 3 (ordinal h' hh' i) ∧
        AllSizeS1Geometry.successor (x i)=
          BitVec.ofNat 1 (h' (rightNeighbor i)).toNat
  constructor
  · intro A
    have E : (fun i=>AllSizeS1Geometry.header (x i))=P.h := A.1.2
    have F : cert P.h := ⟨P.hh,A.2⟩
    exact ⟨⟨A.1.1,(congrArg cert E).mpr F⟩,A.1.2⟩
  · rintro ⟨H,E⟩
    have E' : (fun i=>AllSizeS1Geometry.header (x i))=P.h := E
    have G : cert (fun i=>AllSizeS1Geometry.header (x i)) := H.2
    obtain ⟨hh,F⟩ := (congrArg cert E').mp G
    -- CHECK: PhysicalCustodyH2Ready.lean:10–13,
    -- AllSizeS1Geometry.lean:26–28, PhysicalShortSheet.lean:10–19,38.
    -- Proof irrelevance identifies hh with P.hh; the raw field
    -- definitions are the literal MIS1 byte reads.
    exact ⟨⟨H.1,E⟩,F⟩

theorem mis1_cache (x0 : Raw s n) (M : H1.rawMaximal x0)
    (N : 9<n) :
    CacheFacts (mis1Params x0 M N) :=
  (mis1Params x0 M N).cacheFacts

theorem mis2_cache (x0 : Raw s n) (M : H1.rawMaximal x0)
    (C1 : SelectedMISLayers.Layer (SelectedMISLayers.h1_gaps M)
      (SelectedMISLayers.h2 x0))
    (Q : Raw s n → Prop) (closed : AllSizeComposition.Closed (rawNext s) Q)
    (frozen : ∀ x,Q x → mask .mis2 x=mask .mis2 x0)
    (N : 27<n) :
    CacheFacts (mis2Params x0 M C1 Q closed frozen N) :=
  (mis2Params x0 M C1 Q closed frozen N).cacheFacts

theorem mis3_cache (x0 : Raw s n) (M : H1.rawMaximal x0)
    (C1 : SelectedMISLayers.Layer (SelectedMISLayers.h1_gaps M)
      (SelectedMISLayers.h2 x0))
    (C2 : SelectedMISLayers.Layer (SelectedMISLayers.h2_gaps C1)
      (SelectedMISLayers.h3 x0))
    (Q : Raw s n → Prop) (closed : AllSizeComposition.Closed (rawNext s) Q)
    (frozen : ∀ x,Q x → mask .mis3 x=mask .mis3 x0)
    (N : 81<n) :
    CacheFacts (mis3Params x0 M C1 C2 Q closed frozen N) :=
  (mis3Params x0 M C1 C2 Q closed frozen N).cacheFacts

/-- Explicit D=9 regression; no rank-row hypothesis needed. -/
theorem mis1_fiber (x0 : Raw s n) (M : H1.rawMaximal x0)
    (N : 9<n) :
    ShortSheetRankClock.SheetFiber .mis1 (mask .mis1 x0)
      (Cached (mis1Params x0 M N)) 9 :=
  (mis1Params x0 M N).sheet_fiber

theorem mis2_fiber (x0 : Raw s n) (M : H1.rawMaximal x0)
    (C1 : SelectedMISLayers.Layer (SelectedMISLayers.h1_gaps M)
      (SelectedMISLayers.h2 x0))
    (Q : Raw s n → Prop) (closed : AllSizeComposition.Closed (rawNext s) Q)
    (frozen : ∀ x,Q x → mask .mis2 x=mask .mis2 x0)
    (N : 27<n) :
    ShortSheetRankClock.SheetFiber .mis2 (mask .mis2 x0)
      (Cached (mis2Params x0 M C1 Q closed frozen N)) 27 :=
  (mis2Params x0 M C1 Q closed frozen N).sheet_fiber

theorem mis3_fiber (x0 : Raw s n) (M : H1.rawMaximal x0)
    (C1 : SelectedMISLayers.Layer (SelectedMISLayers.h1_gaps M)
      (SelectedMISLayers.h2 x0))
    (C2 : SelectedMISLayers.Layer (SelectedMISLayers.h2_gaps C1)
      (SelectedMISLayers.h3 x0))
    (Q : Raw s n → Prop) (closed : AllSizeComposition.Closed (rawNext s) Q)
    (frozen : ∀ x,Q x → mask .mis3 x=mask .mis3 x0)
    (N : 81<n) :
    ShortSheetRankClock.SheetFiber .mis3 (mask .mis3 x0)
      (Cached (mis3Params x0 M C1 C2 Q closed frozen N)) 81 :=
  (mis3Params x0 M C1 C2 Q closed frozen N).sheet_fiber

/-- Production room for all three instances and the later five-chart
    phase. This is independent of the cache induction. -/
theorem production_rooms (S : 6≤s) (advice : s=ell (ell n)) :
    7*3<n ∧ 7*9<n ∧ 7*27<n :=
  ⟨ProductionShortRoom.seven_gaps_fit S advice (by decide),
    ProductionShortRoom.seven_gaps_fit S advice (by decide),
    ProductionShortRoom.seven_gaps_fit S advice (by decide)⟩

end L4.ShortMISEngine
