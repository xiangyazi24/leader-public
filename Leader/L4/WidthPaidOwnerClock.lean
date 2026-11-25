import Leader.L4.WidthCycleEpoch
import Leader.L4.WidthAbsorbingMax
import Leader.L4.WidthPackTiming
import Leader.L4.AdviceBandRadiusBudget

namespace L4.WidthCycleEpoch
open AllSizeProtocol PhysicalCustody
open BStarH6WordChart (oldH6)
open BStarH6Ordinal WidthSectorGeometry ShortResetChart WidthFreshForward WidthChooseEpoch
open WidthPackJoint
open AdviceBandRadiusBudget (widthMax)
variable {s n d : Nat} {h : Fin n → Bool}

private theorem raw_append (x : Raw s n) (u v : List (Fin n)) :
    rawRun x (u++v)=rawRun (rawRun x u) v := by
  induction u generalizing x with
  | nil => rfl
  | cons e u ih => exact ih (rawNext s x e)

private theorem raw_snoc (x : Raw s n) (u : List (Fin n)) (e : Fin n) :
    rawRun x (u++[e])=rawNext s (rawRun x u) e :=
  raw_append x u [e]

private theorem raw_clock (x : Raw s n) (w : List (Fin n)) :
    SequentialMarkClock.run (rawNext s) x w=rawRun x w := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih => exact ih (rawNext s x e)

/-! Concrete frozen owner family. Choose it ONCE at the lower cut,
    before cache service. No later raw mask or receipt changes the family. -/

open WidthPackJoint (Header SiteInOwnerWord OwnerWordFlagsCorrect)
open AdviceBandRadiusBudget (widthMax)

structure OwnerFamily (P : WidthLower s n) where
  d : Header P.h→Nat
  sector : ∀ q, Sector P.h (d q)
  root : ∀ q,(sector q).root=q.val
  upper : ∀ q,d q+1≤widthMax s

theorem sector_exists (P : WidthLower s n) (hs : 6≤s)
    (advice : s=ell (ell n)) (x : Raw s n) (X : P.Q x)
    (q : Header P.h) :
    ∃ d,∃ S : Sector P.h d,S.root=q.val ∧ d+1≤widthMax s := by
  have M : oldH6 (rows s) x=P.h := funext (P.frozen x X)
  have G := P.spacing x X
  unfold WidthPackedBridge.CertifiedSpacing at G
  rw [M] at G
  obtain ⟨l,_,U,F⟩ := G q.val q.property
  have pos := F.positive
  have room := ProductionH6Count.three_gaps_fit hs advice
  have W : l<n := by omega
  let d := l-1
  have E : d+1=l := by omega
  refine ⟨d,⟨q.val,q.property,?_,?_⟩,rfl,?_⟩
  · rw [E]
    exact F
  · rw [E]
    exact W
  · rw [E]
    exact U

noncomputable def family_of_lower (P : WidthLower s n) (hs : 6≤s)
    (advice : s=ell (ell n)) (x : Raw s n) (X : P.Q x) :
    OwnerFamily P := by
  classical
  let H := fun q=>sector_exists P hs advice x X q
  let d := fun q=>Classical.choose (H q)
  let S := fun q=>Classical.choose (Classical.choose_spec (H q))
  exact ⟨d,S,fun q=>(Classical.choose_spec (Classical.choose_spec (H q))).1,
    fun q=>(Classical.choose_spec (Classical.choose_spec (H q))).2⟩

def OwnerGood (P : WidthLower s n) (F : OwnerFamily P)
    (q : Header P.h) : Raw s n→Prop :=
  WidthGood P (F.sector q)

theorem owner_good_closed (P : WidthLower s n) (F : OwnerFamily P)
    (q : Header P.h) (y : Raw s n) (e : Fin n) (Y : OwnerGood P F q y) :
    OwnerGood P F q (rawNext s y e) :=
  width_good_step P (F.sector q) y e Y

/-- WordData's IN/LAST are exactly the production longGeometry
    readouts, not cache fields and not a synthetic Layout. -/
theorem flags_at_site (S : Sector h d) (x : Raw s n) (i : Fin (d+1)) :
    (longGeometry (rows s) (x (site S i))).inside =
      ((wordData S x i).inside.toNat==1) ∧
    (longGeometry (rows s) (x (site S i))).last =
      ((wordData S x i).last.toNat==1) := by
  -- CHECK: AllSizeProtocol.lean:739-741; production
  -- widthInside/widthLast use WidthByteRows.inside/last at suffix 3/4.
  -- BStarWidthTransferDepart.lean:7-23 and
  -- WidthByteRows.lean:18-19. Both equalities are literal field reads.
  exact ⟨rfl,rfl⟩

theorem owner_good_flags (P : WidthLower s n) (F : OwnerFamily P)
    (hs : 6≤s)
    (q : Header P.h) (y : Raw s n) (Y : OwnerGood P F q y) :
    OwnerWordFlagsCorrect P.h P.hh q y := by
  intro i I
  obtain ⟨l,j,G,J,E⟩ := I
  have G' : ShortLayerGeometry.Gap P.h q.val (F.d q+1) := by
    rw [←F.root q]
    exact (F.sector q).gap
  have L := WidthOrdinalSpan.gap_unique G G'
  let k : Fin (F.d q+1) := ⟨j,by omega⟩
  have R : site (F.sector q) k=i := by
    unfold site
    rw [F.root q]
    exact E
  have O : ordinal P.h P.hh i=j := by
    rw [←E]
    exact WidthPackJoint.ordinal_of_gap P.hh q G J
  have H := (width_good_flags P (F.sector q) hs y Y).2 k
  have K := flags_at_site (F.sector q) y k
  rw [R] at K
  rw [O,K.1,K.2,H.1,H.2.1]
  have V : k.val=j := rfl
  rw [V]
  constructor <;> simp [bit] <;> split <;> simp_all

/-! The actual prefix receipt has a start on this SAME tape; it is
    never synthesized from a new raw state or a bare terminal flag. -/

def PaidReceipt (P : WidthLower s n) (F : OwnerFamily P)
    (x : Raw s n) (q : Header P.h) (u : List (Fin n)) : Prop :=
  ∃ a b : List (Fin n),u=a++b ∧
    CycleReceipt P (F.sector q) ⟨rawRun x a,a⟩ ⟨rawRun x u,u⟩

theorem receipt_credit (P : WidthLower s n) (F : OwnerFamily P)
    (hs : 6≤s)
    (x : Raw s n) (q : Header P.h) (u : List (Fin n))
    (R : PaidReceipt P F x q u) :
    OwnerGood P F q (SequentialMarkClock.run (rawNext s) x u) := by
  obtain ⟨a,b,_,R⟩ := R
  rw [raw_clock]
  exact cut_good P (F.sector q) _ (cycle_cut P (F.sector q) hs _ _ R)

def PaidAt (P : WidthLower s n) (F : OwnerFamily P)
    (x : Raw s n) (q : Header P.h) (z : Tape s n) : Prop :=
  ∃ u v : List (Fin n), z.marks=u++v ∧ PaidReceipt P F x q u

theorem paid_closed (P : WidthLower s n) (F : OwnerFamily P)
    (x : Raw s n) (q : Header P.h) (z : Tape s n) (e : Fin n)
    (Z : PaidAt P F x q z) : PaidAt P F x q (tapeStep z e) := by
  obtain ⟨u,v,E,R⟩ := Z
  exact ⟨u,v++[e],by change z.marks++[e]=_; rw [E,List.append_assoc],R⟩

def Anchored (P : WidthLower s n) (x : Raw s n) (z : Tape s n) : Prop :=
  P.Post z.raw ∧ z.raw=rawRun x z.marks

theorem anchored_closed (P : WidthLower s n) (N : 1<n)
    (x : Raw s n) (z : Tape s n) (e : Fin n) (Z : Anchored P x z) :
    Anchored P x (tapeStep z e) := by
  refine ⟨P.post_closed N z.raw Z.1 e,?_⟩
  change rawNext s z.raw e=rawRun x (z.marks++[e])
  rw [raw_snoc,Z.2]

theorem cycle_pays (P : WidthLower s n) (F : OwnerFamily P)
    (x : Raw s n) (q : Header P.h) (z y : Tape s n)
    (Z : Anchored P x z) (R : CycleReceipt P (F.sector q) z y) :
    PaidAt P F x q y := by
  obtain ⟨w,E,Y⟩ := cycle_extension P (F.sector q) z y R
  have A : y.raw=rawRun x y.marks := by rw [Y,Z.2,E,raw_append]
  have Z' : (⟨rawRun x z.marks,z.marks⟩ : Tape s n)=z := by
    cases z
    simp_all [Anchored]
  have Y' : (⟨rawRun x y.marks,y.marks⟩ : Tape s n)=y := by
    cases y
    simp_all
  refine ⟨y.marks,[],by simp,z.marks,w,E,?_⟩
  rw [Z',Y']
  exact R

/-- Uniform owner mean on all reachable stopped states of this
    single history monitor. Starting a proof of a future receipt
    does not clear an earlier actual paid receipt. -/
theorem paid_owner_mean (P : WidthLower s n) (F : OwnerFamily P)
    (C : ∀ q,Predecessor P (F.sector q)) (hs : 6≤s)
    (x : Raw s n) (q : Header P.h) (z : Tape s n) (Z : Anchored P x z) :
    L4.IIDExpectedHittingTimeAtMost tapeStep (PaidAt P F x q)
      z (20*n*(widthMax s+1)^2) := by
  have H := owner_cycle_mean P (F.sector q) (C q) hs z Z.1
  have B : 20*n*(F.d q+2)^2≤20*n*(widthMax s+1)^2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by have := F.upper q; omega) 2)
  intro t
  exact Nat.le_trans (RankRenewal.cost_mono_target (next:=tapeStep)
    (CycleReceipt P (F.sector q) z) (PaidAt P F x q)
    (fun y R=>cycle_pays P F x q z y Z R) t z)
    (Nat.le_trans (H t) (Nat.mul_le_mul_right _ B))

/-- A total family indexed by the actual n physical sites, with
    nonheaders vacuously paid. This gives the exact union factor ≤n
    without requiring Fintype or an independent scheduler. -/
def PaidIndex (P : WidthLower s n) (F : OwnerFamily P) (x : Raw s n)
    (i : Fin n) (z : Tape s n) : Prop :=
  ∀ H : P.h i=true,PaidAt P F x ⟨i,H⟩ z

theorem paid_index_closed (P : WidthLower s n) (F : OwnerFamily P)
    (x : Raw s n) (i : Fin n) (z : Tape s n) (e : Fin n)
    (Z : PaidIndex P F x i z) : PaidIndex P F x i (tapeStep z e) := by
  intro H
  exact paid_closed P F x ⟨i,H⟩ z e (Z H)

theorem paid_index_mean (P : WidthLower s n) (F : OwnerFamily P)
    (C : ∀ q,Predecessor P (F.sector q)) (hs : 6≤s)
    (x : Raw s n) (i : Fin n) (z : Tape s n) (Z : Anchored P x z) :
    L4.IIDExpectedHittingTimeAtMost tapeStep (PaidIndex P F x i)
      z (20*n*(widthMax s+1)^2) := by
  by_cases H : P.h i=true
  · have B := paid_owner_mean P F C hs x ⟨i,H⟩ z Z
    intro t
    exact Nat.le_trans (RankRenewal.cost_mono_target (next:=tapeStep)
      (PaidAt P F x ⟨i,H⟩) (PaidIndex P F x i)
      (fun y Y I=>by
        have E : (⟨i,H⟩ : Header P.h)=⟨i,I⟩ := rfl
        exact E ▸ Y) t z) (B t)
  · intro t
    have E : PaidIndex P F x i z := fun I=>False.elim (H I)
    rw [L4.iidHitCost_of_target tapeStep _ z E t]
    exact Nat.zero_le _

def PaidDone (P : WidthLower s n) (F : OwnerFamily P)
    (x : Raw s n) : Tape s n→Prop :=
  AbsorbingMax.All (PaidIndex P F x)

theorem paid_max_mean (P : WidthLower s n) (F : OwnerFamily P)
    (C : ∀ q,Predecessor P (F.sector q)) (hs : 6≤s)
    (advice : s=ell (ell n)) (N : 1<n)
    (x : Raw s n) (X : P.Post x) :
    L4.IIDExpectedHittingTimeAtMost tapeStep (PaidDone P F x)
      (tapeStart x) (5120*n^2) := by
  let mu := 20*n*(widthMax s+1)^2
  have pos : 0<mu := Nat.mul_pos (by omega : 0<20*n)
    (Nat.pow_pos (by omega : 0<widthMax s+1))
  have V := AbsorbingMax.expected tapeStep (Anchored P x)
    (anchored_closed P N x) (PaidIndex P F x) (paid_index_closed P F x)
    mu pos (paid_index_mean P F C hs x) (ell n) (power_of_ell n)
    (tapeStart x) ⟨X,rfl⟩
  have B : (2*mu)*(ell n+2)≤5120*n^2 := by
    change (2*(20*n*(widthMax s+1)^2))*(ell n+2)≤_
    rw [←Nat.mul_assoc,←Nat.mul_assoc,show 2*20=40 by decide]
    exact AdviceBandRadiusBudget.width_stage_budget advice hs
  intro t
  exact Nat.le_trans (V t) (Nat.mul_le_mul_right _ B)

theorem paid_terminal (P : WidthLower s n) (F : OwnerFamily P)
    (x : Raw s n) (w : List (Fin n))
    (D : PaidDone P F x (SequentialMarkClock.run tapeStep (tapeStart x) w)) :
    ∀ q : Header P.h,∃ u v,w=u++v ∧ PaidReceipt P F x q u := by
  rw [tape_run] at D
  intro q
  have H := D q.val q.property
  obtain ⟨u,v,E,R⟩ := H
  exact ⟨u,v,by simpa [tapeStart] using E,R⟩

/-- This is the ACTUAL checked interface consumed by WidthPackTiming,
    not another abstract all-owner monitor specification. -/
def paidOwnerMonitor (P : WidthLower s n) (F : OwnerFamily P)
    (C : ∀ q,Predecessor P (F.sector q)) (hs : 6≤s)
    (advice : s=ell (ell n)) (N : 1<n)
    (x : Raw s n) (X : P.Post x) :
    WidthPackTiming.PaidOwnerMonitor P.h (OwnerGood P F) x where
  State := Tape s n
  step := tapeStep
  project := Tape.raw
  start := tapeStart x
  base := rfl
  step_project := tape_project
  done := PaidDone P F x
  Receipt := PaidReceipt P F x
  credit := receipt_credit P F hs x
  terminal := paid_terminal P F x
  price := (MonitorRawBridge.height_iff_row _ _ _ _).mpr
    (paid_max_mean P F C hs advice N x X)

/-- Same original physical process, including the checked cold cache.
    The fixed family is selected at the preceding permanent H6 cut.
    This proves W17.3/7 conditional on only the predecessor interfaces. -/
theorem width_packed_stage_expected (P : WidthLower s n) (F : OwnerFamily P)
    (C : ∀ q,Predecessor P (F.sector q))
    (hs : 6≤s) (advice : s=ell (ell n)) (N : 1<n)
    (x : Raw s n) (X : P.Q x) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s)
      (fun z=>Nonempty (PackedFiber z)) x ((s+5132)*n^2) :=
  WidthPackTiming.width_packed_stage_expected hs N
    P.Q P.h P.hh P.closed P.frozen P.spacing (OwnerGood P F)
    (owner_good_closed P F) (owner_good_flags P F hs)
    (fun y Y=>⟨paidOwnerMonitor P F C hs advice N y Y⟩) x X

theorem width_packed_of_predecessors (P : WidthLower s n)
    (C : ∀ (d : Nat) (S : Sector P.h d),Predecessor P S)
    (hs : 6≤s) (advice : s=ell (ell n)) (N : 1<n)
    (x : Raw s n) (X : P.Q x) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s)
      (fun z=>Nonempty (PackedFiber z)) x ((s+5132)*n^2) := by
  let F := family_of_lower P hs advice x X
  exact width_packed_stage_expected P F (fun q=>C _ (F.sector q))
    hs advice N x X

end L4.WidthCycleEpoch

