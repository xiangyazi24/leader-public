import Leader.L4.BStarCopyRightChartGeometry
import Leader.L4.BStarFenceOccupancy

namespace L4.BStarFenceLineGeometry
open AllSizeProtocol BStarTrace BStarLongClaims BStarH6WordChart BStarH6Ordinal
open BStarLongFiberOwner BStarClearanceDataChart BStarAcquireAnchors
open BStarCopyRightStrip (addr addr_next addr_inj address_ordinal_run)

/-- A direction is on typed site/sheet addresses: if the two streams
share a raw edge, that does not identify their cells. -/
def rightRail (d j : Nat) : Sheet := if j<d then .rd else .rs

def rightPos {n : Nat} (root : Fin n) (d j : Nat) : Fin n × Sheet :=
  (addr root j,rightRail d j)

private theorem zero {n : Nat} (a : Fin n) : addr a 0=a :=
  Fin.ext (Nat.mod_eq_of_lt a.isLt)

private theorem addr_add {n : Nat} (a : Fin n) (i j : Nat) :
    addr (addr a i) j=addr a (i+j) := by
  apply Fin.ext
  change ((a.val+i)%n+j)%n=(a.val+(i+j))%n
  rw [Nat.mod_add_mod,Nat.add_assoc]

/-- The extra RD run precedes the old strict-strip head. Express the
entire chart in clockwise coordinates, then run packets from large
indices to small ones. The formulas agree at the shared RD occurrence. -/
theorem glue {n : Nat} (root : Fin n) {r seam j : Nat}
    (Q : r-1≤j) :
    rightPos root (r-1+seam) j =
      (addr (addr root (r-1)) (j-(r-1)), BStarCopyRightStrip.rail seam (j-(r-1))) := by
  apply Prod.ext
  · change addr root j=addr (addr root (r-1)) (j-(r-1))
    rw [addr_add,show r-1+(j-(r-1))=j by omega]
  · have E : j<r-1+seam ↔ j-(r-1)<seam := by omega
    simp [rightPos,rightRail,BStarCopyRightStrip.rail,E]

private theorem add_inj {n : Nat} (root : Fin n) (off i j : Nat)
    (a : i<n) (b : j<n)
    (E : addr root (off+i)=addr root (off+j)) : i=j := by
  rw [←addr_add,←addr_add] at E
  exact addr_inj (addr root off) a b E

theorem right_injective {n : Nat} (root : Fin n) {d r i j : Nat}
    (hd : d≤n) (hr : r≤n) (hi : i<d+r) (hj : j<d+r)
    (E : rightPos root d i=rightPos root d j) : i=j := by
  have T := congrArg Prod.snd E
  have U := congrArg Prod.fst E
  change addr root i=addr root j at U
  by_cases I : i<d <;> by_cases J : j<d
  · exact addr_inj root (by omega) (by omega) U
  · simp [rightPos,rightRail,I,J] at T
  · simp [rightPos,rightRail,I,J] at T
  · have F : addr root (d+(i-d))=addr root (d+(j-d)) := by
      rwa [show d+(i-d)=i by omega,show d+(j-d)=j by omega]
    have Z := add_inj root d (i-d) (j-d) (by omega) (by omega) F
    omega

private def geo (hh i l : Bool) : LongGeometry :=
  ⟨⟨false,false,false,false,false,hh⟩,i,l,0,false⟩

/-- There is no arbitration loss without a prep reservation. The
enumeration exhausts the four old-bit coordinates of the data rows. -/
theorem nominal_iff_raw (g : Pair LongGeometry) (D : DataClaim) :
    D∈orderedData g [] ↔ D∈dataClaims g := by
  constructor
  · exact BStarLongFenceTopology.selected_data_raw g [] D
  · obtain ⟨x,y⟩ := g
    change D∈dataClaims (geo false x.inside x.last,geo y.axes.h6 y.inside false) →
      D∈orderedData (geo false x.inside x.last,geo y.axes.h6 y.inside false) []
    have F (a b c d : Bool) :
        (dataClaims (geo false a b,geo c d false)).all
          (fun k => decide (k∈orderedData (geo false a b,geo c d false) []))=true := by
      cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel
    intro K
    exact of_decide_eq_true (List.all_eq_true.mp (F _ _ _ _) D K)

/-- The fixed lower fibre freezes all nominal data footprints. The
actual offer may still be suppressed by a prep, which is why the
separate old-pc 11 proof is needed. -/
theorem data_eq {p : LargeParams} {n : Nat} (b : LargeRows p)
    (x y : Fin n → LargeSite p)
    (same : ∀ i,BStarLongFixedRouting.Layout b x i=BStarLongFixedRouting.Layout b y i)
    (e : Fin n) : orderedData (oldPair b x e) []=orderedData (oldPair b y e) [] := by
  let u := oldPair b x e
  let v := oldPair b y e
  have l := same e
  have r := same (rightNeighbor e)
  change (u.1.axes.h6,u.1.inside,u.1.last)=(v.1.axes.h6,v.1.inside,v.1.last) at l
  change (u.2.axes.h6,u.2.inside,u.2.last)=(v.2.axes.h6,v.2.inside,v.2.last) at r
  have LI : u.1.inside=v.1.inside := congrArg (fun z : Bool × Bool × Bool => z.2.1) l
  have LL : u.1.last=v.1.last := congrArg (fun z : Bool × Bool × Bool => z.2.2) l
  have RH : u.2.axes.h6=v.2.axes.h6 := congrArg Prod.fst r
  have RI : u.2.inside=v.2.inside := congrArg (fun z : Bool × Bool × Bool => z.2.1) r
  change select Claim.slots [] (offers dataKey (dataClaims u))=
    select Claim.slots [] (offers dataKey (dataClaims v))
  rw [show dataClaims u=dataClaims (geo false u.1.inside u.1.last,geo u.2.axes.h6 u.2.inside false) from rfl,
    show dataClaims v=dataClaims (geo false v.1.inside v.1.last,geo v.2.axes.h6 v.2.inside false) from rfl,
    LI,LL,RH,RI]

structure RightFrame {p : LargeParams} {n : Nat} (b : LargeRows p)
    (x : Fin n → LargeSite p) (root : Fin n) (d r : Nat) : Prop where
  word_bound : d≤n
  width_bound : r≤n
  width_pos : 0<r
  terminal_header : oldH6 b x root=true
  first_header : oldH6 b x (addr root d)=true
  body : ∀ j, 0<j → j<d → oldH6 b x (addr root j)=false
  adjacent : ∀ j, j+1<d+r →
    hop (R (rightRail d (j+1))) (L (rightRail d j)) ∈ orderedData (oldPair b x (addr root j)) []

/-- Prepend the r-1 earlier RD sites before the strict strip.
The old strip coordinate 0 is preserved once, not duplicated. -/
theorem right_extend {p : LargeParams} {n : Nat} {b : LargeRows p}
    {x : Fin n → LargeSite p} {root : Fin n} {r seam tail : Nat}
    (D : BStarCopyRightRetained.Dest b x root r)
    (C : BStarCopyRightStrip.Strip b x (addr root (r-1)) seam tail)
    (len : tail+1=seam+r) :
    RightFrame b x root (r-1+seam) r := by
  let d := r-1+seam
  have hd : d=tail := by have := D.pos; dsimp [d]; omega
  have rs : oldH6 b x (addr root d)=true := by
    dsimp [d]
    rw [←addr_add]; exact C.rs_header
  have body (j : Nat) (P : 0<j) (J : j<d) : oldH6 b x (addr root j)=false := by
    by_cases H : j<r
    · exact D.body j P H
    · have F := C.rd_noheader (j-(r-1)) (by dsimp [d] at J; omega)
      rw [addr_add,show r-1+(j-(r-1))=j by omega] at F
      exact F
  have rootH := D.header
  rw [zero] at rootH
  refine ⟨by change d≤n; rw [hd]; exact Nat.le_of_lt C.tail_lt,D.fit,D.pos,rootH,rs,body,?_⟩
  intro j J
  apply (nominal_iff_raw _ _).mpr
  by_cases H : j<r-1
  · have ds : r-1<d := by have := C.seam_pos; dsimp [d]; omega
    have A : rightRail d j=.rd := if_pos (by change j<d; omega)
    have B : rightRail d (j+1)=.rd := if_pos (by change j+1<d; omega)
    rw [A,B]
    apply (BStarCopyRightStrip.raw_rd_send_body _ _ _ rfl).mpr rfl
    change oldH6 b x (rightNeighbor (addr root j))=false
    rw [←addr_next]
    exact D.body _ (by omega) (by omega)
  · have J' : j-(r-1)<tail := by have := D.pos; change j+1<d+r at J; dsimp [d] at J; omega
    have E : addr (addr root (r-1)) (j-(r-1))=addr root j := by
      rw [addr_add,show r-1+(j-(r-1))=j by omega]
    have A := congrArg Prod.snd (glue root (r:=r) (seam:=seam) (j:=j) (by omega))
    have B := congrArg Prod.snd (glue root (r:=r) (seam:=seam) (j:=j+1) (by omega))
    change rightRail d j=BStarCopyRightStrip.rail seam (j-(r-1)) at A
    change rightRail d (j+1)=BStarCopyRightStrip.rail seam (j+1-(r-1)) at B
    rw [A,B,show j+1-(r-1)=(j-(r-1))+1 by omega,←E]
    exact (BStarCopyRightStrip.raw_incoming C _ J' _ rfl).mpr rfl

theorem right_terminal {p : LargeParams} {n : Nat} {b : LargeRows p}
    {x : Fin n → LargeSite p} {root : Fin n} {d r : Nat}
    (F : RightFrame b x root d r) :
    ending (R .rd)∈orderedData (oldPair b x (RearTrace.predecessor root)) [] := by
  apply (nominal_iff_raw _ _).mpr
  let e := RearTrace.predecessor root
  have H : (oldPair b x e).2.axes.h6=true := by
    change oldH6 b x (rightNeighbor e)=true
    rw [RearTrace.right_predecessor]
    exact F.terminal_header
  change ending (R .rd)∈dataClaims (oldPair b x e)
  simp [dataClaims,H]

theorem right_width {p : LargeParams} {n : Nat} {b : LargeRows p}
    {x : Fin n → LargeSite p} {root : Fin n} {d r W : Nat}
    (F : RightFrame b x root d r) (hh : ∃ i,oldH6 b x i=true)
    (hd : 0<d) (hr : r≤W)
    (cap : ∀ i,oldH6 b x (rightNeighbor i)=true → oldOrdinal b x hh i+1≤W) :
    d+r≤2*W := by
  let h := oldH6 b x
  have C := address_ordinal_run root h hh 0 (d-1)
    (fun j P J => by rw [Nat.zero_add]; exact F.body j P (by omega)) (d-1) (Nat.le_refl _)
  have K := (ordinal_zero h hh root).mpr F.terminal_header
  rw [Nat.zero_add,zero,K,Nat.zero_add] at C
  have Z : h (rightNeighbor (addr root (d-1)))=true := by
    rw [←addr_next,show d-1+1=d by omega]
    exact F.first_header
  have O := cap _ Z
  change ordinal h hh (addr root (d-1))+1≤W at O
  omega

theorem left_adjacent {p : LargeParams} {n : Nat} {b : LargeRows p}
    {x : Fin n → LargeSite p} {root : Fin n} {d r : Nat}
    (F : BStarCopyLeftStrip.Strip b x root d r) (j : Nat) (J : j+1<d+r) :
    hop (L (BStarCopyLeftStrip.rail d j)) (R (BStarCopyLeftStrip.rail d (j+1))) ∈
      orderedData (oldPair b x (addr root j)) [] := by
  apply (nominal_iff_raw _ _).mpr
  exact (BStarCopyLeftStrip.raw_hop F j J _ rfl).mpr rfl

theorem left_terminal {p : LargeParams} {n : Nat} {b : LargeRows p}
    {x : Fin n → LargeSite p} {root : Fin n} {d r : Nat}
    (F : BStarCopyLeftStrip.Strip b x root d r) :
    ending (L .ld)∈orderedData (oldPair b x (addr root (d+r-1))) [] := by
  apply (nominal_iff_raw _ _).mpr
  exact (BStarCopyLeftStrip.raw_ld_terminal _ _ F.last rfl).mpr rfl

theorem left_width {p : LargeParams} {n : Nat} {b : LargeRows p}
    {x : Fin n → LargeSite p} {root : Fin n} {d r W : Nat}
    (F : BStarCopyLeftStrip.Strip b x root d r) (hh : ∃ i,oldH6 b x i=true)
    (hr : r≤W)
    (cap : ∀ i,oldH6 b x (rightNeighbor i)=true → oldOrdinal b x hh i+1≤W) :
    d+r≤2*W := by
  let h := oldH6 b x
  have pos := F.seam_pos
  have C := address_ordinal_run root h hh 0 (d-1)
    (fun j P J => by rw [Nat.zero_add]; exact F.ls_body j P (by omega)) (d-1) (Nat.le_refl _)
  have K := (ordinal_zero h hh root).mpr F.source_header
  rw [Nat.zero_add,zero,K,Nat.zero_add] at C
  have Z : h (rightNeighbor (addr root (d-1)))=true := by
    rw [←addr_next,show d-1+1=d by omega]
    exact F.dest_header
  have O := cap _ Z
  change ordinal h hh (addr root (d-1))+1≤W at O
  omega

/-- All typed addresses on the full right line have the terminal's
owner. No label from another owner is identified with this lane. -/
theorem right_owner {p : LargeParams} {n : Nat} {b : LargeRows p}
    {x : Fin n → LargeSite p} {root : Fin n} {d r : Nat}
    (F : RightFrame b x root d r) (hd : 0<d) :
    ∀ j, j<d+r → dataOwner (oldH6 b x) (addr root j) (rightRail d j) =
      commandOwner (oldH6 b x) root 10 := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [zero,show rightRail d 0=.rd from if_pos hd]
    rfl
  | succ j ih =>
    intro J
    have H := reserved_hop_owner b x (addr root j) []
      (hop (R (rightRail d (j+1))) (L (rightRail d j))) (L (rightRail d j))
      (F.adjacent j J) rfl
    change dataOwner _ (rightNeighbor (addr root j)) (rightRail d (j+1)) =
      dataOwner _ (addr root j) (rightRail d j) at H
    rw [←addr_next] at H
    exact H.trans (ih (by omega))

theorem left_owner {p : LargeParams} {n : Nat} {b : LargeRows p}
    {x : Fin n → LargeSite p} {root : Fin n} {d r : Nat}
    (F : BStarCopyLeftStrip.Strip b x root d r) :
    ∀ j, j<d+r → dataOwner (oldH6 b x) (addr root j) (BStarCopyLeftStrip.rail d j) =
      commandOwner (oldH6 b x) root 0 := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [zero,show BStarCopyLeftStrip.rail d 0=.ls from if_pos F.seam_pos]
    rfl
  | succ j ih =>
    intro J
    have H := reserved_hop_owner b x (addr root j) []
      (hop (L (BStarCopyLeftStrip.rail d j)) (R (BStarCopyLeftStrip.rail d (j+1))))
      (R (BStarCopyLeftStrip.rail d (j+1))) (left_adjacent F j J) rfl
    change dataOwner _ (addr root j) (BStarCopyLeftStrip.rail d j) =
      dataOwner _ (rightNeighbor (addr root j)) (BStarCopyLeftStrip.rail d (j+1)) at H
    rw [←addr_next] at H
    exact H.symm.trans (ih (by omega))

theorem lines_disjoint {n : Nat} (a b : Fin n) (d e i j : Nat) :
    BStarCopyLeftStrip.position a d i≠rightPos b e j := by
  intro E
  have H := congrArg Prod.snd E
  unfold BStarCopyLeftStrip.position BStarCopyLeftStrip.rail rightPos rightRail at H
  dsimp at H
  split at H <;> split at H <;> contradiction

open BStarLongWork BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

/-- Both physical line sizes and seam-dependent rows are determined
from a generated owner's fixed lower chart. No mobile occupancy
or steering condition is needed to identify the lines. -/
theorem of_chart {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) {r' W : Nat} (hr : 2≤r') (hW : r'≤W)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r') ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=r'))
    (notShort : ∀ i,oldH6 B base (rightNeighbor i)=true → r'≤oldOrdinal B base hh i+1)
    (cap : ∀ i,oldH6 B base (rightNeighbor i)=true → oldOrdinal B base hh i+1≤W)
    (other : ∃ i,i≠(S.getD len fall).1 ∧ oldH6 B base i=true) :
    ∃ l d, BStarCopyLeftStrip.Strip B base (S.getD 0 fall).1 l r' ∧
      addr (S.getD 0 fall).1 l=(S.getD len fall).1 ∧
      RightFrame B base (S.getD len fall).1 d r' ∧
      l+r'≤2*W ∧ d+r'≤2*W := by
  obtain ⟨l,L,joinL,_,_⟩ := BStarCopyLeftStrip.of_chart hp C (show 0<r' by omega) flags notShort
  obtain ⟨a,seam,tail,D,F,joinR,size,_⟩ := BStarCopyRightChartGeometry.of_chart hp C hr flags notShort other
  rw [zero] at joinR
  subst a
  have RF := right_extend D F size
  exact ⟨l,r'-1+seam,L,joinL,RF,left_width L hh hW cap,
    right_width RF hh (by have := F.seam_pos; omega) hW cap⟩

end L4.BStarFenceLineGeometry
