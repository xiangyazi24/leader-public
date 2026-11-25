import Leader.L4.PhysicalCustodyEntrance
import Leader.L4.WidthOrdinalSpan
import Leader.L4.WidthRatioArithmetic
import Leader.L4.PackedOrdinalCount

namespace L4.WidthPackedBridge
open AllSizeProtocol PhysicalCustody BStarH6Ordinal BStarH6WordChart
open BStarLongFixedRouting ShortLayerGeometry

/-- Certified S5/S6 physical successor bounds. This is not supplied by
a frozen H6 mask or by the coarse 1024r bounds. -/
def CertifiedSpacing {s n : Nat} (z : Raw s n) : Prop :=
  ∀ q, oldH6 (rows s) z q=true →
    ∃ d, 16*(s+1)*(radiusTwo s+1)≤d ∧ d≤81*(2*s+1)*(2*radiusTwo s+1) ∧
      Gap (oldH6 (rows s) z) q d

def FlagsCorrect {s n : Nat} (z : Raw s n) (hh : ∃ i,oldH6 (rows s) z i=true) : Prop :=
  ∀ i, (longGeometry (rows s) (z i)).inside=decide (oldOrdinal (rows s) z hh i<radWidth s) ∧
       (longGeometry (rows s) (z i)).last=decide (oldOrdinal (rows s) z hh i+1=radWidth s)

theorem spacing_end_width {s n : Nat} (z : Raw s n) (hh : ∃ i,oldH6 (rows s) z i=true)
    (S : CertifiedSpacing z) :
    ∀ e, oldH6 (rows s) z (rightNeighbor e)=true →
      16*(s+1)*(radiusTwo s+1)≤oldOrdinal (rows s) z hh e+1 ∧
      oldOrdinal (rows s) z hh e+1≤81*(2*s+1)*(2*radiusTwo s+1) :=
  WidthOrdinalSpan.end_width_bounds (oldH6 (rows s) z) hh S

theorem spacing_ratio {s n : Nat} (z : Raw s n) (hh : ∃ i,oldH6 (rows s) z i=true)
    (S : CertifiedSpacing z) :
    ∀ e f, oldH6 (rows s) z (rightNeighbor e)=true →
      oldH6 (rows s) z (rightNeighbor f)=true →
      4*(oldOrdinal (rows s) z hh e+1)<81*(oldOrdinal (rows s) z hh f+1) :=
  WidthRatioArithmetic.physical_width_ratio hh (spacing_end_width z hh S)

private theorem equal_headers {s n : Nat} {x y : Raw s n}
    (L : ∀ i, Layout (rows s) x i=Layout (rows s) y i) :
    oldH6 (rows s) x=oldH6 (rows s) y := funext (fun i=>congrArg Prod.fst (L i))

theorem spacing_of_same_layout {s n : Nat} {x y : Raw s n}
    (L : ∀ i, Layout (rows s) x i=Layout (rows s) y i)
    (S : CertifiedSpacing x) : CertifiedSpacing y := by
  unfold CertifiedSpacing at S ⊢
  rwa [←equal_headers L]

theorem flags_of_same_layout {s n : Nat} {x y : Raw s n}
    (L : ∀ i, Layout (rows s) x i=Layout (rows s) y i)
    (hx : ∃ i,oldH6 (rows s) x i=true) (hy : ∃ i,oldH6 (rows s) y i=true)
    (F : FlagsCorrect x hx) : FlagsCorrect y hy := by
  intro i
  have I : (longGeometry (rows s) (x i)).inside=(longGeometry (rows s) (y i)).inside :=
    congrArg (fun z : Bool × Bool × Bool=>z.2.1) (L i)
  have J : (longGeometry (rows s) (x i)).last=(longGeometry (rows s) (y i)).last :=
    congrArg (fun z : Bool × Bool × Bool=>z.2.2) (L i)
  have ordinalEq {h g : Fin n→Bool} (E : h=g)
      (hh : ∃ j,h j=true) (gg : ∃ j,g j=true) : ordinal h hh i=ordinal g gg i := by
    subst g
    rfl
  have A : oldOrdinal (rows s) x hx i=oldOrdinal (rows s) y hy i :=
    ordinalEq (equal_headers L) hx hy
  exact ⟨I.symm.trans ((F i).1.trans (congrArg (fun d=>decide (d<radWidth s)) A)),
     J.symm.trans ((F i).2.trans (congrArg (fun d=>decide (d+1=radWidth s)) A))⟩

/-- Once the certified H6 gap law and prefix flags are both present,
all static custody geometry fields follow on the actual raw state. -/
theorem geometry_of_certified_width {s n : Nat} (S : 6≤s) (z : Raw s n)
    (hh : ∃ i,oldH6 (rows s) z i=true) (gaps : CertifiedSpacing z)
    (flags : FlagsCorrect z hh) : CustodyGeometry z := by
  obtain ⟨lo,hi⟩ := WidthRatioArithmetic.production_bounds S
  have H (e : Fin n) (T : oldH6 (rows s) z (rightNeighbor e)=true) :
      radWidth s≤oldOrdinal (rows s) z hh e+1 :=
    Nat.le_trans lo (spacing_end_width z hh gaps e T).1
  have U (e : Fin n) (T : oldH6 (rows s) z (rightNeighbor e)=true) :
      oldOrdinal (rows s) z hh e+1≤1024*radWidth s :=
    Nat.le_trans (spacing_end_width z hh gaps e T).2 hi
  have pos : 0<radWidth s := by
    have P := Nat.pow_le_pow_right (by decide : 0<2) (show 1≤s by omega)
    unfold radWidth
    change 2≤2^s at P
    omega
  exact geometry_of_settled_flags hh pos flags H
    (PackedOrdinalCount.total_mul_width_le _ hh _ H) U (spacing_ratio z hh gaps)

/-- This is a static assembly, not an entrance proof for the width
writer. Closure of the actual lower/flag region and frozen Layout
are explicit inputs. No inherited width token is treated as credit. -/
theorem packed_fiber_from_closed_width {s n : Nat} (S : 6≤s) (z : Raw s n)
    (Q : Raw s n → Prop) (A : Q z)
    (closed : ∀ y e, Q y→Q (rawNext s y e))
    (layout : ∀ y, Q y→∀ i, Layout (rows s) z i=Layout (rows s) y i)
    (hh : ∃ i,oldH6 (rows s) z i=true) (gaps : CertifiedSpacing z)
    (flags : FlagsCorrect z hh) : Nonempty (PackedFiber z) := by
  refine ⟨⟨Q,A,closed,layout,?_⟩⟩
  intro y Y
  have L := layout y Y
  have hy : ∃ i,oldH6 (rows s) y i=true := equal_headers L ▸ hh
  exact geometry_of_certified_width S y hy (spacing_of_same_layout L gaps)
    (flags_of_same_layout L hh hy flags)

end L4.WidthPackedBridge
