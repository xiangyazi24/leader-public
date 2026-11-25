import Leader.L4.PhysicalCustodyCommonReplay
import Leader.L4.BStarCopyRightChartGeometry
import Leader.L4.BStarFenceLineGeometry
import Leader.L4.BStarOwnerChartWidth

namespace L4.PhysicalOwnerStripGeometry
open AllSizeProtocol BStarTrace PhysicalCustody BStarLongWork BStarLongClaims
open BStarH6WordChart BStarH6Ordinal BStarAcquireLiteralChain BStarAcquireVisitOrder
open BStarResetChartTouch BStarFenceLineGeometry BStarOwnerChartWidth
open BStarCopyRightStrip (addr addr_inj address_ordinal_run)
local notation "hp" => (show 0<2 by decide)

private theorem addrZero {n : Nat} (root : Fin n) : addr root 0=root :=
  Fin.ext (Nat.mod_eq_of_lt root.isLt)

private theorem short_word {n : Nat} (h : Fin n→Bool) (hh : ∃ i,h i=true)
    (W : Nat) (upper : ∀ i,h (rightNeighbor i)=true→ordinal h hh i+1≤W)
    (root : Fin n) (hdr : h root=true) (l : Nat) (lp : 0<l)
    (body : ∀ j,0<j→j<l→h (addr root j)=false) :
    l≤W := by
  have E := address_ordinal_run root h hh 0 (l-1)
    (fun j J L=>by simpa only [Nat.zero_add] using body j J (by omega)) (l-1) (by omega)
  rw [Nat.zero_add, addrZero, (ordinal_zero h hh root).mpr hdr, Nat.zero_add] at E
  have bound := ordinal_lt_of_width_bound h hh W upper (addr root (l-1))
  omega

/-- A settled width ceiling strictly below the ring size rules out a
sole H6 header, including on layouts whose first seam wraps. -/
theorem other_header_of_width {n : Nat} (h : Fin n→Bool) (hh : ∃ i,h i=true)
    (W : Nat) (upper : ∀ i,h (rightNeighbor i)=true→ordinal h hh i+1≤W)
    (hn : W<n) (root : Fin n) (hdr : h root=true) :
    ∃ i,i≠root ∧ h i=true := by
  classical
  by_cases H : ∃ i,i≠root ∧ h i=true
  · exact H
  · have B (j : Nat) (J : 0<j) (L : j<n) : h (addr root j)=false := by
      cases S : h (addr root j)
      · rfl
      · apply False.elim
        apply H
        refine ⟨addr root j,?_,S⟩
        intro K
        have N : addr root j=addr root 0 := K.trans (addrZero root).symm
        have eq := addr_inj root L (Nat.zero_lt_of_lt root.isLt) N
        omega
    exact (Nat.not_le_of_gt hn (short_word h hh W upper root hdr n (by omega) B)).elim

/-- Static strip adapter for the actual owner chart used by the physical
clocks. Width and size conditions are explicit; no progress is assumed. -/
theorem strips_of_chart {s n : Nat} {base : Raw s n} (g : ReadyAfterCovers base)
    {o : Owners (oldH6 (rows s) base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base g.hh o S len fall)
    (hw : 2≤radWidth s) (prod : 2*(1024*radWidth s)≤n) :
    let w := radWidth s
    let W := 1024*w
    ∃ l d,
      BStarCopyLeftStrip.Strip (rows s) base (S.getD 0 fall).1 l w ∧
      RightFrame (rows s) base (S.getD len fall).1 d w ∧
      0<d ∧ addr (S.getD 0 fall).1 l=(S.getD len fall).1 ∧
      0<l+w ∧ l+w≤n ∧ d+w≤n ∧ 2*len+1≤22*W := by
  dsimp only
  let w := radWidth s
  let W := 1024*w
  let h := oldH6 (rows s) base
  let root := (S.getD len fall).1
  have upper : ∀ i,h (rightNeighbor i)=true→ordinal h g.hh i+1≤W := g.upperWidth
  have hw₀ : 0<w := by omega
  have Wn : W<n := by
    change 2*W≤n at prod
    have P : 0<W := by dsimp [W]; omega
    omega
  have rootH : h root=true := by
    change h (S.getD len fall).1=true
    rw [C.terminal]
    exact (endpoint_spec h g.hh o 10).1
  have other := other_header_of_width h g.hh W upper Wn root rootH
  obtain ⟨l,LF,seam,_,_⟩ := BStarCopyLeftStrip.of_chart hp C hw₀ g.flags g.notShort
  obtain ⟨a,r,tail,D,U,shift,lenR,_⟩ :=
    BStarCopyRightChartGeometry.of_chart hp C hw g.flags g.notShort other
  rw [addrZero] at shift
  subst a
  have RF := right_extend D U lenR
  let d := w-1+r
  have dp : 0<d := by have H := U.seam_pos; dsimp [d]; omega
  have lB : l≤W := short_word h g.hh W upper _ LF.source_header l LF.seam_pos LF.ls_body
  have dB : d≤W := short_word h g.hh W upper _ RF.terminal_header d dp RF.body
  have wB : w≤W := by dsimp [W]; omega
  have length := chart_length_le_width_mul hp C W upper
  have lenS := C.length
  change 2*W≤n at prod
  exact ⟨l,d,LF,RF,dp,seam,by omega,by omega,by omega,by omega⟩

theorem strips_of_production {s n : Nat} {base : Raw s n} (g : ReadyAfterCovers base)
    (hs : 2≤s) (prod : 3*1024*radWidth s<n)
    (o : Owners (oldH6 (rows s) base)) :
    ∃ (S : List (Pos n)) (len : Nat) (fall : Pos n) (l d : Nat),
      Chart hp base g.hh o S len fall ∧
      BStarCopyLeftStrip.Strip (rows s) base (S.getD 0 fall).1 l (radWidth s) ∧
      RightFrame (rows s) base (S.getD len fall).1 d (radWidth s) ∧
      0<d ∧ addr (S.getD 0 fall).1 l=(S.getD len fall).1 ∧
      0<l+radWidth s ∧ l+radWidth s≤n ∧ d+radWidth s≤n ∧
      2*len+1≤22*(1024*radWidth s) := by
  have width : 2≤radWidth s := by
    unfold radWidth
    have P := Nat.pow_le_pow_right (by decide : 0<2) hs
    omega
  obtain ⟨S,len,fall,C⟩ := g.charts o
  obtain ⟨l,d,H⟩ := strips_of_chart g C width (by omega)
  exact ⟨S,len,fall,l,d,C,H⟩

end L4.PhysicalOwnerStripGeometry
