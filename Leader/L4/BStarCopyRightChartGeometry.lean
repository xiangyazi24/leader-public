import Leader.L4.BStarCopyRightActualWitness
import Leader.L4.BStarCopyLeftStrip

namespace L4.BStarCopyRightChartGeometry
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongCommand
open BStarH6WordChart BStarH6Ordinal BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarResetChartTouch BStarCopyRightStrip BStarCopyRightRetained
open BStarFenceReceiverChart BStarClearanceDataChart
open BStarLongFiberOwner BStarAcquireAnchors

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

private theorem zero_addr {n : Nat} (a : Fin n) : addr a 0=a :=
  Fin.ext (Nat.mod_eq_of_lt a.isLt)

private theorem add_addr {n : Nat} (a : Fin n) (i j : Nat) :
    addr (addr a i) j=addr a (i+j) := by
  calc
    addr (addr a i) j = digitFrom (addr a i) j := by
      have E := BStarCopyLeftStrip.addr_from (addr a i) 0 j
      rw [Nat.zero_add,zero_addr] at E
      exact E
    _ = addr a (i+j) := (BStarCopyLeftStrip.addr_from a i j).symm

private theorem reach_addr {n : Nat} (a b : Fin n) :
    ∃ off,off<n ∧ addr a off=b := by
  by_cases H : a.val≤b.val
  · refine ⟨b.val-a.val,by omega,Fin.ext ?_⟩
    change (a.val+(b.val-a.val))%n=b.val
    rw [show a.val+(b.val-a.val)=b.val by omega,Nat.mod_eq_of_lt b.isLt]
  · refine ⟨n-a.val+b.val,by omega,Fin.ext ?_⟩
    change (a.val+(n-a.val+b.val))%n=b.val
    rw [show a.val+(n-a.val+b.val)=b.val+n by omega,Nat.add_mod_right,Nat.mod_eq_of_lt b.isLt]

private theorem first_next {n : Nat} (h : Fin n→Bool) (root : Fin n)
    (other : ∃ q,q≠root ∧ h q=true) :
    ∃ d,0<d ∧ d<n ∧ h (addr root d)=true ∧
      ∀ j,0<j → j<d → h (addr root j)=false := by
  obtain ⟨q,ne,J⟩ := other
  obtain ⟨z,zn,Z⟩ := reach_addr root q
  have nz : 0<z := by
    cases z with
    | zero => exact (ne (Z.symm.trans (zero_addr _))).elim
    | succ z => omega
  have H (d : Nat) (pos : 0<d) (D : h (addr root d)=true) :
      ∃ next,0<next ∧ next≤d ∧ h (addr root next)=true ∧
        ∀ j,0<j → j<next → h (addr root j)=false := by
    induction d using Nat.strongRecOn with
    | ind d ih =>
      by_cases any : ∃ j,0<j ∧ j<d ∧ h (addr root j)=true
      · obtain ⟨j,P,L,R⟩ := any
        obtain ⟨next,A,Q,S,T⟩ := ih j L P R
        exact ⟨next,A,by omega,S,T⟩
      · refine ⟨d,pos,Nat.le_refl _,D,?_⟩
        intro j P L
        cases K : h (addr root j)
        · rfl
        · exact (any ⟨j,P,L,K⟩).elim
  obtain ⟨d,A,C,D,E⟩ := H z nz (Z.symm ▸ J)
  exact ⟨d,A,by omega,D,E⟩

/-- The current right projection cannot describe a one-header ring:
the last upstream RS aliases the physical RD head on a different
sheet. Its physical offset is n, excluded by Strip.tail_lt. -/
theorem sole_header_no_strip (base : X) (root a : Fin n) (width seam tail : Nat)
    (only : ∀ i,oldH6 B base i=true → i=root)
    (strip : Strip B base a seam tail)
    (join : addr a 0=addr root (width-1)) (size : tail+1=seam+width)
    (hw : 0<width) : False := by
  rw [zero_addr] at join
  have H := only _ strip.rs_header
  rw [join,add_addr] at H
  have H' : addr root (width-1+seam)=addr root 0 := H.trans (zero_addr _).symm
  have J := strip.tail_lt
  have P := strip.seam_pos
  have K := addr_inj root (i:=width-1+seam) (j:=0) (by omega) (by have := root.isLt; omega) H'
  omega

/-- The present Strip definition also excludes width one: index zero
would be the H6 destination header, but rd_noheader includes it. -/
theorem width_one_no_strip (base : X) (root a : Fin n) (seam tail : Nat)
    (H : oldH6 B base root=true) (strip : Strip B base a seam tail)
    (join : addr a 0=addr root (1-1)) : False := by
  have E := strip.rd_noheader 0 strip.seam_pos
  rw [join,show 1-1=0 from rfl,zero_addr,H] at E
  contradiction

/-- Actual right dest/strip from the K10 chart header and the first
following H6. The restriction to a second header and width ≥2 is
essential for the present right Strip data type. -/
theorem of_chart {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) {width : Nat} (hw : 2≤width)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<width) ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=width))
    (notShort : ∀ i,oldH6 B base (rightNeighbor i)=true → width≤oldOrdinal B base hh i+1)
    (other : ∃ i,i≠(S.getD len fall).1 ∧ oldH6 B base i=true) :
    let root := (S.getD len fall).1
    ∃ a seam tail, Dest B base root width ∧ Strip B base a seam tail ∧
      addr a 0=addr root (width-1) ∧ tail+1=seam+width ∧
      dataOwner (oldH6 B base) (addr a 0) (rail seam 0)=o.val := by
  dsimp only
  let root := (S.getD len fall).1
  have H := (endpoint_spec (oldH6 B base) hh o 10)
  rw [←chart.terminal] at H
  have rootH : oldH6 B base root=true := H.1
  have rootO : commandOwner (oldH6 B base) root 10=o.val := H.2.1
  obtain ⟨d,dp,dn,next,mid⟩ := first_next (oldH6 B base) root other
  have dist : ∀ j<d,oldOrdinal B base hh (addr root j)=j := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [zero_addr]
      exact (ordinal_zero _ hh root).mpr rootH
    | succ j ih =>
      intro L
      have J := ordinal_body (oldH6 B base) hh (addr root j) (by
        rw [←addr_next]
        exact mid (j+1) (by omega) L)
      change oldOrdinal B base hh (rightNeighbor (addr root j))=oldOrdinal B base hh (addr root j)+1 at J
      rw [←addr_next,ih (by omega)] at J
      exact J
  have dw : width≤d := by
    have N : oldH6 B base (rightNeighbor (addr root (d-1)))=true := by
      rw [←addr_next,show d-1+1=d by omega]
      exact next
    have Q := notShort _ N
    rw [dist _ (by omega)] at Q
    omega
  let a := addr root (width-1)
  let seam := d-(width-1)
  have se : width-1+seam=d := by dsimp [seam]; omega
  have sp : 0<seam := by dsimp [seam]; omega
  have sr : addr a seam=addr root d := by rw [show a=addr root (width-1) from rfl,add_addr,se]
  have after (i : Nat) (L : seam≤i) (U : i≤d) :
      oldOrdinal B base hh (addr a i)=i-seam := by
    have R := digit_from hp next width notShort (i-seam) (by omega)
    rw [←sr,←BStarCopyLeftStrip.addr_from,show seam+(i-seam)=i by omega] at R
    exact R.1
  have before (i : Nat) (L : i<seam) :
      oldOrdinal B base hh (addr a i)=width-1+i := by
    rw [show a=addr root (width-1) from rfl,add_addr]
    exact dist _ (by omega)
  have D : Dest B base root width := by
    refine ⟨by omega,by omega,?_,?_,?_⟩
    · rw [zero_addr]; exact rootH
    · intro j P L
      exact mid _ P (by omega)
    · intro j L
      rw [(flags _).1,dist _ (by omega)]
      exact decide_eq_true L
  have U : Strip B base a seam d := by
    refine ⟨sp,by omega,dn,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · rw [(flags _).1,before 0 sp]
      exact decide_eq_true (by omega)
    · intro i L
      rw [show a=addr root (width-1) from rfl,add_addr]
      exact mid _ (by omega) (by omega)
    · intro i P L
      rw [(flags _).1,before i L]
      exact decide_eq_false (by omega)
    · rwa [sr]
    · intro i P L
      cases e : oldH6 B base (addr a i)
      · rfl
      · have zero := (ordinal_zero _ hh _).mpr e
        change oldOrdinal B base hh (addr a i)=0 at zero
        rw [after i (by omega) L] at zero
        omega
    · intro i P L
      rw [(flags _).1,after i P L]
      exact decide_eq_true (by omega)
    · intro i P L
      unfold ends
      rw [(flags _).2,after i P (by omega)]
      simp [show i-seam+1≠width by omega]
    · unfold ends
      rw [(flags _).1,(flags _).2,after d (by omega) (Nat.le_refl _)]
      simp [show d-seam<width by omega,show d-seam+1=width by omega]
  refine ⟨a,seam,d,D,U,zero_addr _,by omega,?_⟩
  have wordSame := (digit_from hp rootH width notShort (width-1) (by omega)).2
  have aa : a=digitFrom root (width-1) := by
    have T := BStarCopyLeftStrip.addr_from root 0 (width-1)
    rw [Nat.zero_add,zero_addr] at T
    exact T
  rw [←aa] at wordSame
  rw [zero_addr,show rail seam 0=.rd from if_pos sp]
  unfold dataOwner
  rw [show word (oldH6 B base) a=word (oldH6 B base) root from wordSame]
  exact rootO

end L4.BStarCopyRightChartGeometry
