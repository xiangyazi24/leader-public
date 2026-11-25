import Leader.L4.BStarCopyRightInjectStep
import Leader.L4.BStarCopyRightLoadCoverage

namespace L4.BStarCopyRightReleaseOrder
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarCopyRightStrip BStarCopyRightK2 BStarCopyRightLoadCoverage
open BStarCopyRightReleaseClass BStarCopyRightMixed BStarCopyMarkedLedger
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarClearanceDataChart BStarGeneratedOwner BStarSeparatingRail

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

/-- The right-source K2 indices are one literal contiguous interval
on the command chart, in precisely physical source order. -/
structure K2Block (S : List (Pos n)) (len : Nat) (fall : Pos n)
    (a : Fin n) (seam tail first : Nat) : Prop where
  start : 0<first
  valid : seam≤tail
  address : ∀ i, seam≤i → i≤tail →
    first+(i-seam)<len ∧ S.getD (first+(i-seam)) fall=(addr a i,2)

theorem k2_block {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (a : Fin n) (seam tail : Nat) (C : Strip B base a seam tail)
    (head : dataOwner (oldH6 B base) (addr a 0) (rail seam 0)=o.val) :
    ∃ first, K2Block S len fall a seam tail first := by
  have T := C.seam_le_tail
  obtain ⟨first,fl,atFirst⟩ := rs_ord hp chart a seam tail C head seam (by omega) T
  have firstPos : 0<first := by
    cases first with
    | zero =>
      have E := congrArg Prod.snd (chart.root.symm.trans atFirst)
      change (0 : Fin 11)=2 at E
      contradiction
    | succ j => omega
  refine ⟨first,firstPos,T,?_⟩
  have H : ∀ d, seam+d≤tail →
      first+d<len ∧ S.getD (first+d) fall=(addr a (seam+d),2) := by
    intro d
    induction d with
    | zero =>
      intro _
      simpa only [Nat.add_zero] using And.intro fl atFirst
    | succ d ih =>
      intro scope
      obtain ⟨bound,E⟩ := ih (by omega)
      let j := seam+d
      let u : Pos n := (addr a j,2)
      let v : Pos n := (addr a (j+1),2)
      have right := addr_next a j
      have body : (oldPair B base (addr a j)).2.axes.h6=false := by
        change oldH6 B base (rightNeighbor (addr a j))=false
        rw [←right]
        exact C.rs_nonheader _ (by dsimp [j]; omega) (by dsimp [j]; omega)
      have edge : Edge B base u v := by
        refine ⟨addr a j,link (L 2) (R 2),R 2,k2_body _ body,rfl,rfl,?_⟩
        change (addr a (j+1),2)=(rightNeighbor (addr a j),2)
        rw [right]
      have Ls := chart.length
      have jr : first+d<S.length := by omega
      have U : S.getD (first+d) fall=u := E
      have m : u∈S := by
        rw [←U,←List.getElem_eq_getD (h:=jr)]
        exact List.getElem_mem _
      obtain ⟨p,pLt,F,G⟩ := chart.edge u v m edge
      have pEq : p=first+d := (List.getD_inj (by omega) jr chart.nodup).mp (by
        rw [←List.getElem_eq_getD (h:=show p<S.length by omega),F,U])
      subst p
      have new : S.getD (first+d+1) fall=v := (List.getElem_eq_getD _).symm.trans G
      have strict : first+d+1<len := by
        by_cases eq : first+d+1=len
        · rw [eq] at new
          have K := congrArg Prod.snd (chart.terminal.symm.trans new)
          change (10 : Fin 11)=2 at K
          contradiction
        · omega
      rw [Nat.add_succ,Nat.add_succ]
      exact ⟨strict,new⟩
  intro i lo hi
  have E : seam+(i-seam)=i := by omega
  simpa only [E] using H (i-seam) (by omega)

theorem release_position {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    {a e : Fin n} {seam tail first : Nat} {m : Mode}
    (block : K2Block S len fall a seam tail first)
    (R : ReleaseAt hp x e a seam tail (fun k=>S.getD k fall) len m) :
    R.k=first+(R.i-seam) := by
  have Ls := chart.length
  have e := block.address R.i R.range.1 R.range.2
  have h := R.strict
  exact (List.getD_inj (by omega) (by have := e.1; omega) chart.nodup).mp (R.ptr.trans e.2.symm)

def nextSource (seam tail first k : Nat) : Nat := seam+min (tail+1-seam) (k-first)

def PendingAt {Tag : Type} (atSource : Nat→Tag) (seam tail first k : Nat) : List Tag :=
  let i := nextSource seam tail first k
  (List.range' i (tail+1-i)).map atSource

theorem pending_initial {Tag : Type} (atSource : Nat→Tag) (seam tail first : Nat) :
    PendingAt atSource seam tail first 0=planOf atSource seam tail := by
  simp [PendingAt,nextSource,planOf]

/-- If this actual cursor belongs to the old selected right source,
the pending suffix is exactly indexed by that source. -/
theorem pending_release {Tag : Type} (atSource : Nat→Tag)
    (seam tail first k i : Nat) (lo : seam≤i) (hi : i≤tail)
    (ptr : k=first+(i-seam)) :
    PendingAt atSource seam tail first k=(List.range' i (tail+1-i)).map atSource ∧
    PendingAt atSource seam tail first (k+1)=(List.range' (i+1) (tail-i)).map atSource := by
  subst k
  unfold PendingAt nextSource
  have A : min (tail+1-seam) (first+(i-seam)-first)=i-seam := by
    rw [show first+(i-seam)-first=i-seam by omega]
    exact Nat.min_eq_right (by omega)
  have BB : min (tail+1-seam) (first+(i-seam)+1-first)=i+1-seam := by
    have Q : first+(i-seam)+1-first=i+1-seam := by omega
    rw [Q,Nat.min_eq_right (by omega)]
  rw [A,BB,show seam+(i-seam)=i by omega,show seam+(i+1-seam)=i+1 by omega]
  dsimp only
  rw [show tail+1-(i+1)=tail-i by omega]
  exact ⟨rfl,rfl⟩

/-- An actual cursor crossing outside the K2 block leaves pending
unchanged. Stutters leave it unchanged definitionally. -/
theorem pending_off_block {Tag : Type} (atSource : Nat→Tag)
    (seam tail first k : Nat) (outside : k<first ∨ first+(tail+1-seam)≤k) :
    PendingAt atSource seam tail first (k+1)=PendingAt atSource seam tail first k := by
  unfold PendingAt nextSource
  rcases outside with H|H
  · rw [show k+1-first=0 by omega,show k-first=0 by omega]
  · rw [Nat.min_eq_left (by omega : tail+1-seam≤k+1-first),
      Nat.min_eq_left (by omega : tail+1-seam≤k-first)]

theorem pending_after_block {Tag : Type} (atSource : Nat→Tag)
    (seam tail first k : Nat) (within : seam≤tail) (done : first+(tail+1-seam)≤k) :
    PendingAt atSource seam tail first k=[] := by
  unfold PendingAt nextSource
  rw [Nat.min_eq_left (by omega : tail+1-seam≤k-first)]
  simp [show seam+(tail+1-seam)=tail+1 by omega]

#print axioms k2_block
#print axioms release_position
#print axioms pending_release
end L4.BStarCopyRightReleaseOrder
