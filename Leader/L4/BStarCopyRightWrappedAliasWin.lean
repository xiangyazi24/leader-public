import Leader.L4.BStarCopyRightWrappedAliasMark
import Leader.L4.BStarCopyRightWrappedSelection

namespace L4.BStarCopyRightWrappedAliasWin
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims
open BStarH6WordChart BStarCopyRightStrip BStarCopyRightWrappedGeometry BStarCopyRightWrappedPairs
open BStarLongPackets BStarLongPrep BStarLongCommandData BStarCopyInjection
open BStarCopyFenceSaturation BStarCopyMarkedLedger BStarCopyFIFO
open BStarCopyRightMark BStarCopyRightRetained BStarCopyRightRetainedClassify
open BStarCopyRightDeposit BStarCopyRightWrappedDeposit BStarCopyRightWrappedSelection
open BStarLongCommand BStarLongEvents BStarLongToken BStarCopyRightWrappedAliasMark

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B

/-- Full ring projection of the nonstuttering wrapped alias release.
The actual healthy K2 offer and exclusive reservation scope give
both literal selected rows; every other tracked lane is accounted for. -/
theorem simultaneous_alias_win {Tag : Type} (digits : Tag→BitVec 36)
    (x : X) (root a : Fin n) (width seam : Nat) (N : 1<n)
    (D : Dest B x root width) (U : WrappedStrip B x a seam n)
    (join : addr a 0=addr root (width-1))
    (s : Ledger Tag) (plan : List Tag) (size : plan.length=width)
    (label : Nat→Option Tag) (P : OrderedPrefix plan s (stripWord n label))
    (old : RetainedMatches digits x root width s)
    (mob : MobileMatches digits x a seam n label)
    (prior fresh : Tag) (todo : List Tag) (got : label 1=some prior)
    (blank : label n=none) (empty : (s.cells 0).mobile=none)
    (pending : s.release.pending=fresh::todo)
    :
    let e := addr a 0
    let g := oldPair B x e
    let raw := ((x e).long,(x (rightNeighbor e)).long)
    e≠rightNeighbor e →
    injection .left true∈(arbitration (round g raw).prep).1 →
    NoRDPrep hp x root e width → NoPrepExcept hp x e a seam n n →
    (lanes x (addr a n) .rs).gate=true →
    (lanes x (addr a n) .rs).frozen=.data (digits fresh) →
    ((lanes x (addr a 1) (rail seam 1)).gate && (lanes x (addr a 0) .rd).gate)=true →
    let out := ring x e
    let t := (s.receiveFirst prior).releaseOne fresh todo
    let labels := deposit (clearHead label) n fresh
    OrderedPrefix plan t (stripWord n labels) ∧
      RetainedMatches digits out root width t ∧ MobileMatches digits out a seam n labels := by
  dsimp only
  intro sep won prep upScope gate frozen gates
  let e := addr a 0
  have headLoc : addr a n=e := by
    apply Fin.ext
    change (a.val+n)%n=(a.val+0)%n
    rw [Nat.add_mod_right,Nat.add_zero]
  have rightLoc : rightNeighbor e=addr a 1 := (addr_next a 0).symm
  have r := prep (width-1) (by have := D.pos; omega) .left join
  have u := upScope 1 .right (by decide) (by omega) (by omega) rightLoc
  have sel := ingress_selected hp x a seam n U _ u r
  have rs : rail seam n=.rs := if_neg (Nat.not_lt_of_ge U.seam_le_tail)
  have js := mob n (by omega) (Nat.le_refl _)
  rw [blank,rs,headLoc] at js
  have first := mob 1 (by decide) (by omega)
  rw [got] at first
  have atRD := old (width-1) (by have := D.pos; omega)
  rw [Nat.sub_self,←join] at atRD
  have orig : OrderedPrefix plan s (prior::stripWord n (clearHead label)) :=
    (stripWord_clear label n (by omega) prior got) ▸ P
  rw [headLoc] at gate frozen
  rw [←rightLoc] at gates first
  obtain ⟨ord,newSender,newRet,newTail,notFrozen⟩ :=
    ingress_release_and_cross hp digits x a seam U prior fresh (stripWord n (clearHead label)) todo s plan
      orig pending sep won sel gate frozen js gates
      first atRD empty
  have endVacant : ∀ j,n≤j → j≤n → clearHead label j=none := by
    intro j A Z
    have E : j=n := by omega
    subst j
    simp [clearHead,show n≠1 by omega,blank]
  refine ⟨?_,?_,?_⟩
  · rw [stripWord_deposit _ n n (by omega) (Nat.le_refl _) fresh endVacant]
    exact ord
  · intro j L
    by_cases jLast : j=width-1
    · subst j
      rw [Nat.sub_self,←join]
      exact newRet
    · have sameCell : ((s.receiveFirst prior).releaseOne fresh todo).cells (width-1-j)=s.cells (width-1-j) := by
        simp [Ledger.releaseOne,Ledger.receiveFirst,show width-1-j≠0 by have := D.pos; omega]
      change Compatible digits (((s.receiveFirst prior).releaseOne fresh todo).cells (width-1-j)) _
      rw [sameCell]
      have notLeft : addr root j≠e := fun H => jLast (addr_inj root (by have := D.fit; omega)
        (by have := D.fit; have := D.pos; omega) (H.trans join))
      by_cases touched : addr root j=rightNeighbor e
      · by_cases zero : j=0
        · subst j
          rw [retained_header_frame hp digits x root e width D s plan _ size P old touched.symm sep
            (prep 0 L .right touched.symm)]
          exact old 0 L
        · have eEq : e=addr root (j-1) := by
            apply rightNeighbor_inj
            rw [←addr_next root (j-1),show j-1+1=j by omega]
            exact touched.symm
          have I := addr_inj root (i:=width-1) (j:=j-1)
            (by have := D.fit; have := D.pos; omega) (by have := D.fit; omega) (join.symm.trans eEq)
          omega
      · rw [show ring x e (addr root j)=x (addr root j) from by simp [AllSizeS1Geometry.step,notLeft,touched]]
        exact old j L
  · intro j J R
    by_cases first : j=1
    · subst j
      simp only [deposit,if_neg (show 1≠n by omega),clearHead]
      exact rightLoc ▸ newSender
    · by_cases last : j=n
      · subst j
        simp only [deposit,rs]
        exact headLoc.symm ▸ newTail
      · simpa only [deposit,clearHead,if_neg first,if_neg last] using alias_other_mobile hp digits x a seam label mob j J R first last

end L4.BStarCopyRightWrappedAliasWin
