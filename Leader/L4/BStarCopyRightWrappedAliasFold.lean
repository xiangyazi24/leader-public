import Leader.L4.BStarCopyRightWrappedAliasWin
import Leader.L4.BStarCopyRightWrappedAliasMark

namespace L4.BStarCopyRightWrappedAliasFold
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims
open BStarH6WordChart BStarCopyRightStrip BStarCopyRightWrappedGeometry BStarCopyRightWrappedPairs
open BStarLongPackets BStarLongPrep BStarLongCommandData BStarCopyInjection
open BStarCopyFenceSaturation BStarCopyMarkedLedger BStarCopyFIFO
open BStarCopyRightMark BStarCopyRightRetained BStarCopyRightRetainedClassify
open BStarCopyRightDeposit BStarCopyRightWrappedDeposit BStarCopyRightWrappedSelection
open BStarLongCommand BStarLongEvents BStarLongToken

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B

open BStarCopyRightWrappedAliasMark BStarCopyRightWrappedAliasWin BStarCopyRightWrappedSweep

theorem alias_release_mark {Tag : Type} (digits : Tag→BitVec 36)
    (x : X) (root a : Fin n) (width seam : Nat) (N : 1<n)
    (D : Dest B x root width) (U : WrappedStrip B x a seam n)
    (join : addr a 0=addr root (width-1))
    (s : Ledger Tag) (plan : List Tag) (size : plan.length=width)
    (label : Nat→Option Tag) (P : OrderedPrefix plan s (stripWord n label))
    (old : RetainedMatches digits x root width s)
    (mob : MobileMatches digits x a seam n label)
    (fresh : Tag) (todo : List Tag) (blank : label n=none)
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
    ∃ (t : Ledger Tag) (labels : Nat→Option Tag),
      t.release=(s.releaseOne fresh todo).release ∧
      OrderedPrefix plan t (stripWord n labels) ∧
      RetainedMatches digits out root width t ∧ MobileMatches digits out a seam n labels := by
  dsimp only
  intro sep win prep upScope gate frozen gates
  let e := addr a 0
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let g := oldPair B x e
  let u := R (rail seam 1)
  let v := L (rail seam 0)
  let rv := reserved (round g raw).prep
  let h := hop u v
  have loc : addr a n=e := by
    apply Fin.ext
    change (a.val+n)%n=(a.val+0)%n
    rw [Nat.add_mod_right,Nat.add_zero]
  have ULoc : site e u.side=addr a 1 := (addr_next a 0).symm
  have RLoc : rail seam 0=.rd := if_pos U.seam_pos
  have RSn : rail seam n=.rs := if_neg (Nat.not_lt_of_ge U.seam_le_tail)
  have pU : u∉rv := upScope 1 .right (by decide) (by omega) (by omega) ULoc
  have pV := prep (width-1) (by have := D.pos; omega) .left join
  have sel := ingress_selected hp x a seam n U _ pU pV
  have A : (view raw u).mobile=encode digits (label 1) := by
    rw [old_access x e u,ULoc]
    exact mob 1 (by decide) (by omega)
  have Z : (view raw v).mobile=encode digits (s.cells 0).mobile := by
    rw [old_access x e v,show site e v.side=addr root (width-1) from join]
    change (readLane (Sheet.index (rail seam 0)) (x (addr root (width-1))).long).mobile=_
    rw [RLoc]
    have K := (old (width-1) (by have := D.pos; omega)).1
    rwa [Nat.sub_self] at K
  have G : ((view raw u).gate && (view raw v).gate)=true := by
    rw [old_access x e u,old_access x e v,ULoc]
    change ((lanes x (addr a 1) (rail seam 1)).gate && (lanes x (addr a 0) (rail seam 0)).gate)=true
    rwa [RLoc]
  have B0 : ∀ j,n≤j → j≤n → label j=none := by
    intro j jj jj2
    rw [show j=n by omega,blank]
  have localVac := mob n (by omega) (Nat.le_refl _)
  rw [RSn,blank,loc] at localVac
  have gateOrig := gate
  have frozenOrig := frozen
  rw [loc] at gate frozen
  have injectionEq : readLane (Sheet.index .rs) (ring x e e).long =
      {readLane (Sheet.index .rs) (x e).long with mobile:=.data (digits fresh),frozen:=.empty} := BStarCopyOperand.ring_inject hp x e sep .left true (digits fresh) win
    gate frozen localVac
  have stays (inactive : h∉orderedData g rv ∨ (view raw u).mobile=.empty ∨
      (((view raw u).gate && (view raw v).gate)=true ∧ (view raw v).mobile≠.empty)) :
      ∃ t labels,t.release=(s.releaseOne fresh todo).release ∧
      OrderedPrefix plan t (stripWord n labels) ∧ RetainedMatches digits (ring x e) root width t ∧
      MobileMatches digits (ring x e) a seam n labels := by
    have keepRD := (BStarCopyRightWrappedSweep.ingress_quiet hp digits x root a width seam n D U join s
      plan size label P old mob sep prep inactive).1
    have ord := deposit_ordered plan s label n n (by omega) (Nat.le_refl _) fresh todo pending B0 P
    refine ⟨s.releaseOne fresh todo,deposit label n fresh,rfl,ord,keepRD,?_⟩
    intro j J L
    by_cases last : j=n
    · subst j
      rw [RSn,loc]
      have dep : deposit label n fresh n=some fresh := by simp [deposit]
      rw [dep]
      exact congrArg Lane.mobile injectionEq
    · by_cases first : j=1
      · subst j
        have Z := strip_pair_frame hp x a seam n 0 (by omega) U inactive u (.inl rfl) pU
        change view (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) u=view raw u at Z
        rw [new_access hp x e u sep,old_access x e u,ULoc] at Z
        have S : readLane (Sheet.index (rail seam 1)) (ring x e (addr a 1)).long =
            readLane (Sheet.index (rail seam 1)) (x (addr a 1)).long := Z
        rw [S]
        simp only [deposit,if_neg last]
        exact mob 1 (by decide) L
      · simpa only [deposit,if_neg last] using alias_other_mobile hp digits x a seam label mob j J L first last
  cases first : label 1 with
  | none => exact stays (.inr (.inl (A.trans (by rw [first]; rfl))))
  | some prior =>
    cases dest : (s.cells 0).mobile with
    | some q => exact stays (.inr (.inr ⟨G,by rw [Z,dest]; intro H; contradiction⟩))
    | none =>
      have active := simultaneous_alias_win hp digits x root a width seam N D U join s plan size label
        P old mob prior fresh todo first blank dest pending sep win prep upScope gateOrig frozenOrig gates
      exact ⟨(s.receiveFirst prior).releaseOne fresh todo,deposit (clearHead label) n fresh,rfl,active⟩

end L4.BStarCopyRightWrappedAliasFold
