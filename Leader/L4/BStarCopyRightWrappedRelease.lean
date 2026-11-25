import Leader.L4.BStarCopyRightWrappedAliasFold

namespace L4.BStarCopyRightWrappedRelease
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarLongPackets BStarLongCommandData BStarLongPrep
open BStarCopyRightStrip BStarCopyRightMark BStarCopyFIFO BStarCopyFenceSaturation
open BStarCopyMarkedLedger BStarCopyRightRetained BStarCopyRightRetainedClassify
open BStarCopyRightDataSweep BStarCopyRightDeposit BStarCopyDownstream
open BStarAcquireVisitOrder

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B

open BStarCopyRightMixed

open BStarCopyRightWrappedSweep BStarCopyRightWrappedGeometry
open BStarCopyRightWrappedPairs BStarCopyRightWrappedAliasFold
open BStarLongToken BStarLongEvents BStarLongCommand
local notation "updateRing" => ring

private theorem wrapped_other_positions (x : X) (base : Fin n) (i j tail : Nat)
    (ip : 0<i) (it : i<tail) (jp : 0<j) (jt : j≤tail) (N : tail≤n)
    (a : j≠i) (b : j≠i+1) :
    ring x (addr base i) (addr base j)=x (addr base j) := by
  apply ring_exterior_frame hp x base _ j jp
  · intro E
    exact a (upstream_addr_inj base jp ip (by omega) (by omega) E.symm)
  · intro E
    have H := addr_next base (j-1)
    rw [show j-1+1=j by omega,←E,←addr_next] at H
    exact b (upstream_addr_inj base jp (by omega) (by omega) (by omega) H)

theorem ring_blocked_spectator (x : X) (base : Fin n) (seam tail i k j : Nat)
    (C : WrappedStrip B x base seam tail) (kt : k<tail)
    (jp : 0<j) (jt : j≤tail) (J : j≠i)
    (kp : 0<k) (scope : NoPrepExcept hp x (addr base k) base seam tail i)
    (block : let e := addr base k
      let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
      let rs := reserved (round (oldPair B x e) raw).prep
      L (rail seam k)∈rs ∨ R (rail seam (k+1))∈rs)
    (sep : addr base k≠rightNeighbor (addr base k)) :
    lanes (updateRing x (addr base k)) (addr base j) (rail seam j) =
      lanes x (addr base j) (rail seam j) := by
  dsimp only at block
  let e := addr base k
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let rs := reserved (round (oldPair B x e) raw).prep
  have nobid := strip_reserved_blocks (b:=B) (x:=x) (base:=base) (seam:=seam) (i:=k) rs block
  have H := strip_pair_frame hp x base seam tail k kt C (Or.inl nobid)
  by_cases A : j=k
  · subst j
    let s := L (rail seam k)
    have S : s∉rs := scope k .left jp jt J rfl
    have Hs := H s (.inr rfl) S
    change view (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) s=view raw s at Hs
    rw [new_access hp x e s sep,old_access] at Hs
    exact Hs
  · by_cases E : j=k+1
    · subst j
      let s := R (rail seam (k+1))
      have V : site e .right=addr base (k+1) := (addr_next base k).symm
      have S : s∉rs := scope (k+1) .right jp jt J V
      have Hs := H s (.inl rfl) S
      change view (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) s=view raw s at Hs
      rw [new_access hp x e s sep,old_access] at Hs
      change readLane (Sheet.index (rail seam (k+1))) (updateRing x e (site e .right)).long =
        readLane (Sheet.index (rail seam (k+1))) (x (site e .right)).long at Hs
      rw [V] at Hs
      exact Hs
    · unfold lanes
      rw [wrapped_other_positions hp x base k j tail kp kt jp jt C.tail_le A E]

theorem ring_tail_exterior (x : X) (base : Fin n) (seam tail j : Nat)
    (_C : WrappedStrip B x base seam tail) (jp : 0<j) (jt : j≤tail) (ne : j≠tail) (tailN : tail<n) :
    updateRing x (addr base tail) (addr base j)=x (addr base j) := by
  apply ring_exterior_frame hp x base (addr base tail) j jp
  · intro H
    exact ne ((addr_inj base tailN (by omega) H).symm)
  · intro H
    have K := addr_inj base tailN (by omega) H
    omega

theorem ring_deposit {Tag : Type} (digits : Tag→BitVec 36) (atSource : Nat→Tag)
    (x : X) (e base : Fin n) (seam tail i : Nat)
    (C : WrappedStrip B x base seam tail) (is : seam≤i) (it : i≤tail)
    (loc : e=addr base i) (sep : e≠rightNeighbor e) (noningress : e≠addr base 0)
    (labels : Nat→Option Tag) (matched : MobileMatches digits x base seam tail labels)
    (scope : NoPrepExcept hp x e base seam tail i)
    (win : BStarCopyInjection.injection .left true∈
      (arbitration (round (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).prep).1)
    (gate : (lanes x (addr base i) .rs).gate=true)
    (captured : (lanes x (addr base i) .rs).frozen=.data (digits (atSource i)))
    (vacant : labels i=none) :
    MobileMatches digits (updateRing x e) base seam tail (deposit labels i (atSource i)) := by
  have ip : 0<i := by have := C.seam_pos; omega
  have rs : rail seam i=.rs := if_neg (by omega)
  have E := matched i ip it
  rw [vacant,rs] at E
  have old : (lanes x (addr base i) .rs).mobile=.empty := E
  have G : (lanes x (site e .left) .rs).gate=true := loc.symm ▸ gate
  have F : (lanes x (site e .left) .rs).frozen=.data (digits (atSource i)) := loc.symm ▸ captured
  have A : (lanes x (site e .left) .rs).mobile=.empty := loc.symm ▸ old
  have out := congrArg Lane.mobile (BStarCopyOperand.ring_inject hp x e sep .left true
    (digits (atSource i)) win G F A)
  change (lanes (updateRing x e) (site e .left) .rs).mobile=.data (digits (atSource i)) at out
  rw [loc] at out
  have booked : (⟨Side.left,rail seam i⟩ : At Sheet)∈
      reserved (round (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).prep := by
    rw [rs]
    exact List.mem_map.mpr ⟨_,win,rfl⟩
  intro j jp jt
  by_cases J : j=i
  · subst j
    rw [rs]
    change (lanes (updateRing x e) (addr base i) .rs).mobile =
      encode digits (deposit labels i (atSource i) i)
    rw [loc]
    change (lanes (updateRing x (addr base i)) (site (addr base i) .left) .rs).mobile = _
    rw [out]
    simp [deposit,BStarCopyFIFO.encode]
  · have same : lanes (updateRing x e) (addr base j) (rail seam j)=lanes x (addr base j) (rail seam j) := by
      subst e
      by_cases T : i=tail
      · subst i
        have lim : tail<n := by
          have L := C.tail_le
          by_cases E : tail=n
          · subst tail
            exfalso
            apply noningress
            apply Fin.ext
            change (base.val+n)%n=(base.val+0)%n
            rw [Nat.add_mod_right,Nat.add_zero]
          · omega
        unfold lanes
        rw [ring_tail_exterior hp x base seam tail j C jp jt J lim]
      · exact ring_blocked_spectator hp x base seam tail i i j C (by omega) jp jt J ip scope
          (Or.inl booked) sep
    change (lanes (updateRing x e) (addr base j) (rail seam j)).mobile = _
    rw [same]
    simp only [deposit,if_neg J]
    exact matched j jp jt

private theorem rebase_same_up {Tag : Type} (s t : Ledger Tag) (up other : List Tag)
    (d : Tag) (todo : List Tag) (same : OrderedStep s up t up) :
    OrderedStep (s.releaseOne d todo) other (t.releaseOne d todo) other := by
  suffices all : ∀ (u v : List Tag), OrderedStep s u t v → u=v →
      OrderedStep (s.releaseOne d todo) other (t.releaseOne d todo) other by
    exact all up up same rfl
  intro u v Q eq
  cases Q with
  | hold => exact .hold _ _
  | issue us a z old =>
    have L := congrArg List.length eq
    simp only [List.length_append,List.length_cons,List.length_nil] at L
    omega
  | cross us a vac credit =>
    have L := congrArg List.length eq
    simp only [List.length_cons] at L
    omega
  | interior us k a src dst =>
    rw [release_transfer_commute]
    exact .interior _ _ k a src dst

/-- A real left-origin release on the wrapped strip. Away from ingress
the reserved strip hop blocks and an independent retained hop may
act. At the full-wrap alias, the initial ingress may independently
consume only its old head, or be blocked, with exact tail deposition
in either case. -/
theorem wrapped_release_mark {Tag : Type} (digits : Tag→BitVec 36) (atSource : Nat→Tag)
    (x : X) (root base e : Fin n) (width seam tail i : Nat)
    (C : Dest B x root width) (U : WrappedStrip B x base seam tail)
    (join : addr base 0=addr root (width-1)) (sep : e≠rightNeighbor e)
    (s : Ledger Tag) (size : (planOf atSource seam tail).length=width)
    (label : Nat→Option Tag)
    (P : OrderedPrefix (planOf atSource seam tail) s (stripWord tail label))
    (old : RetainedMatches digits x root width s) (mob : MobileMatches digits x base seam tail label)
    (rg : ∀ j<width,(lanes x (addr root j) .rd).gate=true)
    (ug : ∀ j,0<j → j≤tail → (lanes x (addr base j) (rail seam j)).gate=true)
    (rdPrep : NoRDPrep hp x root e width)
    (is : seam≤i) (it : i≤tail) (loc : e=addr base i) (only : NoPrepExcept hp x e base seam tail i)
    (win : BStarCopyInjection.injection .left true∈
      (arbitration (round (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).prep).1)
    (gate : (lanes x (addr base i) .rs).gate=true)
    (captured : (lanes x (addr base i) .rs).frozen=.data (digits (atSource i)))
    (behind : ∀ j,i≤j → j≤tail → label j=none)
    (pending : s.release.pending=(List.range' i (tail+1-i)).map atSource) :
    let rest := (List.range' (i+1) (tail-i)).map atSource
    ∃ t labels,t.release=(s.releaseOne (atSource i) rest).release ∧
      OrderedPrefix (planOf atSource seam tail) t (stripWord tail labels) ∧
      RetainedMatches digits (ring x e) root width t ∧ MobileMatches digits (ring x e) base seam tail labels := by
  dsimp only
  let rest := (List.range' (i+1) (tail-i)).map atSource
  let plan := planOf atSource seam tail
  have ip : 0<i := Nat.lt_of_lt_of_le U.seam_pos is
  have newPending : s.release.pending=atSource i::rest := by
    rw [pending,show tail+1-i=(tail-i)+1 by omega,List.range'_succ]
    rfl
  by_cases onHead : e=addr base 0
  · have lim := U.tail_le
    have full : i=n := by
      rcases ingress_upstream_touch base ip (by omega) .left (loc.symm.trans onHead) with ⟨_,E⟩|⟨F,_⟩
      · exact E
      · cases F
    subst i
    have Eq : tail=n := by omega
    subst tail
    subst e
    have N : 1<n := by
      by_cases K : 1<n
      · exact K
      · apply sep.elim
        apply Fin.ext
        have h := (addr base 0).isLt
        have j := (rightNeighbor (addr base 0)).isLt
        omega
    have g0 := rg (width-1) (by have := C.pos; omega)
    rw [←join] at g0
    have both : ((lanes x (addr base 1) (rail seam 1)).gate &&
        (lanes x (addr base 0) .rd).gate)=true := by
      rw [g0,ug 1 (by decide) (by omega)]
      rfl
    exact alias_release_mark hp digits x root base width seam N C U join s plan size label P old mob
      (atSource n) rest (behind n (Nat.le_refl _) (Nat.le_refl _)) newPending
      sep win rdPrep only gate captured both
  · let labels := deposit label i (atSource i)
    have movedUp := ring_deposit hp digits atSource x e base seam tail i U is it loc sep onHead
      label mob only win gate captured (behind i (Nat.le_refl _) it)
    have W := deposit_ordered plan s label tail i ip it (atSource i) rest newPending behind P
    rcases BStarCopyRightRetainedClassify.noningress_classify hp digits x root e width C sep (join ▸ onHead)
      s plan _ size P old rg rdPrep with frame|⟨j,a,step,after⟩
    · exact ⟨s.releaseOne (atSource i) rest,labels,rfl,W,frame,movedUp⟩
    · have moved := rebase_same_up s (s.transfer j a) (stripWord tail label)
        (stripWord tail labels) (atSource i) rest step
      exact ⟨(s.transfer j a).releaseOne (atSource i) rest,labels,rfl,.mark W moved,after,movedUp⟩

end L4.BStarCopyRightWrappedRelease
