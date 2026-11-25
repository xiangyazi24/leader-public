import Leader.L4.BStarCopyRightMixed

namespace L4.BStarCopyRightScopedDeposit
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

/-- Genuine justified right INJECT with vacancy required only on the
tracked active-source suffix, and its independent retained
projection. Away from ingress, the destination RD can transfer
while the RS source deposits. At ingress the injected slot is
necessarily the unique old head, and its reservation suppresses
the competing cross rather than forwarding freshly injected mail. -/
theorem scoped_deposit {Tag : Type} (digits : Tag→BitVec 36) (atSource : Nat→Tag)
    (x : X) (root base e : Fin n) (width seam tail i : Nat) (side : Side)
    (C : Dest B x root width) (U : Strip B x base seam tail)
    (join : addr base 0=addr root (width-1)) (sep : e≠rightNeighbor e)
    (s : Ledger Tag) (size : (planOf atSource seam tail).length=width)
    (label : Nat→Option Tag)
    (P : OrderedPrefix (planOf atSource seam tail) s (stripWord tail label))
    (old : RetainedMatches digits x root width s)
    (matched : MobileMatches digits x base seam tail label)
    (rdGate : ∀ j<width, (readLane (Sheet.index .rd) (x (addr root j)).long).gate=true)
    (rdPrep : NoRDPrep hp x root e width)
    (is : seam≤i) (it : i≤tail) (loc : site e side=addr base i)
    (scope : NoPrepExcept hp x e base seam tail i)
    (win : BStarCopyInjection.injection side true∈
      (arbitration (round (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).prep).1)
    (gate : (lanes x (addr base i) .rs).gate=true)
    (captured : (lanes x (addr base i) .rs).frozen=.data (digits (atSource i)))
    (emptyBehind : ∀ j, i≤j → j≤tail → label j=none)
    (pending : s.release.pending=(List.range' i (tail+1-i)).map atSource) :
    let rest := (List.range' (i+1) (tail-i)).map atSource
    let labels := deposit label i (atSource i)
    ∃ t, t.release=(s.releaseOne (atSource i) rest).release ∧
      OrderedPrefix (planOf atSource seam tail) t (stripWord tail labels) ∧
      RetainedMatches digits (ring x e) root width t ∧
      MobileMatches digits (ring x e) base seam tail labels := by
  dsimp only
  let rest := (List.range' (i+1) (tail-i)).map atSource
  let labels := deposit label i (atSource i)
  let plan := planOf atSource seam tail
  let t := s.releaseOne (atSource i) rest
  have I : 0<i := Nat.lt_of_lt_of_le U.seam_pos is
  have next : s.release.pending=atSource i::rest := by
    rw [pending,show tail+1-i=(tail-i)+1 by omega,List.range'_succ]
    rfl
  have mob : MobileMatches digits (ring x e) base seam tail labels :=
    ring_deposit hp digits atSource x e base side seam tail i U is it loc sep label matched scope
      win gate captured (emptyBehind i (by omega) it)
  have ordered : OrderedPrefix plan t (stripWord tail labels) :=
    deposit_ordered plan s label tail i I it (atSource i) rest next emptyBehind P
  by_cases head : e=addr base 0
  · subst e
    have pos := U.seam_pos
    have bound := U.tail_lt
    have kPos : 0<i := by omega
    have srcSide : side=.right := by
      cases side with
      | right => rfl
      | left =>
        have Z : addr base 0=addr base i := loc
        have v := addr_inj base (by omega) (by omega) Z
        omega
    subst side
    have rloc := (addr_next base 0).trans loc
    have same : i=1 := by
      have v := addr_inj base (by omega) (by omega) rloc
      omega
    let e := addr base 0
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    let g := oldPair B x e
    let rs := reserved (round g raw).prep
    have shr : rail seam 1=.rs := if_neg (by omega)
    have booked : R (rail seam (0+1))∈rs := by
      change R (rail seam 1)∈rs
      rw [shr]
      exact List.mem_map.mpr ⟨_,win,rfl⟩
    have ignore := strip_reserved_blocks (b:=B) (x:=x) (base:=base) (seam:=seam) (i:=0) rs (.inr booked)
    have frame := (ingress_quiet hp digits x root base width seam tail C U join s plan size label P old
      matched sep rdPrep (.inl ignore)).1
    exact ⟨t,rfl,ordered,frame,mob⟩
  · rcases noningress_classify hp digits x root e width C sep (join ▸ head) s plan _ size P old rdGate rdPrep with
      frame|⟨k,a,changeQ,carry⟩
    · exact ⟨t,rfl,ordered,frame,mob⟩
    · have moved := rebase_same_up s (s.transfer k a) (stripWord tail label)
          (stripWord tail labels) (atSource i) rest changeQ
      exact ⟨(s.transfer k a).releaseOne (atSource i) rest,rfl,.mark ordered moved,carry,mob⟩

end L4.BStarCopyRightScopedDeposit
