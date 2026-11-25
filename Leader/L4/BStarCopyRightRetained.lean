import Leader.L4.BStarCopyRightAckRetention

namespace L4.BStarCopyRightRetained
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarLongPackets BStarLongCommandData BStarLongPrep
open BStarCopyRightStrip BStarCopyRightMark BStarCopyFIFO BStarCopyFenceSaturation
open BStarCopyMarkedLedger BStarCopyRightDeposit

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B

structure Dest {a : LargeParams} {n : Nat} (b : LargeRows a)
    (x : Fin n→LargeSite a) (root : Fin n) (width : Nat) : Prop where
  fit : width≤n
  pos : 0<width
  header : oldH6 b x (addr root 0)=true
  body : ∀ j, 0<j → j<width → oldH6 b x (addr root j)=false
  inside : ∀ j<width, (longGeometry b (x (addr root j))).inside=true

/-- Indices run along travel order: the first retained destination is
the *last* physical INSIDE site; the final retained destination is H6. -/
def RetainedMatches {Tag : Type} (digits : Tag→BitVec 36) (x : X)
    (root : Fin n) (width : Nat) (s : Ledger Tag) : Prop :=
  ∀ j<width, Compatible digits (s.cells (width-1-j))
    (readLane (Sheet.index .rd) (x (addr root j)).long)

private theorem rd_pair_claim (g : Pair LongGeometry) (rs : List (At Sheet))
    (body : g.2.axes.h6=false) (d : DataClaim) (M : d∈orderedData g rs)
    (touch : L Sheet.rd∈d.slots ∨ R Sheet.rd∈d.slots) :
    d=hop (R .rd) (L .rd) := by
  have raw := BStarLongFenceTopology.selected_data_raw _ _ _ M
  have H := no_left_send _ _ raw
  have K := no_right_receive _ _ raw
  rcases touch with P|P
  · rcases List.mem_cons.mp P with P|P
    · exact (H.1 P.symm).elim
    · cases e : d.destination with
      | none => simp [e] at P
      | some a =>
        simp only [e,Option.toList_some,List.mem_singleton] at P
        subst a
        exact ((raw_rd_receive g d e).mp raw).elim And.right
          (fun h => Bool.noConfusion (body.symm.trans h.1))
  · rcases List.mem_cons.mp P with P|P
    · exact (raw_rd_send_body _ _ body P.symm).mp raw
    · cases e : d.destination with
      | none => simp [e] at P
      | some a =>
        simp only [e,Option.toList_some,List.mem_singleton] at P
        subst a
        exact (K.1 e).elim

/-- Actual selected internal RD move extends the *ordered* retained
ledger and preserves every other retained byte on the same raw mark. -/
theorem retained_internal {Tag : Type} (digits : Tag→BitVec 36)
    (x : X) (root : Fin n) (width j : Nat) (jfit : j+1<width)
    (C : Dest B x root width) (s : Ledger Tag) (plan up : List Tag)
    (P : OrderedPrefix plan s up) (old : RetainedMatches digits x root width s)
    (tag : Tag) (source : (s.cells (width-2-j)).mobile=some tag)
    (vacant : (s.cells (width-2-j+1)).mobile=none) :
    let e := addr root j
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    let g := oldPair B x e
    e≠rightNeighbor e →
    hop (R .rd) (L .rd)∈orderedData g (reserved (round g raw).prep) →
    (((view raw (R .rd)).gate && (view raw (L .rd)).gate)=true) →
    let t := s.transfer (width-2-j) tag
    OrderedPrefix plan t up ∧ RetainedMatches digits (ring x e) root width t := by
  dsimp only
  intro sep selected gates
  let e := addr root j
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let g := oldPair B x e
  let k := width-2-j
  have right : rightNeighbor e=addr root (j+1) := (addr_next root j).symm
  have eL : site e .left=addr root j := rfl
  have eR : site e .right=addr root (j+1) := right
  have A : width-1-(j+1)=k := by dsimp [k]; omega
  have D : width-1-j=k+1 := by dsimp [k]; omega
  have donor : Compatible digits (s.cells k) (view raw (R .rd)) := by
    rw [old_access x e (R .rd)]
    change Compatible digits (s.cells k) (readLane (Sheet.index .rd) (x (site e .right)).long)
    rw [eR,←A]
    exact old _ jfit
  have to : Compatible digits (s.cells (k+1)) (view raw (L .rd)) := by
    rw [old_access x e (L .rd)]
    change Compatible digits (s.cells (k+1)) (readLane (Sheet.index .rd) (x (site e .left)).long)
    rw [eL,←D]
    exact old _ (by omega)
  have ret : retains g (L .rd)=true := by
    simp [retains,L,show g.1.inside=true from C.inside j (by omega)]
  have ne : R Sheet.rd≠L Sheet.rd := by decide
  have F := physical_transfer digits plan s (ordered_prefix P).1 k tag g raw (R .rd) (L .rd)
    (hop (R .rd) (L .rd)) rfl rfl rfl selected ne ret gates source donor to vacant
  have J := BStarClearanceMobileJoined.joined_view k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x (rightNeighbor e))
  change view (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) =
    view (patchPair (patch g raw) raw) at J
  have cR := F.2.1
  have cL := F.2.2
  change Compatible digits ((s.transfer k tag).cells k) (view (patchPair (patch g raw) raw) (R .rd)) at cR
  change Compatible digits ((s.transfer k tag).cells (k+1)) (view (patchPair (patch g raw) raw) (L .rd)) at cL
  rw [←congrFun J (R .rd),new_access hp x e (R .rd) sep] at cR
  rw [←congrFun J (L .rd),new_access hp x e (L .rd) sep] at cL
  change Compatible digits ((s.transfer k tag).cells k)
    (readLane (Sheet.index .rd) (ring x e (site e .right)).long) at cR
  change Compatible digits ((s.transfer k tag).cells (k+1))
    (readLane (Sheet.index .rd) (ring x e (site e .left)).long) at cL
  rw [eL] at cL
  rw [eR] at cR
  refine ⟨.mark P (.interior s up k tag source vacant),?_⟩
  intro q hq
  change Compatible digits ((s.transfer k tag).cells (width-1-q))
    (readLane (Sheet.index .rd) (ring x e (addr root q)).long)
  by_cases qJ : q=j
  · subst q
    rw [D]
    exact cL
  · by_cases qR : q=j+1
    · subst q
      rw [A]
      exact cR
    · have wn := C.fit
      have Lh : addr root q≠e := fun h => qJ (addr_inj root (by omega) (by omega) h)
      have Rh : addr root q≠rightNeighbor e := fun h => qR (addr_inj root (by omega) (by omega) (h.trans right))
      have ext : ring x e (addr root q)=x (addr root q) := by simp [AllSizeS1Geometry.step,Lh,Rh]
      rw [ext,show (s.transfer k tag).cells (width-1-q) = (if width-1-q=k then (s.cells k).send else if width-1-q=k+1 then (s.cells (k+1)).receive tag else s.cells (width-1-q)) by rfl,if_neg (by dsimp [k]; omega),if_neg (by dsimp [k]; omega)]
      exact old q hq

/-- PC10/11 can never reserve the destination RD. An owner-licensed
INJECT concerns the source RS; it does not suppress a same-mark
retained RD transfer through aliased physical sites. -/
theorem no_rd_reservation_late (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (sd : Side)
    (ownerCode : ∀ offer∈(arbitration (round g raw).prep).1, offer.claim.lane=⟨sd,.rd⟩ →
      ∃ pc, 10≤pc ∧ prepOf pc=some offer.claim.op) :
    (⟨sd,.rd⟩ : At Sheet)∉reserved (round g raw).prep := by
  rcases inject_or_no_reservation g raw ⟨sd,.rd⟩ (.inl rfl) ownerCode with H|H
  · exact H
  · cases H.1

/-- Selected END at the physical terminal header is harmless on the
reachable ledger: that exact retained cell's mobile is empty.
This proves a frame only at the old right RD header. Even here an
independent seam ingress may change the old left RD cell. -/
theorem retained_header_frame {Tag : Type} (digits : Tag→BitVec 36)
    (x : X) (root e : Fin n) (width : Nat) (C : Dest B x root width)
    (s : Ledger Tag) (plan up : List Tag) (size : plan.length=width)
    (P : OrderedPrefix plan s up) (old : RetainedMatches digits x root width s)
    (right : rightNeighbor e=addr root 0) (sep : e≠rightNeighbor e) :
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    let g := oldPair B x e
    R Sheet.rd∉reserved (round g raw).prep →
      readLane (Sheet.index .rd) (ring x e (addr root 0)).long =
      readLane (Sheet.index .rd) (x (addr root 0)).long := by
  dsimp only
  intro no
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let a := R Sheet.rd
  have widthP := C.pos
  have E := terminal_empty (ordered_prefix P).1 (by omega)
  rw [size] at E
  have bin := (old 0 widthP).1
  rw [Nat.sub_zero,E] at bin
  have empty : (view raw a).mobile=.empty := by
    rw [old_access x e a]
    change (readLane (Sheet.index .rd) (x (rightNeighbor e)).long).mobile=.empty
    rw [right]
    exact bin
  have K := empty_patch_frame g raw a empty no
    (fun d dm D => ((no_right_receive g d
      (BStarLongFenceTopology.selected_data_raw _ _ _ dm)).1 D).elim)
  have J := BStarClearanceMobileJoined.joined_view k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x (rightNeighbor e))
  have out : view (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) a=view raw a :=
    (congrFun J a).trans K
  rw [new_access hp x e a sep,old_access x e a] at out
  change readLane (Sheet.index .rd) (ring x e (rightNeighbor e)).long =
    readLane (Sheet.index .rd) (x (rightNeighbor e)).long at out
  rw [right] at out
  exact out

/-- An earlier RS track swap and a simultaneous RD ledger transfer
commute because the swap preserves the ordered upstream word.
This is the exact immutable-mark algebra needed for aliased rails. -/
theorem transport_and_transfer {Tag : Type} (digits : Tag→BitVec 36)
    (x' : X) (root base : Fin n) (width seam tail q : Nat)
    (t : Ledger Tag) (plan : List Tag) (label : Nat→Option Tag) (tag : Tag)
    (qp : 0<q) (qt : q<tail) (empty : label q=none) (fromTag : label (q+1)=some tag)
    (retained : RetainedMatches digits x' root width t)
    (P : OrderedPrefix plan t (stripWord tail label))
    (upstream : MobileMatches digits x' base seam tail (swapTag label q tag)) :
    OrderedPrefix plan t (stripWord tail (swapTag label q tag)) ∧
      RetainedMatches digits x' root width t ∧
      MobileMatches digits x' base seam tail (swapTag label q tag) := by
  exact ⟨(stripWord_swap tail q qp qt label tag fromTag empty).symm ▸ P,retained,upstream⟩

theorem release_transfer_commute {Tag : Type}
    (s : Ledger Tag) (i : Nat) (a released : Tag) (todo : List Tag) :
    (s.transfer i a).releaseOne released todo=(s.releaseOne released todo).transfer i a := by
  cases s
  rfl

/-- Simultaneous owned RS release and a retained RD hop compose as
two independent ledger events for the same raw mark. The deposit
controller does not modify old RD queue premises. -/
theorem deposit_and_transfer {Tag : Type} (digits : Tag→BitVec 36)
    (x' : X) (root base : Fin n) (width seam tail q i : Nat)
    (plan : List Tag) (s : Ledger Tag) (label : Nat→Option Tag)
    (d a : Tag) (todo : List Tag)
    (afterIssue : OrderedPrefix plan (s.releaseOne d todo) (stripWord tail (deposit label q d)))
    (outgoing : (s.cells i).mobile=some a)
    (vacant : (s.cells (i+1)).mobile=none)
    (retained : RetainedMatches digits x' root width (s.transfer i a))
    (upstream : MobileMatches digits x' base seam tail (deposit label q d)) :
    let post := (s.transfer i a).releaseOne d todo
    OrderedPrefix plan post (stripWord tail (deposit label q d)) ∧
      RetainedMatches digits x' root width post ∧
      MobileMatches digits x' base seam tail (deposit label q d) := by
  dsimp only
  refine ⟨?_,retained,upstream⟩
  rw [release_transfer_commute]
  exact .mark afterIssue (.interior (s.releaseOne d todo) _ i a outgoing vacant)

private def bodyGeo : LongGeometry := ⟨⟨false,false,false,false,false,false⟩,true,false,0,false⟩

/-- Actual body routing has simultaneous retained RD and unretained
RS demands on distinct slots at the same physical mark. They are
both chosen in the arbiter, so a single-global-hop model is false. -/
theorem overlap_pair_fixture :
    hop (R .rd) (L .rd)∈orderedData (bodyGeo,bodyGeo) [] ∧
    hop (R .rs) (L .rs)∈orderedData (bodyGeo,bodyGeo) [] ∧
    retains (bodyGeo,bodyGeo) (L .rd)=true ∧
    retains (bodyGeo,bodyGeo) (L .rs)=false ∧
    ((hop (R .rd) (L .rd)).slots++(hop (R .rs) (L .rs)).slots).Nodup := by
  decide +kernel

end L4.BStarCopyRightRetained
