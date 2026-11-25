import Leader.L4.BStarCopyLeftCollector
import Leader.L4.BStarCopyRightRetained

namespace L4.BStarCopyLeftRetained
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarLongPackets BStarLongCommandData BStarLongPrep
open BStarCopyRightStrip (addr addr_next addr_inj)
open BStarCopyRightMark (old_access new_access)
open BStarCopyLeftStrip BStarCopyLeftMark BStarCopyLeftCollector BStarCopyFIFO BStarCopyFenceSaturation
open BStarCopyMarkedLedger
open BStarCopyRightRetained (Dest)

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B

/-- Retained LD indices increase with physical travel; the last
inside site is the terminal, not the H6 header. -/
def RetainedMatches {Tag : Type} (digits : Tag→BitVec 36) (x : X)
    (root : Fin n) (width : Nat) (s : Ledger Tag) : Prop :=
  ∀ j<width, Compatible digits (s.cells j)
    (readLane (Sheet.index .ld) (x (addr root j)).long)

theorem retained_internal {Tag : Type} (digits : Tag→BitVec 36)
    (x : X) (root : Fin n) (width j : Nat) (jfit : j+1<width)
    (C : Dest B x root width) (s : Ledger Tag) (plan up : List Tag)
    (P : OrderedPrefix plan s up) (old : RetainedMatches digits x root width s)
    (tag : Tag) (source : (s.cells (j)).mobile=some tag)
    (vacant : (s.cells (j+1)).mobile=none) :
    let e := addr root j
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    let g := oldPair B x e
    e≠rightNeighbor e →
    hop (L .ld) (R .ld)∈orderedData g (reserved (round g raw).prep) →
    (((view raw (L .ld)).gate && (view raw (R .ld)).gate)=true) →
    let t := s.transfer (j) tag
    OrderedPrefix plan t up ∧ RetainedMatches digits (ring x e) root width t := by
  dsimp only
  intro sep selected gates
  let e := addr root j
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let g := oldPair B x e
  let k := j
  have right : rightNeighbor e=addr root (j+1) := (addr_next root j).symm
  have eL : site e .left=addr root j := rfl
  have eR : site e .right=addr root (j+1) := right
  have donor : Compatible digits (s.cells k) (view raw (L .ld)) := by
    rw [old_access x e (L .ld)]
    exact old j (by omega)
  have to : Compatible digits (s.cells (k+1)) (view raw (R .ld)) := by
    rw [old_access x e (R .ld)]
    change Compatible digits (s.cells (k+1)) (readLane (Sheet.index .ld) (x (site e .right)).long)
    rw [eR]
    exact old _ jfit
  have ret : retains g (R .ld)=true := by
    have H : g.2.inside=true := by
      change (longGeometry B (x (rightNeighbor e))).inside=true
      rw [right]
      exact C.inside (j+1) jfit
    simp [retains,R,H]
  have ne : L Sheet.ld≠R Sheet.ld := by decide
  have F := physical_transfer digits plan s (ordered_prefix P).1 k tag g raw (L .ld) (R .ld)
    (hop (L .ld) (R .ld)) rfl rfl rfl selected ne ret gates source donor to vacant
  have J := BStarClearanceMobileJoined.joined_view k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x (rightNeighbor e))
  change view (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) =
    view (patchPair (patch g raw) raw) at J
  have cR := F.2.1
  have cL := F.2.2
  change Compatible digits ((s.transfer k tag).cells k) (view (patchPair (patch g raw) raw) (L .ld)) at cR
  change Compatible digits ((s.transfer k tag).cells (k+1)) (view (patchPair (patch g raw) raw) (R .ld)) at cL
  rw [←congrFun J (L .ld),new_access hp x e (L .ld) sep] at cR
  rw [←congrFun J (R .ld),new_access hp x e (R .ld) sep] at cL
  change Compatible digits ((s.transfer k tag).cells k)
    (readLane (Sheet.index .ld) (ring x e (site e .left)).long) at cR
  change Compatible digits ((s.transfer k tag).cells (k+1))
    (readLane (Sheet.index .ld) (ring x e (site e .right)).long) at cL
  rw [eL] at cR
  rw [eR] at cL
  refine ⟨.mark P (.interior s up k tag source vacant),?_⟩
  intro q hq
  change Compatible digits ((s.transfer k tag).cells q)
    (readLane (Sheet.index .ld) (ring x e (addr root q)).long)
  by_cases qJ : q=j
  · subst q
    exact cR
  · by_cases qR : q=j+1
    · subst q
      exact cL
    · have wn := C.fit
      have Lh : addr root q≠e := fun h => qJ (addr_inj root (by omega) (by omega) h)
      have Rh : addr root q≠rightNeighbor e := fun h => qR (addr_inj root (by omega) (by omega) (h.trans right))
      have ext : ring x e (addr root q)=x (addr root q) := by simp [AllSizeS1Geometry.step,Lh,Rh]
      rw [ext,show (s.transfer k tag).cells q = (if q=k then (s.cells k).send else if q=k+1 then (s.cells (k+1)).receive tag else s.cells q) by rfl,if_neg (by dsimp [k]; omega),if_neg (by dsimp [k]; omega)]
      exact old q hq

#print axioms retained_internal

/-- Selected END at the physical terminal LAST is harmless on the
reachable ledger: that exact retained cell's mobile is empty.
This proves a frame only at the old left LD LAST. Even here an
independent seam ingress may change the old right LS cell. -/
theorem retained_last_frame {Tag : Type} (digits : Tag→BitVec 36)
    (x : X) (root e : Fin n) (width : Nat) (C : Dest B x root width)
    (s : Ledger Tag) (plan up : List Tag) (size : plan.length=width)
    (P : OrderedPrefix plan s up) (old : RetainedMatches digits x root width s)
    (last : e=addr root (width-1)) (sep : e≠rightNeighbor e) :
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    let g := oldPair B x e
    L Sheet.ld∉reserved (round g raw).prep →
      readLane (Sheet.index .ld) (ring x e (addr root (width-1))).long =
      readLane (Sheet.index .ld) (x (addr root (width-1))).long := by
  dsimp only
  intro no
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let a := L Sheet.ld
  have widthP := C.pos
  have E := terminal_empty (ordered_prefix P).1 (by omega)
  rw [size] at E
  have bin := (old (width-1) (by omega)).1
  rw [E] at bin
  have empty : (view raw a).mobile=.empty := by
    rw [old_access x e a]
    change (readLane (Sheet.index .ld) (x e).long).mobile=.empty
    rw [last]
    exact bin
  have K := empty_patch_frame g raw a empty no
    (fun d dm D => ((no_left_receive g d
      (BStarLongFenceTopology.selected_data_raw _ _ _ dm)).2 D).elim)
  have J := BStarClearanceMobileJoined.joined_view k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x (rightNeighbor e))
  have out : view (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) a=view raw a :=
    (congrFun J a).trans K
  rw [new_access hp x e a sep,old_access x e a] at out
  change readLane (Sheet.index .ld) (ring x e e).long =
    readLane (Sheet.index .ld) (x e).long at out
  rw [←last]
  exact out

/-- The destination starts at the actual next H6 seam and uses
the increasing ordinal LD strip already certified by the chart. -/
theorem dest_of_strip (x : X) (base : Fin n) (seam width : Nat)
    (S : Strip B x base seam width) : Dest B x (addr base seam) width := by
  have index (j : Nat) : addr (addr base seam) j=addr base (seam+j) := by
    rw [addr_from,show j=0+j from (Nat.zero_add j).symm,addr_from (addr base seam) 0]
    simp only [Nat.zero_add]
    have E : addr (addr base seam) 0=addr base seam :=
      Fin.ext (Nat.mod_eq_of_lt (addr base seam).isLt)
    rw [E]
  refine ⟨S.width_le,S.width_pos,?_,?_,?_⟩
  · rw [index,Nat.add_zero]; exact S.dest_header
  · intro j J K
    rw [index]; exact S.ld_body _ (by omega) (by omega)
  · intro j J
    rw [index]; exact S.ld_in _ (by omega) (by omega)

open BStarCopyLeftDeposit

/-- Apply the LS tag move and the retained LD transfer on the same
new state, without requiring a scheduler interleaving. -/
theorem transport_and_transfer {Tag : Type} (digits : Tag→BitVec 36)
    (y : X) (root base : Fin n) (width seam j : Nat)
    (t : Ledger Tag) (plan : List Tag) (label : Nat→Option Tag) (tag : Tag)
    (inside : j+1<seam) (donor : label j=some tag) (vacant : label (j+1)=none)
    (retained : RetainedMatches digits y root width t)
    (P : OrderedPrefix plan t (headFirst seam label))
    (upstream : UpstreamMatches digits y base seam (moveTag label j tag)) :
    OrderedPrefix plan t (headFirst seam (moveTag label j tag)) ∧
      RetainedMatches digits y root width t ∧
      UpstreamMatches digits y base seam (moveTag label j tag) := by
  have E := congrArg List.reverse (upstreamWord_move seam j inside label tag donor vacant)
  change headFirst seam (moveTag label j tag)=headFirst seam label at E
  exact ⟨E.symm ▸ P,retained,upstream⟩

/-- A source deposition and a selected retained LD hop are independent
old-pair effects. The two certified post views compose without
resampling either side. -/
theorem deposit_and_transfer {Tag : Type} (digits : Tag→BitVec 36)
    (y : X) (root base : Fin n) (width seam q i : Nat)
    (plan : List Tag) (s : Ledger Tag) (label : Nat→Option Tag)
    (d a : Tag) (todo : List Tag)
    (afterIssue : OrderedPrefix plan (s.releaseOne d todo) (headFirst seam (deposit label q d)))
    (outgoing : (s.cells i).mobile=some a)
    (vacant : (s.cells (i+1)).mobile=none)
    (retained : RetainedMatches digits y root width (s.transfer i a))
    (upstream : UpstreamMatches digits y base seam (deposit label q d)) :
    let post := (s.transfer i a).releaseOne d todo
    OrderedPrefix plan post (headFirst seam (deposit label q d)) ∧
      RetainedMatches digits y root width post ∧
      UpstreamMatches digits y base seam (deposit label q d) := by
  dsimp only
  refine ⟨?_,retained,upstream⟩
  rw [BStarCopyRightRetained.release_transfer_commute]
  exact .mark afterIssue (.interior (s.releaseOne d todo) _ i a outgoing vacant)

#print axioms dest_of_strip
#print axioms transport_and_transfer
#print axioms deposit_and_transfer
#print axioms retained_last_frame
end L4.BStarCopyLeftRetained
