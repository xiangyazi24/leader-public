import Leader.L4.BStarCopyRightRetained

namespace L4.BStarCopyRightRetainedClassify
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarLongPackets BStarLongCommandData BStarLongPrep
open BStarCopyRightStrip BStarCopyRightMark BStarCopyFIFO BStarCopyFenceSaturation
open BStarCopyMarkedLedger BStarCopyRightRetained

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B

def NoRDPrep (x : X) (root e : Fin n) (width : Nat) : Prop :=
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let rs := reserved (round (oldPair B x e) raw).prep
  ∀ q<width, ∀ s, site e s=addr root q → (⟨s,.rd⟩ : At Sheet)∉rs

private theorem body_claim (g : Pair LongGeometry) (rs : List (At Sheet))
    (H : g.2.axes.h6=false) (d : DataClaim) (D : d∈orderedData g rs) (s : Side)
    (M : (⟨s,.rd⟩ : At Sheet)∈d.slots) : d=hop (R .rd) (L .rd) := by
  have raw := BStarLongFenceTopology.selected_data_raw _ _ _ D
  rcases List.mem_cons.mp M with Q|Q
  · cases s with
    | left => exact ((no_left_send _ _ raw).1 Q.symm).elim
    | right => exact (raw_rd_send_body _ _ H Q.symm).mp raw
  · obtain ⟨a,A⟩ : ∃ a,d.destination=some a := by
      cases E : d.destination with
      | none => simp [E] at Q
      | some a => exact ⟨a,rfl⟩
    have eq : d.destination=some ⟨s,.rd⟩ := by
      have h : (⟨s,.rd⟩ : At Sheet)=a := by
        simpa only [A,Option.toList_some,List.mem_singleton] using Q
      rw [A,h]
    cases s with
    | left =>
      exact ((raw_rd_receive _ _ eq).mp raw).elim And.right
        (fun h => Bool.noConfusion (H.symm.trans h.1))
    | right => exact ((no_right_receive _ _ raw).1 eq).elim

/-- Strong whole retained projection away from the one ingress mark.
A tagged old mobile moves iff the actual selected RD row has old
vacancy; otherwise every retained lane frames. Deliberately leaves
the upstream projection wholly independent, even on alias marks. -/
theorem noningress_classify {Tag : Type} (digits : Tag→BitVec 36)
    (x : X) (root e : Fin n) (width : Nat) (C : Dest B x root width)
    (sep : e≠rightNeighbor e) (excludeIngress : e≠addr root (width-1))
    (s : Ledger Tag) (plan up : List Tag) (size : plan.length=width)
    (P : OrderedPrefix plan s up)
    (old : RetainedMatches digits x root width s)
    (gate : ∀ j<width, (readLane (Sheet.index .rd) (x (addr root j)).long).gate=true)
    (prep : NoRDPrep hp x root e width) :
    RetainedMatches digits (ring x e) root width s ∨
      ∃ (k : Nat) (tag : Tag),
        OrderedStep s up (s.transfer k tag) up ∧
        RetainedMatches digits (ring x e) root width (s.transfer k tag) := by
  have fit := C.fit
  have pos := C.pos
  by_cases inside : ∃ j, j+1<width ∧ e=addr root j
  · obtain ⟨j,jw,rfl⟩ := inside
    let mark := addr root j
    let g := oldPair B x mark
    let raw : Pair (BitVec LW) := ((x mark).long,(x (rightNeighbor mark)).long)
    let u := R Sheet.rd
    let v := L Sheet.rd
    let d := hop u v
    let rs := reserved (round g raw).prep
    let k := width-2-j
    have Rj : rightNeighbor mark=addr root (j+1) := (addr_next root j).symm
    have H : g.2.axes.h6=false := by
      change oldH6 B x (rightNeighbor mark)=false
      rw [Rj]
      exact C.body _ (by omega) jw
    have src := (old (j+1) jw).1
    have dst := (old j (by omega)).1
    have hsrc : (view raw u).mobile=encode digits (s.cells k).mobile := by
      rw [old_access x mark u]
      change (readLane (Sheet.index .rd) (x (rightNeighbor mark)).long).mobile=_
      rw [Rj]
      have K : width-1-(j+1)=k := by dsimp [k]; omega
      exact K ▸ src
    have hdst : (view raw v).mobile=encode digits (s.cells (k+1)).mobile := by
      rw [old_access x mark v]
      have K : width-1-j=k+1 := by dsimp [k]; omega
      exact K ▸ dst
    have gu : (view raw u).gate=true := by
      rw [old_access x mark u]
      change (readLane (Sheet.index .rd) (x (rightNeighbor mark)).long).gate=true
      rw [Rj]; exact gate _ jw
    have gv : (view raw v).gate=true := by
      rw [old_access x mark v]
      exact gate _ (by omega)
    have G : ((view raw u).gate && (view raw v).gate)=true := by simp [gu,gv]
    have blocked (Hq : d∉orderedData g rs ∨ dataEffects g (view raw) d=[]) :
        RetainedMatches digits (ring x mark) root width s := by
      intro q qw
      have frameSide (side : Side) (loc : site mark side=addr root q) :
          readLane (Sheet.index .rd) (ring x mark (addr root q)).long =
            readLane (Sheet.index .rd) (x (addr root q)).long := by
        let slot : At Sheet := ⟨side,.rd⟩
        have Hs := joined_spectator hp (x mark,x (rightNeighbor mark)) slot (prep q qw side loc)
        have Hs := Hs (fun c M l A => by
          have T := data_lane_claim g (view raw) c slot l A
          have Eq := body_claim g rs H c M side T
          change c=d at Eq
          subst c
          rcases Hq with Hq|Hq
          · exact Hq M
          · change (slot,l)∈dataEffects g (view raw) d at A
            rw [Hq] at A
            exact List.not_mem_nil A)
        change view (Pair.map LargeSite.long (largePair B (x mark,x (rightNeighbor mark)))) slot = view raw slot at Hs
        rw [new_access hp x mark slot sep,old_access x mark slot] at Hs
        change readLane (Sheet.index .rd) (ring x mark (site mark side)).long =
          readLane (Sheet.index .rd) (x (site mark side)).long at Hs
        rwa [loc] at Hs
      change Compatible digits (s.cells (width-1-q)) (readLane (Sheet.index .rd) (ring x mark (addr root q)).long)
      by_cases Lp : addr root q=mark
      · rw [frameSide .left Lp.symm]; exact old q qw
      · by_cases Rp : addr root q=rightNeighbor mark
        · rw [frameSide .right Rp.symm]; exact old q qw
        · rw [show ring x mark (addr root q)=x (addr root q) from by simp [AllSizeS1Geometry.step,Lp,Rp]]
          exact old q qw
    by_cases M : d∈orderedData g rs
    · cases a : (s.cells k).mobile with
      | none =>
        apply Or.inl (blocked (.inr ?_))
        apply hop_no_effect
        exact .inl (hsrc.trans (by rw [a]; rfl))
      | some tag =>
        cases b : (s.cells (k+1)).mobile with
        | none =>
          have R := retained_internal hp digits x root width j jw C s plan up P old tag a b sep M G
          exact .inr ⟨k,tag,.interior s up k tag a b,R.2⟩
        | some other =>
          apply Or.inl (blocked (.inr ?_))
          apply hop_no_effect
          exact .inr ⟨G,by rw [hdst,b]; intro H; contradiction⟩
    · exact .inl (blocked (.inl M))
  · apply Or.inl
    intro j jw
    have noL : addr root j≠e := by
      intro a
      by_cases last : j=width-1
      · exact excludeIngress (last ▸ a.symm)
      · exact inside ⟨j,by omega,a.symm⟩
    by_cases noR : addr root j=rightNeighbor e
    · by_cases zero : j=0
      · subst j
        rw [retained_header_frame hp digits x root e width C s plan up size P old noR.symm sep
          (prep 0 jw .right noR.symm)]
        exact old 0 jw
      · have T : e=addr root (j-1) := by
          apply rightNeighbor_inj
          rw [←addr_next,show j-1+1=j by omega]
          exact noR.symm
        exact (inside ⟨j-1,by omega,T⟩).elim
    · rw [show ring x e (addr root j)=x (addr root j) from by simp [AllSizeS1Geometry.step,noL,noR]]
      exact old j jw

def clearHead {T : Type} (lab : Nat→Option T) (i : Nat) : Option T :=
  if i=1 then none else lab i

theorem stripWord_clear {T : Type} (label : Nat→Option T) (tail : Nat)
    (pos : 0<tail) (tag : T) (H : label 1=some tag) :
    stripWord tail label=tag::stripWord tail (clearHead label) := by
  cases tail with
  | zero => contradiction
  | succ k =>
    unfold stripWord
    rw [List.range'_succ]
    simp only [List.flatMap_cons,H,Option.toList_some,clearHead,if_true,Option.toList_none,List.nil_append,List.singleton_append]
    congr 1
    suffices ∀ q : List Nat, (∀ j∈q, 2≤j) →
      q.flatMap (fun j => (label j).toList)=
      q.flatMap (fun j => (if j=1 then none else label j).toList) by
      apply this
      intro j M
      obtain ⟨l,_,EQ⟩ := List.mem_range'.mp M
      omega
    intro q Q
    induction q with
    | nil => rfl
    | cons a q ih =>
      have n : a≠1 := by have := Q a (by simp); omega
      simp only [List.flatMap_cons,if_neg n]
      exact congrArg _ (ih (fun i M => Q i (List.mem_cons_of_mem _ M)))

/-- Exact ingress branch of the independent projections. The actual
old head tag is consumed from the stream, first queue receives it,
and all other tracked lanes are framed, including an aliased RD
terminal END on the same seam. -/
theorem ingress_cross {Tag : Type} (digits : Tag→BitVec 36)
    (x : X) (root base : Fin n) (width seam tail : Nat)
    (C : Dest B x root width) (U : Strip B x base seam tail)
    (join : addr base 0=addr root (width-1))
    (s : Ledger Tag) (plan : List Tag) (size : plan.length=width)
    (label : Nat→Option Tag)
    (P : OrderedPrefix plan s (stripWord tail label))
    (old : RetainedMatches digits x root width s)
    (matched : MobileMatches digits x base seam tail label)
    (tag : Tag) (positive : label 1=some tag) (empty : (s.cells 0).mobile=none) :
    let e := addr base 0
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    let g := oldPair B x e
    let u := R (rail seam 1)
    let v := L Sheet.rd
    e≠rightNeighbor e →
    NoRDPrep hp x root e width →
    hop u v∈orderedData g (reserved (round g raw).prep) →
    (((view raw u).gate && (view raw v).gate)=true) →
    OrderedPrefix plan (s.receiveFirst tag) (stripWord tail (clearHead label)) ∧
      RetainedMatches digits (ring x e) root width (s.receiveFirst tag) ∧
      MobileMatches digits (ring x e) base seam tail (clearHead label) := by
  dsimp only
  intro sep prep selected gates
  let e := addr base 0
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let u := R (rail seam 1)
  let v := L Sheet.rd
  let Ls := fun (z : X) (a : At Sheet) =>
    readLane (Sheet.index a.occurrence) (z (site e a.side)).long
  have uLoc : site e u.side=addr base 1 := (addr_next base 0).symm
  have vLoc : site e v.side=addr root (width-1) := join
  have widthP := C.pos
  have pos := U.seam_pos
  have len := U.seam_le_tail
  have T : 0<tail := by omega
  have inTag : (Ls x u).mobile=encode digits (some tag) := by
    change (readLane (Sheet.index (rail seam 1)) (x (site e u.side)).long).mobile=_
    rw [uLoc]
    exact (matched 1 (by omega) (by omega)).trans (congrArg (encode digits) positive)
  have oldV : Compatible digits (s.cells 0) (Ls x v) := by
    change Compatible digits (s.cells 0) (readLane (Sheet.index .rd) (x (site e v.side)).long)
    rw [vLoc]
    have hv := old (width-1) (by omega)
    rwa [Nat.sub_self] at hv
  have ret : retains (oldPair B x e) v=true := by
    simp [retains,v,L,show (oldPair B x e).1.inside=true from U.head_in]
  have G : ((Ls x u).gate && (Ls x v).gate)=true := by
    dsimp only [Ls]
    rw [←old_access x e u,←old_access x e v]
    exact gates
  have hP : OrderedPrefix plan s (tag::stripWord tail (clearHead label)) := (stripWord_clear label tail T tag positive) ▸ P
  obtain ⟨P',uAfter,vAfter⟩ := BStarCopyUpstreamTags.ring_cross_head hp digits tag
    (stripWord tail (clearHead label)) hP x e sep (hop u v) v rfl rfl selected
    (by intro H; have Q := congrArg At.side H; contradiction) ret G inTag oldV empty
  refine ⟨P',?_,?_⟩
  · intro q Q
    have fw := C.fit
    by_cases H : q=width-1
    · subst q
      change Compatible digits ((s.receiveFirst tag).cells (width-1-(width-1))) _
      rw [Nat.sub_self]
      change Compatible digits ((s.receiveFirst tag).cells 0)
        (readLane (Sheet.index .rd) (ring x e (site e v.side)).long) at vAfter
      rw [vLoc] at vAfter
      exact vAfter
    · have untouchedCell : (s.receiveFirst tag).cells (width-1-q)=s.cells (width-1-q) := by
        simp [Ledger.receiveFirst,show width-1-q≠0 by omega]
      change Compatible digits ((s.receiveFirst tag).cells (width-1-q))
        (readLane (Sheet.index .rd) (ring x e (addr root q)).long)
      rw [untouchedCell]
      have noL : addr root q≠e := fun M => H (addr_inj root (by omega) (by omega) (M.trans join))
      by_cases isR : addr root q=rightNeighbor e
      · by_cases zero : q=0
        · subst q
          rw [retained_header_frame hp digits x root e width C s plan _ size P old isR.symm sep
            (prep 0 Q .right isR.symm)]
          exact old 0 Q
        · have eq : e=addr root (q-1) := by
            apply rightNeighbor_inj
            rw [←addr_next root (q-1),show q-1+1=q by omega]
            exact isR.symm
          have impossible := addr_inj root (by omega) (by omega) (join.symm.trans eq)
          omega
      · rw [show ring x e (addr root q)=x (addr root q) from by simp [AllSizeS1Geometry.step,noL,isR]]
        exact old q Q
  · intro j JP JT
    by_cases H : j=1
    · subst j
      change (Ls (ring x e) u).mobile=encode digits none at uAfter
      change (readLane (Sheet.index (rail seam 1)) (ring x e (site e u.side)).long).mobile=encode digits none at uAfter
      rw [uLoc] at uAfter
      exact uAfter
    · rw [ring_other_positions hp x base 0 j tail T JP JT U.tail_lt (by omega) H]
      simp only [clearHead,if_neg H]
      exact matched j JP JT

end L4.BStarCopyRightRetainedClassify
