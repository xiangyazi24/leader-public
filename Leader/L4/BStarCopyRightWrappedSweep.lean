import Leader.L4.BStarCopyRightWrappedPairs
import Leader.L4.BStarCopyRightDataSweep

namespace L4.BStarCopyRightWrappedSweep
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarLongPackets BStarLongCommandData BStarLongPrep
open BStarCopyRightStrip BStarCopyRightMark BStarCopyFIFO BStarCopyFenceSaturation
open BStarCopyMarkedLedger BStarCopyRightRetained BStarCopyRightRetainedClassify

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B

open BStarCopyRightDataSweep BStarCopyRightWrappedGeometry BStarCopyRightWrappedPairs
open BStarCopyUpstreamTags
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

private theorem ingress_other_slot (x : X) (a : Fin n) (seam tail : Nat)
    (C : WrappedStrip B x a seam tail) (sep : addr a 0≠rightNeighbor (addr a 0))
    (prep : NoUpPrep hp x a (addr a 0) seam tail)
    (j : Nat) (jp : 0<j) (jt : j≤tail) (ne : j≠1) :
    readLane (Sheet.index (rail seam j)) (ring x (addr a 0) (addr a j)).long =
      readLane (Sheet.index (rail seam j)) (x (addr a j)).long := by
  have lim := C.tail_le
  by_cases eq : addr a j=addr a 0
  · obtain ⟨_,J⟩ | ⟨D,_⟩ := ingress_upstream_touch a jp (by omega) .left eq
    · subst j
      have ends : tail=n := by omega
      subst tail
      have S : rail seam n=.rs := if_neg (Nat.not_lt_of_ge C.seam_le_tail)
      have safe := prep n jp jt .left eq.symm
      have ready : L .rs∉reserved (round (oldPair B x (addr a 0))
          ((x (addr a 0)).long,(x (rightNeighbor (addr a 0))).long)).prep := by
        rwa [S] at safe
      rw [S]
      exact ingress_tail_frame hp x a seam C sep ready
    · cases D
  · have other : addr a j≠rightNeighbor (addr a 0) := by
      intro E
      obtain ⟨D,_⟩ | ⟨_,J⟩ := ingress_upstream_touch a jp (by omega) .right E
      · cases D
      · exact ne J
    rw [show ring x (addr a 0) (addr a j)=x (addr a j) from by simp [AllSizeS1Geometry.step,eq,other]]

theorem retains_iff_head {a : LargeParams} {n : Nat} {b : LargeRows a}
    {x : Fin n→LargeSite a} {base : Fin n} {seam tail : Nat}
    (C : WrappedStrip b x base seam tail) (i : Nat) :
    retains (oldPair b x (addr base i)) (L (rail seam i)) = decide (i=0) := by
  by_cases h : i=0
  · subst i
    simp [rail,C.seam_pos,retains,L,show
      (oldPair b x (addr base 0)).1.inside=true from C.head_in]
  · by_cases j : i<seam
    · simp [rail,j,retains,L,h,show (oldPair b x (addr base i)).1.inside=false
        from C.pads_out _ (by omega) j]
    · simp [rail,j,retains,L,h]

theorem selected_adjacent {a : LargeParams} {n : Nat} {b : LargeRows a}
    {x : Fin n→LargeSite a} {base : Fin n} {seam tail : Nat}
    (C : WrappedStrip b x base seam tail) (i : Nat) (it : i<tail)
    (rsv : List (At Sheet)) (d : DataClaim)
    (M : d∈orderedData (oldPair b x (addr base i)) rsv)
    (D : d.destination=some (L (rail seam i))) :
    d=hop (R (rail seam (i+1))) (L (rail seam i)) :=
  (wrapped_raw_incoming C i it d D).mp (BStarLongFenceTopology.selected_data_raw _ _ _ M)

theorem joined_strip_hop {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
    {Label : Type} (digits : Label→BitVec 36) (tag : Label)
    (x : Fin n→LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (base : Fin n) (seam tail i : Nat) (pos : 0<i) (it : i<tail)
    (C : WrappedStrip (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp) x base seam tail)
    (d : DataClaim) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let edge := addr base i
    let xx := (x edge,x (rightNeighbor edge))
    let raw := Pair.map LargeSite.long xx
    let g := oldPair b x edge
    let u := R (rail seam (i+1))
    let v := L (rail seam i)
    d∈orderedData g (reserved (round g raw).prep) →
    d.destination=some v →
    ((view raw u).gate && (view raw v).gate)=true →
    (view raw u).mobile=encode digits (some tag) →
    (view raw v).mobile=encode digits none →
    let out := view (Pair.map LargeSite.long (largePair b xx))
    (out u).mobile=encode digits none ∧
    (out v).mobile=encode digits (some tag) ∧
    (out v).retained=(view raw v).retained := by
  dsimp only
  intro M D G U V
  have E := selected_adjacent C i it _ d M D
  subst d
  apply nonretaining_tag_joined hp digits tag _ _ _ _ rfl rfl rfl M
  · intro H
    have T := congrArg At.side H
    contradiction
  · change retains (oldPair _ x (addr base i)) (L (rail seam i)) = false
    rw [retains_iff_head C i]
    exact decide_eq_false (by omega)
  · exact G
  · exact U
  · exact V

theorem selected_outgoing {a : LargeParams} {n : Nat} {b : LargeRows a}
    {x : Fin n→LargeSite a} {base : Fin n} {seam tail : Nat}
    (C : WrappedStrip b x base seam tail) (i : Nat) (it : i<tail)
    (rsv : List (At Sheet)) (d : DataClaim)
    (M : d∈orderedData (oldPair b x (addr base i)) rsv)
    (S : d.source=R (rail seam (i+1))) :
    d=hop (R (rail seam (i+1))) (L (rail seam i)) := by
  let g := oldPair b x (addr base i)
  have raw : d∈dataClaims g := BStarLongFenceTopology.selected_data_raw _ _ _ M
  have right := (addr_next base i).symm
  by_cases pad : i+1<seam
  · have H : g.2.axes.h6=false := by
      change oldH6 b x (rightNeighbor (addr base i))=false
      rw [right]; exact C.rd_noheader _ (by omega) pad
    have q : i<seam := by omega
    simp only [rail,if_pos q,if_pos pad] at S ⊢
    exact (raw_rd_send_body _ _ H S).mp raw
  · have T : d.source=R .rs := by simpa only [rail,if_neg pad] using S
    have cases := (raw_rs_send _ _ T).mp raw
    by_cases atSeam : i+1=seam
    · have H : g.2.axes.h6=true := by
        change oldH6 b x (rightNeighbor (addr base i))=true
        rw [right,atSeam]; exact C.rs_header
      have q : i<seam := by omega
      simp only [rail,if_neg pad,if_pos q]
      rcases cases with ⟨_,_,E⟩|⟨N,_⟩
      · exact E
      · rw [H] at N
        contradiction
    · have H : g.2.axes.h6=false := by
        change oldH6 b x (rightNeighbor (addr base i))=false
        rw [right]; exact C.rs_nonheader _ (by omega) (by omega)
      have q : ¬i<seam := by omega
      simp only [rail,if_neg pad,if_neg q]
      rcases cases with ⟨N,_⟩|⟨_,_,_,_,E⟩
      · rw [H] at N
        contradiction
      · exact E

set_option maxHeartbeats 400000 in
/-- On an interior physical edge both strip slots have exactly one
possible selected data demand, with no other read/write aliases. Any
other simultaneous selected row (other lane or other owner) frames
the two slots. This includes the seam and all center padding. -/
theorem strip_pair_claim {a : LargeParams} {n : Nat} {b : LargeRows a}
    {x : Fin n→LargeSite a} {base : Fin n} {seam tail : Nat}
    (C : WrappedStrip b x base seam tail) (i : Nat) (it : i<tail)
    (rsv : List (At Sheet)) (d : DataClaim)
    (M : d∈orderedData (oldPair b x (addr base i)) rsv)
    (T : L (rail seam i)∈d.slots ∨ R (rail seam (i+1))∈d.slots) :
    d=hop (R (rail seam (i+1))) (L (rail seam i)) := by
  have raw := BStarLongFenceTopology.selected_data_raw _ _ _ M
  have l := no_left_send _ _ raw
  have rr := no_right_receive _ _ raw
  unfold Claim.slots at T
  cases D : d.destination with
  | none =>
    simp only [D,Option.toList_none,List.mem_cons,List.not_mem_nil,or_false] at T
    rcases T with T|T
    · by_cases h : i<seam
      · exact (l.1 (T.symm.trans (congrArg L (if_pos h)))).elim
      · exact (l.2 (T.symm.trans (congrArg L (if_neg h)))).elim
    · exact selected_outgoing C i it _ _ M T.symm
  | some dst =>
    simp only [D,Option.toList_some,List.mem_cons,List.not_mem_nil,or_false] at T
    rcases T with (T|T)|(T|T)
    · cases h : rail seam i with
      | ls => simp [rail] at h <;> split at h <;> contradiction
      | ld => simp [rail] at h <;> split at h <;> contradiction
      | rs => exact (l.2 (T.symm.trans (congrArg L h))).elim
      | rd => exact (l.1 (T.symm.trans (congrArg L h))).elim
    · exact selected_adjacent C i it _ _ M (D.trans (congrArg some T.symm))
    · exact selected_outgoing C i it _ _ M T.symm
    · cases h : rail seam (i+1) with
      | ls => simp [rail] at h <;> split at h <;> contradiction
      | ld => simp [rail] at h <;> split at h <;> contradiction
      | rs => exact (rr.2 (D.trans (congrArg some (T.symm.trans (congrArg R h))))).elim
      | rd => exact (rr.1 (D.trans (congrArg some (T.symm.trans (congrArg R h))))).elim

#print axioms strip_pair_claim

theorem strip_pair_frame {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
    (x : Fin n→LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (base : Fin n) (seam tail i : Nat) (it : i<tail)
    (C : WrappedStrip (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp) x base seam tail) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let edge := addr base i
    let xx := (x edge,x (rightNeighbor edge))
    let g := oldPair b x edge
    let raw := Pair.map LargeSite.long xx
    let rs := reserved (round g raw).prep
    let u := R (rail seam (i+1))
    let v := L (rail seam i)
    let h := hop u v
    (h∉orderedData g rs ∨ (view raw u).mobile=.empty ∨
      (((view raw u).gate && (view raw v).gate)=true ∧ (view raw v).mobile≠.empty)) →
    ∀ s, (s=u ∨ s=v) → s∉rs →
      view (Pair.map LargeSite.long (largePair b xx)) s=view raw s := by
  dsimp only
  intro quiet s S np
  apply joined_spectator hp _ s np
  intro d D a A
  have M := data_lane_claim _ _ _ _ _ A
  have TS : L (rail seam i)∈d.slots ∨ R (rail seam (i+1))∈d.slots := by
    rcases S with rfl|rfl
    · exact .inr M
    · exact .inl M
  have shape : d=hop (R (rail seam (i+1))) (L (rail seam i)) :=
    strip_pair_claim C i it _ d D TS
  subst d
  rcases quiet with no|blocked
  · exact no D
  · have Z := hop_no_effect (Pair.map (longGeometry (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp))
        (x (addr base i), x (rightNeighbor (addr base i)))) _ _ _ blocked
    rw [Z] at A
    exact List.not_mem_nil A

theorem tail_claim_frame {a : LargeParams} {n : Nat} {b : LargeRows a}
    {x : Fin n→LargeSite a} {base : Fin n} {seam tail : Nat}
    (C : WrappedStrip b x base seam tail) (rs : List (At Sheet)) (d : DataClaim)
    (M : d∈orderedData (oldPair b x (addr base tail)) rs) :
    L (rail seam tail)∉d.slots := by
  intro T
  have raw := BStarLongFenceTopology.selected_data_raw _ _ _ M
  have q : ¬tail<seam := by have := C.seam_le_tail; omega
  unfold Claim.slots at T
  rcases List.mem_cons.mp T with E|E
  · simp only [rail,if_neg q] at E
    exact (no_left_send _ _ raw).2 E.symm
  · have D : d.destination=some (L (rail seam tail)) := by
      cases h : d.destination with
      | none => simp [h] at E
      | some s =>
        simp only [h,Option.toList_some,List.mem_singleton] at E
        rw [E]
    exact wrapped_tail_no_ingress C d raw D

theorem joined_tail_frame {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
    (x : Fin n→LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (base : Fin n) (seam tail : Nat)
    (C : WrappedStrip (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp) x base seam tail) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let edge := addr base tail
    let xx := (x edge,x (rightNeighbor edge))
    let g := oldPair b x edge
    let raw := Pair.map LargeSite.long xx
    let s := L (rail seam tail)
    s∉reserved (round g raw).prep →
      view (Pair.map LargeSite.long (largePair b xx)) s=view raw s := by
  dsimp only
  intro Q
  apply joined_spectator hp _ _ Q
  intro d M a A
  exact tail_claim_frame C _ d M (data_lane_claim _ _ _ _ _ A)

theorem ring_transport {Label : Type} (digits : Label→BitVec 36) (tag : Label)
    (x : X) (base : Fin n) (seam tail i : Nat) (pos : 0<i) (it : i<tail)
    (C : WrappedStrip B x base seam tail) (d : DataClaim) (label : Nat→Option Label)
    (labels : MobileMatches digits x base seam tail label)
    (source : label (i+1)=some tag) (vacant : label i=none) :
    let edge := addr base i
    let raw : Pair (BitVec LW) := ((x edge).long,(x (rightNeighbor edge)).long)
    let g := oldPair B x edge
    let u := R (rail seam (i+1))
    let v := L (rail seam i)
    edge≠rightNeighbor edge →
    d∈orderedData g (reserved (round g raw).prep) →
    d.destination=some v →
    ((view raw u).gate && (view raw v).gate)=true →
    MobileMatches digits (updateRing x edge) base seam tail (swapTag label i tag) := by
  dsimp only
  intro sep M D G
  let edge := addr base i
  let u := R (rail seam (i+1))
  let v := L (rail seam i)
  have U : site edge u.side=addr base (i+1) := (addr_next base i).symm
  have V : site edge v.side=addr base i := rfl
  have donor := labels (i+1) (by omega) (by omega)
  have recv := labels i pos (by omega)
  rw [source] at donor
  rw [vacant] at recv
  have S : (view ((x edge).long,(x (rightNeighbor edge)).long) u).mobile =
      encode digits (some tag) := by rw [old_access,U]; exact donor
  have T : (view ((x edge).long,(x (rightNeighbor edge)).long) v).mobile =
      encode digits none := by rw [old_access,V]; exact recv
  have K := joined_strip_hop hp digits tag x base seam tail i pos it C d M D G S T
  have clear := K.1
  have gain := K.2.1
  change (view (Pair.map LargeSite.long (largePair B (x edge,x (rightNeighbor edge)))) u).mobile = _ at clear
  change (view (Pair.map LargeSite.long (largePair B (x edge,x (rightNeighbor edge)))) v).mobile = _ at gain
  rw [new_access hp x edge u sep,U] at clear
  rw [new_access hp x edge v sep,V] at gain
  intro j jp jt
  by_cases eq : j=i
  · subst j
    simp only [swapTag]
    exact gain
  · by_cases E : j=i+1
    · subst j
      simp only [swapTag,if_neg eq]
      exact clear
    · rw [wrapped_other_positions hp x base i j tail pos it jp jt C.tail_le eq E]
      simpa [swapTag,eq,E] using labels j jp jt

theorem upstream_noningress {Tag : Type} (digits : Tag→BitVec 36)
    (x : X) (base e : Fin n) (seam tail : Nat) (C : WrappedStrip B x base seam tail)
    (sep : e≠rightNeighbor e) (excludeIngress : e≠addr base 0)
    (label : Nat→Option Tag) (old : MobileMatches digits x base seam tail label)
    (gate : ∀ j, 0<j → j≤tail → (readLane (Sheet.index (rail seam j)) (x (addr base j)).long).gate=true)
    (prep : NoUpPrep hp x base e seam tail) :
    ∃ after, stripWord tail after=stripWord tail label ∧
      MobileMatches digits (ring x e) base seam tail after := by
  by_cases inside : ∃ i, 0<i ∧ i<tail ∧ e=addr base i
  · obtain ⟨i,ip,it,rfl⟩ := inside
    let mark := addr base i
    let g := oldPair B x mark
    let raw : Pair (BitVec LW) := ((x mark).long,(x (rightNeighbor mark)).long)
    let rs := reserved (round g raw).prep
    let u := R (rail seam (i+1))
    let v := L (rail seam i)
    let h := hop u v
    have V : site mark v.side=addr base i := rfl
    have U : site mark u.side=addr base (i+1) := (addr_next base i).symm
    have land (a : At Sheet) (A : a=u ∨ a=v) :
        a∉rs := by
      rcases A with rfl|rfl
      · exact prep _ (by omega) (by omega) .right U
      · exact prep _ ip (by omega) .left V
    have source : (view raw u).mobile=encode digits (label (i+1)) := by
      rw [old_access x mark u,U]
      exact old _ (by omega) (by omega)
    have target : (view raw v).mobile=encode digits (label i) := by
      rw [old_access x mark v,V]
      exact old _ ip (by omega)
    have gu : (view raw u).gate=true := by
      rw [old_access x mark u,U]
      exact gate _ (by omega) (by omega)
    have gv : (view raw v).gate=true := by
      rw [old_access x mark v,V]
      exact gate _ ip (by omega)
    have both : ((view raw u).gate && (view raw v).gate)=true := by simp [gu,gv]
    have quiet (inactive : h∉orderedData g rs ∨ (view raw u).mobile=.empty ∨
      (((view raw u).gate && (view raw v).gate)=true ∧ (view raw v).mobile≠.empty)) :
      MobileMatches digits (ring x mark) base seam tail label := by
      intro j jp jt
      have Q := strip_pair_frame hp x base seam tail i it C inactive
      by_cases first : j=i
      · subst j
        have f := Q v (.inr rfl) (land v (.inr rfl))
        change view (Pair.map LargeSite.long (largePair B (x mark,x (rightNeighbor mark)))) v=view raw v at f
        rw [new_access hp x mark v sep,old_access x mark v,V] at f
        exact (congrArg Lane.mobile f).trans (old _ jp jt)
      · by_cases second : j=i+1
        · subst j
          have f := Q u (.inl rfl) (land u (.inl rfl))
          change view (Pair.map LargeSite.long (largePair B (x mark,x (rightNeighbor mark)))) u=view raw u at f
          rw [new_access hp x mark u sep,old_access x mark u,U] at f
          exact (congrArg Lane.mobile f).trans (old _ jp jt)
        · rw [wrapped_other_positions hp x base i j tail ip it jp jt C.tail_le first second]
          exact old _ jp jt
    by_cases selected : h∈orderedData g rs
    · cases s : label (i+1) with
      | none =>
        exact ⟨label,rfl,quiet (.inr (.inl (source.trans (by rw [s]; rfl))))⟩
      | some tag =>
        cases d : label i with
        | none =>
          exact ⟨swapTag label i tag,stripWord_swap tail i ip it label tag s d,
            ring_transport hp digits tag x base seam tail i ip it C h label old s d sep selected rfl both⟩
        | some q =>
          exact ⟨label,rfl,quiet (.inr (.inr ⟨both,by rw [target,d]; intro Z; contradiction⟩))⟩
    · exact ⟨label,rfl,quiet (.inl selected)⟩
  · refine ⟨label,rfl,?_⟩
    intro j jp jt
    by_cases eq : e=addr base j
    · have endEq : j=tail := by
        by_cases why : j=tail
        · exact why
        · exfalso
          exact inside ⟨j,jp,by omega,eq⟩
      subst j
      subst e
      let raw : Pair (BitVec LW) := ((x (addr base tail)).long,(x (rightNeighbor (addr base tail))).long)
      let slot := L (rail seam tail)
      have F := joined_tail_frame hp x base seam tail C (prep tail jp jt .left rfl)
      change view (Pair.map LargeSite.long (largePair B (x (addr base tail),x (rightNeighbor (addr base tail))))) slot =
        view raw slot at F
      rw [new_access hp x (addr base tail) slot sep,old_access x (addr base tail) slot] at F
      exact (congrArg Lane.mobile F).trans (old _ jp jt)
    · have pred : e≠addr base (j-1) := by
        intro E
        by_cases first : j=1
        · subst j
          exact excludeIngress E
        · exact inside ⟨j-1,by omega,by omega,E⟩
      rw [ring_exterior_frame hp x base e j jp eq pred]
      exact old j jp jt

#print axioms upstream_noningress

theorem ingress_quiet {Tag : Type} (digits : Tag→BitVec 36)
    (x : X) (root base : Fin n) (width seam tail : Nat)
    (C : Dest B x root width) (U : WrappedStrip B x base seam tail)
    (join : addr base 0=addr root (width-1))
    (s : Ledger Tag) (plan : List Tag) (size : plan.length=width)
    (label : Nat→Option Tag) (P : OrderedPrefix plan s (stripWord tail label))
    (old : RetainedMatches digits x root width s)
    (matched : MobileMatches digits x base seam tail label) :
    let e := addr base 0
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    let g := oldPair B x e
    let u := R (rail seam 1)
    let v := L (rail seam 0)
    e≠rightNeighbor e →
    NoRDPrep hp x root e width →
    (hop u v∉orderedData g (reserved (round g raw).prep) ∨
      (view raw u).mobile=.empty ∨
      (((view raw u).gate && (view raw v).gate)=true ∧ (view raw v).mobile≠.empty)) →
    RetainedMatches digits (ring x e) root width s ∧
      (NoUpPrep hp x base e seam tail → MobileMatches digits (ring x e) base seam tail label) := by
  dsimp only
  intro sep prep inactive
  let e := addr base 0
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let u := R (rail seam 1)
  let v := L (rail seam 0)
  have vrd : rail seam 0=.rd := if_pos U.seam_pos
  have widthP := C.pos
  have T : 0<tail := Nat.lt_of_lt_of_le U.seam_pos U.seam_le_tail
  have Q := strip_pair_frame hp x base seam tail 0 T U inactive
  have upLoc : site e u.side=addr base 1 := (addr_next base 0).symm
  have vLoc : site e v.side=addr root (width-1) := join
  have notPrepV := prep (width-1) (by omega) .left join
  change (⟨Side.left,Sheet.rd⟩ : At Sheet)∉reserved (round (oldPair B x e) raw).prep at notPrepV
  have Nv : v∉reserved (round (oldPair B x e) raw).prep := by
    change L (rail seam 0)∉reserved (round (oldPair B x e) raw).prep
    rw [vrd]
    exact notPrepV
  have F := Q v (.inr rfl) Nv
  change view (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) v=view raw v at F
  rw [new_access hp x e v sep,old_access x e v,vLoc] at F
  have frameHead : readLane (Sheet.index .rd) (ring x e (addr root (width-1))).long =
      readLane (Sheet.index .rd) (x (addr root (width-1))).long := by
    change readLane (Sheet.index (rail seam 0)) (ring x e (addr root (width-1))).long =
      readLane (Sheet.index (rail seam 0)) (x (addr root (width-1))).long at F
    rwa [vrd] at F
  refine ⟨?_,?_⟩
  · intro j jw
    by_cases same : j=width-1
    · subst j
      rw [frameHead]
      exact old _ jw
    · have fit := C.fit
      have noL : addr root j≠e := fun H => same (addr_inj root (by omega) (by omega) (H.trans join))
      by_cases right : addr root j=rightNeighbor e
      · by_cases zero : j=0
        · subst j
          rw [retained_header_frame hp digits x root e width C s plan _ size P old right.symm sep
            (prep 0 jw .right right.symm)]
          exact old 0 jw
        · have prev : e=addr root (j-1) := by
            apply rightNeighbor_inj
            rw [←addr_next root (j-1),show j-1+1=j by omega]
            exact right.symm
          have impossible := addr_inj root (by omega) (by omega) (join.symm.trans prev)
          omega
      · rw [show ring x e (addr root j)=x (addr root j) from by simp [AllSizeS1Geometry.step,noL,right]]
        exact old _ jw
  · intro prepUp j jp jt
    by_cases same : j=1
    · subst j
      have N := prepUp 1 jp jt .right upLoc
      have Z := Q u (.inl rfl) N
      change view (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) u=view raw u at Z
      rw [new_access hp x e u sep,old_access x e u,upLoc] at Z
      exact (congrArg Lane.mobile Z).trans (matched 1 jp jt)
    · rw [ingress_other_slot hp x base seam tail U sep prepUp j jp jt same]
      exact matched _ jp jt

theorem ingress_cross {Tag : Type} (digits : Tag→BitVec 36)
    (x : X) (root base : Fin n) (width seam tail : Nat)
    (C : Dest B x root width) (U : WrappedStrip B x base seam tail)
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
    NoUpPrep hp x base e seam tail →
    hop u v∈orderedData g (reserved (round g raw).prep) →
    (((view raw u).gate && (view raw v).gate)=true) →
    OrderedPrefix plan (s.receiveFirst tag) (stripWord tail (clearHead label)) ∧
      RetainedMatches digits (ring x e) root width (s.receiveFirst tag) ∧
      MobileMatches digits (ring x e) base seam tail (clearHead label) := by
  dsimp only
  intro sep prep upPrep selected gates
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
    · rw [ingress_other_slot hp x base seam tail U sep upPrep j JP JT H]
      simp only [clearHead,if_neg H]
      exact matched j JP JT

/-- Complete all-label data-only classifier. Each physical mark may
cause an independent upstream swap and a retained transfer; neither
projection pretends the other rail is idle. Intended for the PC11
portion after actual absence of new INJECT has been proved. -/
theorem data_mark {Tag : Type} (digits : Tag→BitVec 36)
    (x : X) (root base e : Fin n) (width seam tail : Nat)
    (C : Dest B x root width) (U : WrappedStrip B x base seam tail)
    (join : addr base 0=addr root (width-1)) (sep : e≠rightNeighbor e)
    (s : Ledger Tag) (plan : List Tag) (size : plan.length=width)
    (label : Nat→Option Tag)
    (P : OrderedPrefix plan s (stripWord tail label))
    (old : RetainedMatches digits x root width s)
    (matched : MobileMatches digits x base seam tail label)
    (rdGate : ∀ j<width, (readLane (Sheet.index .rd) (x (addr root j)).long).gate=true)
    (upGate : ∀ j, 0<j → j≤tail → (readLane (Sheet.index (rail seam j)) (x (addr base j)).long).gate=true)
    (rdPrep : NoRDPrep hp x root e width) (upPrep : NoUpPrep hp x base e seam tail) :
    ∃ t labels, t.release=s.release ∧ OrderedPrefix plan t (stripWord tail labels) ∧
      RetainedMatches digits (ring x e) root width t ∧
      MobileMatches digits (ring x e) base seam tail labels := by
  by_cases atHead : e=addr base 0
  · subst e
    let e := addr base 0
    let g := oldPair B x e
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    let u := R (rail seam 1)
    let v := L (rail seam 0)
    let h := hop u v
    have vrd : rail seam 0=.rd := if_pos U.seam_pos
    have lp := C.pos
    have pos : 0<tail := Nat.lt_of_lt_of_le U.seam_pos U.seam_le_tail
    have uLoc : site e u.side=addr base 1 := (addr_next base 0).symm
    have vLoc : site e v.side=addr root (width-1) := join
    have source : (view raw u).mobile=encode digits (label 1) := by
      rw [old_access x e u,uLoc]
      exact matched 1 (by omega) (by omega)
    have target : (view raw v).mobile=encode digits (s.cells 0).mobile := by
      rw [old_access x e v,vLoc]
      change (readLane (Sheet.index (rail seam 0)) (x (addr root (width-1))).long).mobile=_
      rw [vrd]
      have T := (old (width-1) (by omega)).1
      rwa [Nat.sub_self] at T
    have gu : (view raw u).gate=true := by
      rw [old_access x e u,uLoc]
      exact upGate 1 (by omega) (by omega)
    have gv : (view raw v).gate=true := by
      rw [old_access x e v,vLoc]
      change (readLane (Sheet.index (rail seam 0)) (x (addr root (width-1))).long).gate=true
      rw [vrd]
      exact rdGate (width-1) (by omega)
    have G : ((view raw u).gate && (view raw v).gate)=true := by simp [gu,gv]
    have stays (n : h∉orderedData g (reserved (round g raw).prep) ∨
      (view raw u).mobile=.empty ∨
      (((view raw u).gate && (view raw v).gate)=true ∧ (view raw v).mobile≠.empty)) :
        ∃ t labels, t.release=s.release ∧ OrderedPrefix plan t (stripWord tail labels) ∧
          RetainedMatches digits (ring x e) root width t ∧ MobileMatches digits (ring x e) base seam tail labels := by
      obtain ⟨R,U⟩ := ingress_quiet hp digits x root base width seam tail C U join s plan size label P old matched
        sep rdPrep n
      exact ⟨s,label,rfl,P,R,U upPrep⟩
    by_cases selected : h∈orderedData g (reserved (round g raw).prep)
    · cases fromTag : label 1 with
      | none => exact stays (.inr (.inl (source.trans (by rw [fromTag]; rfl))))
      | some tag =>
        cases vacant : (s.cells 0).mobile with
        | none =>
          have M := ingress_cross hp digits x root base width seam tail C U join s plan size label P old matched
            tag fromTag vacant sep rdPrep upPrep (by simpa only [h,u,v,vrd] using selected)
            (by simpa only [v,vrd] using G)
          exact ⟨s.receiveFirst tag,clearHead label,rfl,M⟩
        | some t => exact stays (.inr (.inr ⟨G,by rw [target,vacant]; intro K; contradiction⟩))
    · exact stays (.inl selected)
  · obtain ⟨lab,E,F⟩ := upstream_noningress hp digits x base e seam tail U sep atHead label matched upGate upPrep
    rcases BStarCopyRightRetainedClassify.noningress_classify hp digits x root e width C sep (join ▸ atHead) s plan _ size P old rdGate rdPrep with R|⟨i,tag,step,R⟩
    · exact ⟨s,lab,rfl,E.symm ▸ P,R,F⟩
    · have new : OrderedPrefix plan (s.transfer i tag) (stripWord tail label) := .mark P step
      exact ⟨s.transfer i tag,lab,rfl,E.symm ▸ new,R,F⟩

#print axioms ingress_quiet
#print axioms data_mark

structure DataReady (x : X) (root base e : Fin n) (width seam tail : Nat) : Prop where
  dest : Dest B x root width
  strip : WrappedStrip B x base seam tail
  rdGate : ∀ j<width, (readLane (Sheet.index .rd) (x (addr root j)).long).gate=true
  upGate : ∀ j, 0<j → j≤tail → (readLane (Sheet.index (rail seam j)) (x (addr base j)).long).gate=true
  rdPrep : NoRDPrep hp x root e width
  upPrep : NoUpPrep hp x base e seam tail

local notation "play" => BStarResetSchedule.run ring

/-- Ordered exact right ledger over the whole unreduced PC11 data
word, including waits, nonown physical marks, and simultaneous
independent lane moves. No selected-move checklist is supplied. -/
theorem data_word {Tag : Type} (digits : Tag→BitVec 36)
    (x : X) (w : List (Fin n)) (root base : Fin n) (width seam tail : Nat)
    (join : addr base 0=addr root (width-1))
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (plan : List Tag) (size : plan.length=width)
    (s : Ledger Tag) (labels : Nat→Option Tag)
    (P : OrderedPrefix plan s (stripWord tail labels))
    (old : RetainedMatches digits x root width s)
    (matched : MobileMatches digits x base seam tail labels)
    (ready : ∀ a e b,w=a++e::b → DataReady hp (play x a) root base e width seam tail) :
    ∃ t post, t.release=s.release ∧ OrderedPrefix plan t (stripWord tail post) ∧
      RetainedMatches digits (play x w) root width t ∧ MobileMatches digits (play x w) base seam tail post := by
  induction w generalizing x s labels with
  | nil => exact ⟨s,labels,rfl,P,old,matched⟩
  | cons e w ih =>
    obtain ⟨C,U,rg,ug,rp,up⟩ := ready [] e w rfl
    obtain ⟨t,q,R,ind,held,mobile⟩ := data_mark hp digits x root base e width seam tail C U join (sep e)
      s plan size labels P old matched rg ug rp up
    obtain ⟨v,m,M,A,H,Q⟩ := ih (ring x e) t q ind held mobile
      (fun a f b E => ready (e::a) f b (congrArg (List.cons e) E))
    exact ⟨v,m,M.trans R,A,H,Q⟩

#print axioms data_word
end L4.BStarCopyRightWrappedSweep
