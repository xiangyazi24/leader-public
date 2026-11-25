import Leader.L4.BStarFenceNominatedClear
import Leader.L4.BStarCommitOperands

namespace L4.BStarFenceCoverage
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongPackets
open BStarLongCommand BStarLongCommandData BStarLongLiteral BStarLongPrep BStarLongTransport BStarLongToken
open BStarH6WordChart BStarH6Ordinal BStarAcquireAnchors BStarClearanceDataChart BStarLongFiberOwner
open BStarAcquireVisitOrder BStarResetChartTouch BStarFenceLineGeometry BStarFenceNominatedClear BStarFencePorts
open BStarAcquireLiteralChain BStarLongFixedRouting BStarResetMarkAdapter
open BStarCopyRightStrip (addr addr_next)
open BStarCommitOperands (first_word right_back)

variable {n : Nat}

private theorem addr_zero (a : Fin n) : addr a 0=a :=
  Fin.ext (Nat.mod_eq_of_lt a.isLt)

private theorem addr_add (a : Fin n) (i j : Nat) :
    addr (addr a i) j=addr a (i+j) := by
  apply Fin.ext
  change ((a.val+i)%n+j)%n=(a.val+(i+j))%n
  rw [Nat.mod_add_mod,Nat.add_assoc]

private theorem back_addr (i : Fin n) (d u : Nat) : addr (back i (d+u)) u=back i d := by
  induction u with
  | zero => exact addr_zero _
  | succ u ih =>
    rw [show d+(u+1)=d+u+1 by omega,
      show u+1=1+u by omega,←addr_add,addr_next,addr_zero,right_back]
    exact ih

private theorem word_of_owner (h : Fin n→Bool) (hh : ∃ i,h i=true)
    (a b : Fin n) (sh : Sheet) (H : dataOwner h a sh=dataOwner h b sh) :
    word h a=word h b := by
  have E := congrArg (fun k=>addressWord (total h) k (dataDispl sh)) H
  change addressWord (total h) (owner (total h) (word h a) (dataDispl sh)) (dataDispl sh)
    = addressWord (total h) (owner (total h) (word h b) (dataDispl sh)) (dataDispl sh) at E
  rw [address_inverse,address_inverse,Int.emod_eq_of_lt (word_range h a hh).1 (word_range h a hh).2,
    Int.emod_eq_of_lt (word_range h b hh).1 (word_range h b hh).2] at E
  exact E

private theorem word_coordinate (h : Fin n→Bool) (hh : ∃ i,h i=true)
    (a i : Fin n) (A : h a=true) (W : word h i=word h a) :
    i=addr a (ordinal h hh i) := by
  let k := ordinal h hh i
  have H := (ordinal_spec h hh i).2
  have B : back i k=a := congrArg Subtype.val (header_word_injective h
    (a₁:=⟨back i k,H.1⟩) (a₂:=⟨a,A⟩) ((first_word hh i k H).trans W))
  have R := back_addr i 0 k
  simpa only [Nat.zero_add,B,back_zero] using R.symm

private theorem before_next_header (h : Fin n→Bool) (hh : ∃ i,h i=true)
    (a i : Fin n) (d : Nat) (dp : 0<d)
    (A : h a=true) (W : word h i=word h a) (Y : h (addr a d)=true) :
    ordinal h hh i<d := by
  apply Nat.lt_of_not_ge
  intro N
  let k := ordinal h hh i
  have B := word_coordinate h hh a i A W
  have H := (ordinal_spec h hh i).2
  have C : back i (k-d)=addr a d := by
    have E := back_addr i (k-d) d
    rw [show k-d+d=k by omega] at E
    have base : back i k=a := by
      exact congrArg Subtype.val (header_word_injective h
        (a₁:=⟨back i k,H.1⟩) (a₂:=⟨a,A⟩) ((first_word hh i k H).trans W))
    rw [base] at E
    exact E.symm
  have D := H.2 (k-d) (by omega)
  rw [C,Y] at D
  contradiction

private theorem right_coord_surj (d w j : Nat) (J : j<d+w) :
    ∃ k : Fin (d+w), rightCoord k=j := by
  refine ⟨⟨d+w-1-j,by omega⟩,?_⟩
  change d+w-1-(d+w-1-j)=j
  omega

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

theorem all_sheets {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    {l d w : Nat} (dp : 0<d)
    (LF : BStarCopyLeftStrip.Strip B base (S.getD 0 fall).1 l w)
    (RF : RightFrame B base (S.getD len fall).1 d w)
    (seam : addr (S.getD 0 fall).1 l=(S.getD len fall).1)
    (i : Fin n) (sh : Sheet)
    (own : dataOwner (oldH6 B base) i sh=o.val)
    (inside : sh=.ld ∨ sh=.rs → oldOrdinal B base hh i<w) :
    OnLines (S.getD 0 fall).1 (S.getD len fall).1 l d w i sh := by
  let h := oldH6 B base
  let L := (S.getD 0 fall).1
  let R := (S.getD len fall).1
  let k := ordinal h hh i
  have rootO : commandOwner h L 0=o.val := by
    dsimp [L]; rw [C.root]; exact (endpoint_spec h hh o 0).2.1
  have termO : commandOwner h R 10=o.val := by
    dsimp [R]; rw [C.terminal]; exact (endpoint_spec h hh o 10).2.1
  have leftSeed (j : Nat) (J : j<l+w) :
      dataOwner h (addr L j) (BStarCopyLeftStrip.rail l j)=o.val :=
    (left_owner LF j J).trans rootO
  have rightSeed (j : Nat) (J : j<d+w) :
      dataOwner h (addr R j) (rightRail d j)=o.val :=
    (right_owner RF dp j J).trans termO
  cases sh with
  | ls =>
    have H := leftSeed 0 (by have := LF.seam_pos; omega)
    rw [addr_zero,show BStarCopyLeftStrip.rail l 0=.ls from if_pos LF.seam_pos] at H
    have W := word_of_owner h hh i L .ls (own.trans H.symm)
    have K : k<l := before_next_header h hh L i l LF.seam_pos LF.source_header W LF.dest_header
    exact .inl ⟨⟨k,by omega⟩,word_coordinate h hh L i LF.source_header W,(if_pos K).symm⟩
  | ld =>
    have H := leftSeed l (by have := LF.width_pos; omega)
    rw [seam,show BStarCopyLeftStrip.rail l l=.ld from if_neg (Nat.lt_irrefl _)] at H
    have W := word_of_owner h hh i R .ld (own.trans H.symm)
    have K : k<w := inside (.inl rfl)
    refine .inl ⟨⟨l+k,by omega⟩,?_,?_⟩
    · rw [←addr_add,seam]
      exact word_coordinate h hh R i RF.terminal_header W
    · exact (if_neg (by omega : ¬l+k<l)).symm
  | rd =>
    have H := rightSeed 0 (by omega)
    rw [addr_zero,show rightRail d 0=.rd from if_pos dp] at H
    have W := word_of_owner h hh i R .rd (own.trans H.symm)
    have K : k<d := before_next_header h hh R i d dp RF.terminal_header W RF.first_header
    obtain ⟨j,J⟩ := right_coord_surj d w k (by omega)
    refine .inr ⟨j,?_,?_⟩
    · rw [J]; exact word_coordinate h hh R i RF.terminal_header W
    · rw [J,rightRail,if_pos K]
  | rs =>
    have H := rightSeed d (by have := RF.width_pos; omega)
    rw [show rightRail d d=.rs from if_neg (Nat.lt_irrefl _)] at H
    have W := word_of_owner h hh i (addr R d) .rs (own.trans H.symm)
    have K : k<w := inside (.inr rfl)
    obtain ⟨j,J⟩ := right_coord_surj d w (d+k) (by omega)
    refine .inr ⟨j,?_,?_⟩
    · rw [J,←addr_add]; exact word_coordinate h hh (addr R d) i RF.first_header W
    · rw [J,rightRail,if_neg (by omega : ¬d+k<d)]

theorem chart_cover {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (layout : ∀ i,Layout B base i=Layout B x i)
    {l d w : Nat} (dp : 0<d)
    (LF : BStarCopyLeftStrip.Strip B base (S.getD 0 fall).1 l w)
    (RF : RightFrame B base (S.getD len fall).1 d w)
    (seam : addr (S.getD 0 fall).1 l=(S.getD len fall).1)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<w))
    (e : Fin n) (cmd : CommandClaim)
    (owns : address e cmd.source∈S)
    (sh : Sheet) (test : fenceSheet (geometry (oldPair B x e) cmd.source.side) cmd.source.occurrence=some sh) :
    OnLines (S.getD 0 fall).1 (S.getD len fall).1 l d w (site e cmd.source.side) sh := by
  let i := site e cmd.source.side
  let g := geometry (oldPair B x e) cmd.source.side
  have H : g=longGeometry B (x i) := by cases Z : cmd.source.side <;> simp [g,i,Z,geometry,oldPair,site]
  have owned : commandOwner (oldH6 B base) i cmd.source.occurrence=o.val :=
    (C.entries _ owns).2
  have equal := relevant_sheets g cmd.source.occurrence sh test
  have disp : dataDispl sh=cmdDispl cmd.source.occurrence := by
    rcases equal with ⟨a,rfl⟩|⟨a,_,rfl⟩|⟨a,_,rfl⟩|⟨a,rfl⟩ <;>
      simp [cmdDispl,dataDispl,a]
  have I : sh=.ld ∨ sh=.rs → g.inside=true := by
    intro K
    rcases equal with ⟨_,rfl⟩|⟨_,I,rfl⟩|⟨_,I,rfl⟩|⟨_,rfl⟩ <;> simp_all
  apply all_sheets hp C dp LF RF seam i sh
  · change owner _ _ (dataDispl sh)=_
    rw [disp]
    exact owned
  · intro J
    have U := I J
    have V := congrArg (fun k : Bool×Bool×Bool=>k.2.1) (layout i)
    change (longGeometry B (base i)).inside=(longGeometry B (x i)).inside at V
    rw [H,←V,flags i] at U
    exact of_decide_eq_true U

/-- The FENCE checks on a real chart occurrence are all covered by the
physical two timed lines. LD/RS must be INSIDE to be queried at all;
LS/RD include their padding. The result permits a literal fault. -/
theorem chart_nominated {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (layout : ∀ i,Layout B base i=Layout B x i)
    {l d w : Nat} (dp : 0<d)
    (LF : BStarCopyLeftStrip.Strip B base (S.getD 0 fall).1 l w)
    (RF : RightFrame B base (S.getD len fall).1 d w)
    (seam : addr (S.getD 0 fall).1 l=(S.getD len fall).1)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<w))
    (E : BStarFenceSweepClock.Empty (BStarFenceEmptySuffix.ownedLines
      (S.getD 0 fall).1 (S.getD len fall).1 l d w x))
    (e : Fin n) (cmd : CommandClaim) (pay : Payload)
    (owns : address e cmd.source∈S)
    (raw : classifyOld (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long) cmd=.advance pay) :
    let g := oldPair B x e
    let b : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    checkFence g (view b) cmd.source pay≠.hold ∧
      (gatedAt g b cmd=.advance pay ∨ gatedAt g b cmd=.advance failedPayload) := by
  apply nominatedFenceClear hp x _ _ l d w E e cmd pay raw
  exact chart_cover hp C layout dp LF RF seam flags e cmd owns

theorem chart_no_hold {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (layout : ∀ i,Layout B base i=Layout B x i)
    {l d w : Nat} (dp : 0<d)
    (LF : BStarCopyLeftStrip.Strip B base (S.getD 0 fall).1 l w)
    (RF : RightFrame B base (S.getD len fall).1 d w)
    (seam : addr (S.getD 0 fall).1 l=(S.getD len fall).1)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<w))
    (E : BStarFenceSweepClock.Empty (BStarFenceEmptySuffix.ownedLines
      (S.getD 0 fall).1 (S.getD len fall).1 l d w x))
    (e : Fin n) (cmd : CommandClaim) (pay : Payload)
    (owns : address e cmd.source∈S) :
    checkFence (oldPair B x e) (view ((x e).long,(x (rightNeighbor e)).long)) cmd.source pay≠.hold := by
  apply BStarFenceNominatedClear.test_not_hold
  intro sh T
  have cov := chart_cover hp C layout dp LF RF seam flags e cmd owns sh T
  have M := BStarFenceNominatedClear.mobile_empty x _ _ l d w E _ sh cov
  change (readLane (Sheet.index sh)
    (lane (cmd.source.side == .right) ((x e).long,(x (rightNeighbor e)).long))).mobile=.empty
  cases Z : cmd.source.side
  · change (readLane (Sheet.index sh) (x e).long).mobile=.empty
    simpa only [Z,site] using M
  · change (readLane (Sheet.index sh) (x (rightNeighbor e)).long).mobile=.empty
    simpa only [Z,site] using M

end L4.BStarFenceCoverage
