import Leader.L4.BStarCopyRightFenceWord

namespace L4.BStarCopyRightFenceHold
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongPackets BStarLongWork
open BStarLongPrep BStarLongCommandData BStarCopyRightStrip BStarCopyRightMark
open BStarH6WordChart BStarH6Ordinal BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarResetChartTouch BStarGeneratedOwner BStarOwnerLaunchOrigin BStarNativeReceiptTape
open BStarCopyRightReadyWord BStarGeneratedBandScan BStarLongDoor BStarLongFixedRouting
open BStarCopyMarkedLedger
open BStarClearanceDataChart
open BStarCopyRightRetained BStarCopyRightRetainedClassify BStarCopyRightDataSweep
open BStarCopyFenceSaturation BStarCopyRightFence BStarCopyFIFO

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run ring

def Region (root a : Fin n) (width seam tail : Nat) (i : Fin n) (sh : Sheet) : Prop :=
  (∃ j<width,addr root j=i ∧ sh=.rd) ∨
  (∃ j,0<j ∧ j≤tail ∧ addr a j=i ∧ sh=rail seam j)

/-- Internal incoming incidence includes the physical RD/RS seam, but
rejects intake over the last RS site. -/
theorem ready_frozen (x : X) (root a e : Fin n) (width seam tail : Nat)
    (join : addr a 0=addr root (width-1))
    (Q : DataReady hp x root a e width seam tail) :
    FrozenRegion hp (Region root a width seam tail) x e := by
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let rv := reserved (round g raw).prep
  refine ⟨?_,?_⟩
  · rintro ⟨s,sh⟩ (⟨j,jt,loc,rfl⟩|⟨j,jp,jt,loc,rfl⟩)
    · exact Q.rdPrep j jt s loc.symm
    · exact Q.upPrep j jp jt s loc.symm
  · intro d M v reg dest
    have D : d∈dataClaims g := BStarLongFenceTopology.selected_data_raw g rv d M
    obtain ⟨s,sh⟩ := v
    cases s with
    | right =>
      have K : sh=.rd ∨ sh=.rs := by
        rcases reg with ⟨j,jt,eq,h⟩|⟨j,jp,jt,eq,h⟩
        · exact .inl h
        · change sh=rail seam j at h
          rw [h]
          by_cases A : j<seam
          · exact .inl (if_pos A)
          · exact .inr (if_neg A)
      rcases K with rfl|rfl
      · exact False.elim ((no_right_receive g d D).1 dest)
      · exact False.elim ((no_right_receive g d D).2 dest)
    | left =>
      rcases reg with ⟨j,jt,loc,rfl⟩|⟨j,jp,jt,loc,rfl⟩
      · change addr root j=e at loc
        by_cases H : j+1<width
        · have body : g.2.axes.h6=false := by
            change oldH6 B x (rightNeighbor e)=false
            rw [←loc,←addr_next]
            exact Q.dest.body _ (by omega) H
          have V := (raw_rd_receive g d dest).mp D
          rcases V with ⟨_,rfl⟩|⟨bad,_,_⟩
          · exact .inl ⟨j+1,H,(addr_next root j).trans (congrArg rightNeighbor loc),rfl⟩
          · exact False.elim (Bool.noConfusion (body.symm.trans bad))
        · have E : e=addr a 0 := by rw [join,show width-1=j by omega,loc]
          change d∈dataClaims (oldPair B x e) at D
          rw [E] at D ⊢
          have d0 : d.destination=some (L (rail seam 0)) := by
            rw [show rail seam 0=.rd from if_pos Q.strip.seam_pos]
            exact dest
          have D0 := (raw_incoming Q.strip 0 (by have := Q.strip.seam_pos; have := Q.strip.seam_le_tail; omega) d d0).mp D
          subst d
          exact .inr ⟨1,by decide,by have := Q.strip.seam_pos; have := Q.strip.seam_le_tail; omega,addr_next a 0,rfl⟩
      · change addr a j=e at loc
        subst e
        by_cases below : j<tail
        · have V := (raw_incoming Q.strip j below d dest).mp D
          subst d
          exact .inr ⟨j+1,by omega,by omega,addr_next a j,rfl⟩
        · have E : j=tail := by omega
          subst j
          have rrs : rail seam tail=Sheet.rs := if_neg (Nat.not_lt_of_ge Q.strip.seam_le_tail)
          have dest' : d.destination=some (L .rs) := by
            change d.destination=some (L (rail seam tail)) at dest
            rwa [rrs] at dest
          have bad := ((raw_rs_receive g d dest').mp D).2.2.2.1
          have last : ends g.1=true := Q.strip.tail_last
          exact False.elim (Bool.noConfusion (last.symm.trans bad))

theorem drained_old {Tag : Type} (digits : Tag → BitVec 36) (x : X)
    (root a : Fin n) (width seam tail : Nat) (labels : Nat→Option Tag)
    (rd : ∀ j<width,(rdRead x root width j).mobile=.empty)
    (up : MobileMatches digits x a seam tail labels) (nil : stripWord tail labels=[]) :
    ∀ i sh,Region root a width seam tail i sh →
      (readLane (Sheet.index sh) (x i).long).mobile=.empty := by
  rintro i sh (⟨j,J,rfl,rfl⟩|⟨j,jp,jt,rfl,rfl⟩)
  · have H := rd (width-1-j) (by omega)
    unfold rdRead at H
    rwa [show width-1-(width-1-j)=j by omega] at H
  · rw [stripWord,List.flatMap_eq_nil_iff] at nil
    have H := nil j (List.mem_range'_1.mpr ⟨jp,by omega⟩)
    have V := up j jp jt
    cases K : labels j with
    | none => exact V.trans (by rw [K]; rfl)
    | some z => simp [K] at H

private theorem laneRead_congr (L R : Nat→Lane) (j count : Nat)
    (H : ∀ k, j≤k → k<j+count → L k=R k) : laneRead L j count=laneRead R j count := by
  induction count generalizing j with
  | zero => rfl
  | succ count ih =>
    simp only [laneRead,H j (by omega) (by omega)]
    rw [ih (j+1) (fun k lo hi => H k (by omega) (by omega))]

theorem hold_through_ack {Tag : Type} (digits : Tag→BitVec 36)
    {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) {width : Nat} (hw : 0<width)
    (inside : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<width))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → width≤oldOrdinal B base hh j+1)
    (root a : Fin n) (seam tail : Nat) (rootAt : root=(S.getD len fall).1)
    (join : addr a 0=addr root (width-1))
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (w : List (Fin n)) (ack : Fin n)
    (w9 bridge : List (Fin n)) (ack9 : Fin n)
    (G9 : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle w9 (.busy 9 (.back 0)))
    (event : Event hp (fun j=>S.getD j fall) len (play origin w9) ack9 (.busy 9 (.back 0)) .idle)
    (accepted : (ctrlOp.read (ring (play origin w9) ack9 (S.getD 0 fall).1).long).toNat=10)
    (hist : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle ((w9++ack9::bridge)++(w++[ack])) .idle)
    (valid : ∀ u v, ((w9++ack9::bridge)++(w++[ack]))=u++v →
      (∀ j, Layout B base j=Layout B (play origin u) j) ∧ Band (play origin u) (S.getD 0 fall).1)
    (late : 11≤pc (play origin (w9++ack9::bridge)) (S.getD 0 fall).1)
    (dest : Dest B base root width) (strip : Strip B base a seam tail)
    (ownHead : dataOwner (oldH6 B base) (addr a 0) (rail seam 0)=o.val)
    (x : X) (xEq : x=play origin (w9++ack9::bridge))
    (T : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle w (.busy 11 (.back 0)))
    (H : Hit hp base (fun j=>S.getD j fall) len (play x w) ack 11)
    (plan : List Tag) (size : plan.length=width) (s : Ledger Tag) (label : Nat→Option Tag)
    (P : OrderedPrefix plan s (stripWord tail label))
    (old : RetainedMatches digits x root width s)
    (mobile : MobileMatches digits x a seam tail label)
    (ack12 : (ctrlOp.read (ring (play x w) ack (S.getD 0 fall).1).long).toNat=12) :
    ∃ (pre gap back : List (Fin n)) (mark turn : Fin n),
      w=pre++mark::(gap++turn::back) ∧
      let y := play x ((pre++[mark])++gap)
      let last := play x (w++[ack])
      (ctrlOp.read (last (S.getD 0 fall).1).long).toNat=12 ∧
      (∀ i sh,Region root a width seam tail i sh →
        (readLane (Sheet.index sh) (last i).long).mobile=.empty ∧
        readLane (Sheet.index sh) (last i).long=readLane (Sheet.index sh) (y i).long) ∧
      laneRead (rdRead last root width) 0 width=plan.reverse.map (Digit9.data ∘ digits) := by
  have ready := right_ready_word hp chart sep w9 bridge (w++[ack]) ack9 .idle
    G9 event accepted hist valid late root a width seam tail dest strip join ownHead
  rw [←xEq] at ready
  have prefixReady (u : List (Fin n)) (e : Fin n) (v : List (Fin n))
      (E : w=u++e::v) : DataReady hp (play x u) root a e width seam tail := by
    exact ready u e (v++[ack]) (by rw [E]; simp only [List.append_assoc,List.cons_append])
  obtain ⟨pre,gap,back,mark,turn,t,post,W,rd,read,_,up,nil,_⟩ :=
    accepted_right hp digits chart hw inside notShort root a seam tail rootAt join sep w ack
      T H plan size s label P old mobile prefixReady
  let cut := (pre++[mark])++gap
  let after := turn::(back++[ack])
  have full : w++[ack]=cut++after := by rw [W]; simp [cut,after,List.append_assoc]
  have frame := drained_word_frame hp (Region root a width seam tail) (play x cut) after sep
    (drained_old digits _ root a width seam tail post rd up nil)
    (fun u e v E => by
      apply ready_frozen hp _ root a e width seam tail join
      rw [←BStarResetSchedule.run_append]
      exact ready (cut++u) e v
        (full.trans ((congrArg (cut ++ ·) E).trans (List.append_assoc cut u (e::v)).symm)))
  have last := BStarResetSchedule.run_append ring x cut after
  have stepAck : play x (w++[ack])=ring (play x w) ack := by rw [BStarResetSchedule.run_append]; rfl
  refine ⟨pre,gap,back,mark,turn,W,?_,?_,?_⟩
  · rw [stepAck]; exact ack12
  · intro i sh I
    have F := frame i sh I
    rw [←last,←full] at F
    exact ⟨(congrArg Lane.mobile F).trans
      (drained_old digits _ root a width seam tail post rd up nil i sh I), F⟩
  · have Hread : ∀ j<width,rdRead (play x (w++[ack])) root width j=rdRead (play x cut) root width j := by
      intro j J
      have F := frame (addr root (width-1-j)) .rd
        (.inl ⟨width-1-j,by omega,rfl,rfl⟩)
      rw [←last,←full] at F
      exact F
    exact (laneRead_congr _ _ 0 width (fun j _ J => Hread j (by omega))).trans read

#print axioms hold_through_ack
#print axioms ready_frozen
#print axioms drained_old
end L4.BStarCopyRightFenceHold
