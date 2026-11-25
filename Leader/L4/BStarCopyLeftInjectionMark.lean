import Leader.L4.BStarCopyLeftDeposit
import Leader.L4.BStarCopyRightAuthority

namespace L4.BStarCopyLeftInjectionMark
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarCopyLeftStrip BStarCopyLeftMark BStarCopyLeftDeposit
open BStarLongPackets BStarLongPrep BStarLongCommandData
open BStarClearanceDataChart BStarAcquireVisitOrder BStarAcquireAnchors
open BStarAcquireLiteralChain BStarResetChartIndex BStarResetChartTouch
open BStarCopyOwnedFrozen BStarAcquireHistoryReturn BStarSeparatorControl
open BStarResetMarkAdapter BStarResetQuiet BStarResetSchedule BStarSeparatingRail BStarGeneratedOwner
open BStarCopyRightStrip (addr addr_next addr_inj address_ordinal_run)

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B

theorem ls_same_word {base : X} {a : Fin n} {seam width : Nat}
    (C : Strip B base a seam width) (hh : ∃ j,oldH6 B base j=true) :
    ∀ j<seam, word (oldH6 B base) (addr a j)=word (oldH6 B base) a := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [show addr a 0=a from Fin.ext (Nat.mod_eq_of_lt a.isLt)]
  | succ j ih =>
    intro J
    have T := right_word (oldH6 B base) (addr a j)
    rw [←addr_next,C.ls_body (j+1) (by omega) J] at T
    simp only [Bool.toNat_false,Int.natCast_zero,Int.add_zero] at T
    obtain ⟨u,v⟩ := word_range (oldH6 B base) (addr a j) hh
    rw [Int.emod_eq_of_lt u v] at T
    exact T.trans (ih (by omega))

theorem no_competing_prep {base x : X}
    {hh : ∃ i,oldH6 B base i=true} {o : Owners (oldH6 B base)}
    {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (same : ∀ i, BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    (e a : Fin n) (seam width i cursor : Nat) (it : i<seam)
    (C : Strip B base a seam width) (root : a=(S.getD 0 fall).1)
    (atIssue : (S.getD cursor fall).1=addr a i)
    (good : Good anyTag len (project (fun j => S.getD j fall) x) (.out cursor))
    (clean : OutClean len (project (fun j => S.getD j fall) x) (.out cursor)) :
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    ∀ j<seam, j≠i → ∀ side, site e side=addr a j →
      (⟨side,.ls⟩ : At Sheet)∉reserved (round (oldPair B x e) raw).prep := by
  dsimp only
  intro j jt ne side atSlot H
  obtain ⟨offer,win,lane⟩ := List.mem_map.mp H
  obtain ⟨q,f,v,_,chosen,_,_,origin,owner⟩ := winner_owner hp x e offer win
  have eq : oldH6 B x=oldH6 B base := funext (fun a => (congrArg Prod.fst (same a)).symm)
  have root_owner := (endpoint_spec (oldH6 B base) hh o 0).2.1
  rw [←chart.root,←root] at root_owner
  have O : dataOwner (oldH6 B base) (addr a j) .ls=o.val := by
    unfold dataOwner commandOwner at *
    rw [ls_same_word hp C hh j jt]
    exact root_owner
  rw [eq,lane] at owner
  change commandOwner (oldH6 B base) (site e q.source.side) q.source.occurrence =
    dataOwner (oldH6 B base) (site e side) .ls at owner
  rw [atSlot,O] at owner
  obtain ⟨k,E,idx⟩ := actual_owner_departure hp chart same e q v (.out cursor) chosen owner good clean
  have K := Cursor.out.inj E
  subst k
  have first := congrArg Prod.fst idx
  change (S.getD cursor fall).1=site e q.source.side at first
  have siteEq : offer.claim.lane.side=q.source.side := by
    obtain ⟨Q,_,_,_,_,_,_,originQ,sideQ,_⟩ := winner_origin (oldPair B x e)
      ((x e).long,(x (rightNeighbor e)).long) offer win
    have originSide : offer.claim.lane.side=offer.claim.origin.side :=
      sideQ.trans (congrArg At.side originQ).symm
    exact originSide.trans (congrArg At.side origin)
  have sideEq : side=q.source.side := (congrArg At.side lane).symm.trans siteEq
  rw [←sideEq,atIssue,atSlot] at first
  exact ne ((addr_inj a (by have := C.seam_le; omega)
    (by have := C.seam_le; omega) first).symm)

/-- Every other tracked LS lane is framed on an ordinary right-side
K5 injection. No condition is imposed on simultaneous LD work. -/
theorem ordinary_ring {Tag : Type} (digits : Tag→BitVec 36) (tag : Tag)
    {base x : X} {hh : ∃ i,oldH6 B base i=true} {o : Owners (oldH6 B base)}
    {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (same : ∀ i, BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    (e a : Fin n) (seam width i cursor : Nat) (it : i<seam)
    (C : Strip B base a seam width) (root : a=(S.getD 0 fall).1)
    (atIssue : (S.getD cursor fall).1=addr a i)
    (good : Good anyTag len (project (fun j => S.getD j fall) x) (.out cursor))
    (clean : OutClean len (project (fun j => S.getD j fall) x) (.out cursor))
    (loc : rightNeighbor e=addr a i) (sep : e≠rightNeighbor e)
    (ordinary : 0<i ∨ seam<n)
    (winner : BStarCopyInjection.injection .right false∈
      (arbitration (round (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).prep).1)
    (labels : Nat→Option Tag) (old : UpstreamMatches digits x a seam labels)
    (write : (sample (step x e) a seam i).mobile=BStarCopyFIFO.encode digits (some tag)) :
    UpstreamMatches digits (step x e) a seam (deposit labels i tag) := by
  apply upstream_of_deposition hp digits tag x e a seam i sep labels old write
  dsimp only
  intro j J ne z Z sh
  have np := no_competing_prep hp chart same e a seam width i cursor it C root atIssue good clean j J ne z.side Z
  have eq : z=(⟨z.side,.ls⟩ : At Sheet) := by cases z; simp_all
  have np' : z∉reserved (round (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).prep := by
    rwa [←eq] at np
  refine ⟨np',?_⟩
  intro d M leaf E
  have slot := data_lane_claim _ _ _ _ _ E
  have raw := BStarLongFenceTopology.selected_data_raw _ _ _ M
  cases side : z.side with
  | right =>
    rw [side] at Z
    change rightNeighbor e=addr a j at Z
    have nb := C.seam_le
    exact ne (addr_inj a (by omega) (by omega) (Z.symm.trans loc))
  | left =>
    rw [side] at Z
    change e=addr a j at Z
    have H : addr a (j+1)=addr a i := (addr_next a j).trans (Z ▸ loc)
    have pos : 0<i := by
      rcases ordinary with h|h
      · exact h
      · have eq := addr_inj a (by omega) (by omega) H
        omega
    have body : (oldPair B x e).2.axes.h6=false := by
      change oldH6 B x (rightNeighbor e)=false
      have H := congrArg Prod.fst (same (rightNeighbor e))
      change oldH6 B base (rightNeighbor e)=oldH6 B x (rightNeighbor e) at H
      rw [←H,loc]
      exact C.ls_body i pos it
    have left : z=L .ls := eq.trans (by rw [side]; rfl)
    rw [left] at slot
    have src : d.source=L .ls := by
      cases out : d.destination with
      | none => simpa [Claim.slots,out,eq_comm] using slot
      | some dst =>
        have alt : L Sheet.ls=d.source ∨ L Sheet.ls=dst := by simpa [Claim.slots,out] using slot
        rcases alt with A|A
        · exact A.symm
        · exact ((no_left_receive _ _ raw).1 (out.trans (congrArg some A.symm))).elim
    have K := (raw_ls_send _ _ src).mp raw
    have dh : d=hop (L .ls) (R .ls) := by simpa [body] using K
    have no := BStarCopyInjection.same_mark_reserved _ _ _ winner d M
    apply no
    rw [dh]
    simp [BStarCopyInjection.injection,BStarCopyInjection.sourceLane,Claim.slots,hop,R]

open BStarCopyFIFO BStarCopyFenceSaturation BStarCopyMarkedLedger

def clearLast {T : Type} (q : Nat→Option T) (seam : Nat) (j : Nat) : Option T :=
  if j=seam-1 then none else q j

theorem pop_last {T : Type} (q : Nat→Option T) (seam : Nat) (h : 0<seam)
    (tag : T) (head : q (seam-1)=some tag) :
    headFirst seam q=tag::headFirst seam (clearLast q seam) := by
  have E : List.range seam=List.range (seam-1)++[seam-1] := by
    conv => lhs; rw [show seam=(seam-1)+1 by omega,List.range_succ]
  have Q : (List.range (seam-1)).flatMap (fun j => (clearLast q seam j).toList)=
      (List.range (seam-1)).flatMap (fun j => (q j).toList) := by
    apply congrArg List.flatten
    apply List.map_congr_left
    intro j J
    have := List.mem_range.mp J
    simp [clearLast,show j≠seam-1 by omega]
  unfold headFirst upstreamWord
  rw [E,List.flatMap_append,List.flatMap_append,Q]
  simp [clearLast,head]

theorem sole_header_cross_ring {Tag : Type}
    (digits : Tag→BitVec 36) (head fresh : Tag)
    {base x : X} (e a : Fin n) (width : Nat) (C : Strip B base a n width)
    (loc : rightNeighbor e=addr a 0) (sep : e≠rightNeighbor e)
    (labels : Nat→Option Tag) (old : UpstreamMatches digits x a n labels)
    (headAt : labels (n-1)=some head) (empty0 : labels 0=none)
    (write : (sample (step x e) a n 0).mobile=encode digits (some fresh))
    {plan : List Tag} {s : Ledger Tag} (todo : List Tag)
    (P : OrderedPrefix plan s (headFirst n labels)) (pending : s.release.pending=fresh::todo) :
    let g := oldPair B x e
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    let dst := fun (y : X) => readLane (Sheet.index .ld) (y (rightNeighbor e)).long
    hop (L .ls) (R .ld)∈orderedData g (reserved (round g raw).prep) →
    retains g (R .ld)=true →
    ((readLane (Sheet.index .ls) (x e).long).gate && (dst x).gate)=true →
    Compatible digits (s.cells 0) (dst x) → (s.cells 0).mobile=none →
    let q := deposit (clearLast labels n) 0 fresh
    UpstreamMatches digits (step x e) a n q ∧
    Compatible digits ((s.receiveFirst head).cells 0) (dst (step x e)) ∧
    OrderedPrefix plan ((s.receiveFirst head).releaseOne fresh todo) (headFirst n q) := by
  dsimp only
  intro M ret gates agree vacant
  have npos := C.seam_pos
  have wrap : addr a n=addr a 0 := by
    apply Fin.ext
    simp [addr,Nat.add_mod_right]
  have last : addr a (n-1)=e := by
    apply BStarCopyRightMark.rightNeighbor_inj
    rw [←addr_next,show n-1+1=n by omega,wrap,loc]
  have H0 := old (n-1) (by omega)
  unfold sample at H0
  rw [rail,if_pos (show n-1<n by omega),last,headAt] at H0
  have P' := pop_last labels n npos head headAt ▸ P
  have N : L Sheet.ls≠R .ld := by intro H; cases congrArg At.side H
  obtain ⟨_,outHead,outData⟩ := BStarCopyUpstreamTags.ring_cross_head hp digits head _ P'
    x e sep (hop (L .ls) (R .ld)) (R .ld) rfl rfl M N ret gates H0 agree vacant
  have Q := parallel_prefix head fresh _ todo P' vacant pending
  have emptyCut : ∀ j≤0,clearLast labels n j=none := by
    intro j J; have E : j=0 := by omega
    subst j
    simp [clearLast,empty0]
  rw [←append_at_cut _ n 0 npos fresh emptyCut] at Q
  refine ⟨?_,outData,Q⟩
  intro j J
  by_cases Z : j=0
  · subst j
    rw [deposit,if_pos (rfl : 0=0)]
    exact write
  · by_cases F : j=n-1
    · subst j
      rw [deposit,if_neg Z,clearLast,if_pos (rfl : n-1=n-1)]
      unfold sample
      rw [rail,if_pos J,last]
      exact outHead
    · have A : addr a j≠e := by
        rw [←last]
        exact fun K => F (addr_inj a J (by omega) K)
      have D : addr a j≠rightNeighbor e := by
        rw [loc]
        exact fun K => Z (addr_inj a J npos K)
      have E : step x e (addr a j)=x (addr a j) := by simp [AllSizeS1Geometry.step,A,D]
      change (sample (step x e) a n j).mobile=_
      unfold sample
      rw [E]
      simpa only [sample,deposit,clearLast,if_neg Z,if_neg F] using old j J

end L4.BStarCopyLeftInjectionMark
