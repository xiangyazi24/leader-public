import Leader.L4.BStarCopyRightWrappedActiveFold

namespace L4.BStarCopyRightWrappedReleaseClass
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarLongPackets BStarLongPrep BStarLongCommandData BStarLongEvents BStarLongCommand
open BStarLongDoor BStarLongToken
open BStarCopyRightStrip BStarCopyRightRetained BStarCopyRightRetainedClassify
open BStarCopyRightMark BStarCopyRightDataSweep BStarCopyRightReady BStarCopyRightDeposit
open BStarCopyRightAuthority BStarCopyRightK2Past BStarCopyGateAuthority BStarCopyOwnedFrozen
open BStarClearanceDataChart BStarGeneratedBandScan BStarGeneratedOwner BStarAcquireVisitOrder
open BStarAcquireLiteralChain BStarResetChartTouch BStarResetChartIndex BStarSeparatingRail
open BStarAcquireForwardTrace BStarResetMarkAdapter BStarResetSchedule BStarSeparatorControl
open BStarCopyOperand

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run ring

open BStarCopyRightWrappedGeometry BStarCopyRightWrappedSweep BStarCopyRightReleaseClass
open BStarCopyRightReleaseOrder BStarCopyRightK2 BStarCopyPaddingFrame
open BStarAcquireAnchors

private theorem member_offers {T : Type} (key : T→Nat) (a : T) (l : List T)
    (H : a∈offers key l) : a∈l := by
  induction l with
  | nil => exact H
  | cons b l ih =>
    change a∈insert key b (offers key l) at H
    exact List.mem_cons.mpr (((mem_insert key b a _).mp H).imp_right ih)

private theorem winner_candidate (ps : List BStarLongPrep.Offer) (a : BStarLongPrep.Offer)
    (win : a∈(arbitration ps).1) : a∈ps := by
  unfold arbitration at win
  rw [arbitrate_winners] at win
  exact member_offers offerPriority a ps ((select_sublist ..).subset win)

private theorem canonical_inject (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (a : BStarLongPrep.Offer) (win : a∈(arbitration (round g raw).prep).1)
    (op : a.claim.op=.inject) (sh : a.claim.lane.occurrence=.rs) :
    a=BStarCopyInjection.injection a.claim.lane.side true := by
  have cand := winner_candidate _ _ win
  obtain ⟨C,f,q,_,_,decode,clean,mem,origin,side,sites⟩ := candidate_origin g raw a cand
  rw [op,sh] at sites
  have k2 : C.source.occurrence=2 := by
    simp only [prepSites] at sites
    split at sites
    · split at sites
      · simp at sites
      · split at sites <;> simp_all
    · simp at sites
  have addr : a.claim.origin=⟨a.claim.lane.side, 2⟩ :=
    origin.trans (by
      have eq : C.source=⟨C.source.side,C.source.occurrence⟩ := by cases C.source; rfl
      rw [←side,k2] at eq
      exact eq)
  rw [op] at decode
  simp only [fieldOffers,clean,bne_self_eq_false,decode] at mem
  obtain ⟨c,_,E⟩ := List.mem_map.mp mem
  have payload : a.payload=.empty := by
    have F := congrArg BStarLongPrep.Offer.payload E
    exact F.symm
  have q1 : a.claim=⟨a.claim.op,a.claim.origin,a.claim.lane⟩ := by cases a.claim; rfl
  have q2 : a.claim.lane=⟨a.claim.lane.side,.rs⟩ := by
    have eq : a.claim.lane=⟨a.claim.lane.side,a.claim.lane.occurrence⟩ := by cases a.claim.lane; rfl
    rw [sh] at eq
    exact eq
  have q3 : a=⟨a.claim,a.payload⟩ := by cases a; rfl
  calc
    _ = ⟨a.claim,a.payload⟩ := q3
    _ = _ := by
      unfold BStarCopyInjection.injection BStarCopyInjection.sourceOccurrence BStarCopyInjection.sourceLane
      simp only [if_true]
      have C : a.claim=⟨.inject,⟨a.claim.lane.side,2⟩,⟨a.claim.lane.side,.rs⟩⟩ :=
        q1.trans (by rw [op,addr]; exact congrArg (PrepClaim.mk .inject ⟨a.claim.lane.side,2⟩) q2)
      exact (congrArg (BStarLongPrep.Offer.mk a.claim) payload).trans
        (congrArg (fun p => (⟨p,.empty⟩ : BStarLongPrep.Offer)) C)

/-- Physical evidence for a unique right release at the original
outward cursor. No packet-byte match is used in this classification. -/
theorem strip_same_owner {a : LargeParams} {n : Nat} {b : LargeRows a}
    {x : Fin n→LargeSite a} {base : Fin n} {seam tail : Nat}
    (C : WrappedStrip b x base seam tail) :
    ∀ i≤tail, dataOwner (oldH6 b x) (addr base i) (rail seam i)=
      dataOwner (oldH6 b x) (addr base 0) (rail seam 0) := by
  intro i
  induction i with
  | zero => simp
  | succ i IH =>
    intro it
    let edge := addr base i
    let dst := L (rail seam i)
    let cl := hop (R (rail seam (i+1))) dst
    have M : cl∈dataClaims (oldPair b x edge) := (wrapped_raw_incoming C i (by omega) cl rfl).mpr rfl
    have H := reserved_hop_owner b x edge [] cl dst (raw_is_selected_empty _ _ M) rfl
    change dataOwner (oldH6 b x) (rightNeighbor (addr base i)) (rail seam (i+1)) =
      dataOwner (oldH6 b x) (addr base i) (rail seam i) at H
    rw [←addr_next] at H
    exact H.trans (IH (by omega))

theorem no_competing_from_pointed {base x : X}
    {hh : ∃ i,oldH6 B base i=true} {o : Owners (oldH6 B base)}
    {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (same : ∀ i, BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    (e a : Fin n) (seam tail i cursor : Nat) (ip : 0<i) (it : i≤tail)
    (C : WrappedStrip B base a seam tail)
    (ownerHead : dataOwner (oldH6 B base) (addr a 0) (rail seam 0)=o.val)
    (atIssue : (S.getD cursor fall).1=addr a i)
    (good : Good anyTag len (project (fun j => S.getD j fall) x) (.out cursor))
    (clean : OutClean len (project (fun j => S.getD j fall) x) (.out cursor)) :
    NoPrepExcept hp x e a seam tail i := by
  intro j side jp jt ne atSlot H
  obtain ⟨offer,win,lane⟩ := List.mem_map.mp H
  obtain ⟨q,f,v,_,chosen,_,_,origin,owner⟩ := winner_owner hp x e offer win
  have eq : oldH6 B x=oldH6 B base := funext (fun a => (congrArg Prod.fst (same a)).symm)
  have O := (strip_same_owner C j jt).trans ownerHead
  rw [eq,lane] at owner
  change commandOwner (oldH6 B base) (site e q.source.side) q.source.occurrence =
    dataOwner (oldH6 B base) (site e side) (rail seam j) at owner
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
  exact ne ((upstream_addr_inj a ip jp (Nat.le_trans it C.tail_le)
    (Nat.le_trans jt C.tail_le) first).symm)

theorem rs_ord {base : X} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (a : Fin n) (seam tail : Nat) (C : WrappedStrip B base a seam tail)
    (ownerHead : dataOwner (oldH6 B base) (addr a 0) (rail seam 0)=o.val)
    (i : Nat) (lo : seam≤i) (hi : i≤tail) :
    ∃ k<len, S.getD k fall=(addr a i,2) := by
  have own := (strip_same_owner C i hi).trans ownerHead
  have rs : rail seam i=.rs := if_neg (by omega)
  rw [rs] at own
  have owner : commandOwner (oldH6 B base) (addr a i) 2=o.val := own
  have act : BStarAcquireRailCoverage.active (longGeometry B (base (addr a i))) 2=true := by
    simp [BStarAcquireRailCoverage.active]
  obtain ⟨k,kl,K⟩ := List.getElem_of_mem (chart.cover (addr a i,2) act owner)
  have M : S.getD k fall=(addr a i,2) := (List.getElem_eq_getD (h:=kl) fall).symm.trans K
  have Le : k≤len := by have := chart.length; omega
  have nEnd : k≠len := by
    intro E
    subst k
    have V := congrArg Prod.snd (chart.terminal.symm.trans M)
    change (10 : Fin 11)=2 at V
    contradiction
  exact ⟨k,by omega,M⟩

theorem k2_block {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (a : Fin n) (seam tail : Nat) (C : WrappedStrip B base a seam tail)
    (head : dataOwner (oldH6 B base) (addr a 0) (rail seam 0)=o.val) :
    ∃ first, K2Block S len fall a seam tail first := by
  have T := C.seam_le_tail
  obtain ⟨first,fl,atFirst⟩ := rs_ord hp chart a seam tail C head seam (by omega) T
  have firstPos : 0<first := by
    cases first with
    | zero =>
      have E := congrArg Prod.snd (chart.root.symm.trans atFirst)
      change (0 : Fin 11)=2 at E
      contradiction
    | succ j => omega
  refine ⟨first,firstPos,T,?_⟩
  have H : ∀ d, seam+d≤tail →
      first+d<len ∧ S.getD (first+d) fall=(addr a (seam+d),2) := by
    intro d
    induction d with
    | zero =>
      intro _
      simpa only [Nat.add_zero] using And.intro fl atFirst
    | succ d ih =>
      intro scope
      obtain ⟨bound,E⟩ := ih (by omega)
      let j := seam+d
      let u : Pos n := (addr a j,2)
      let v : Pos n := (addr a (j+1),2)
      have right := addr_next a j
      have body : (oldPair B base (addr a j)).2.axes.h6=false := by
        change oldH6 B base (rightNeighbor (addr a j))=false
        rw [←right]
        exact C.rs_nonheader _ (by dsimp [j]; omega) (by dsimp [j]; omega)
      have edge : Edge B base u v := by
        refine ⟨addr a j,link (L 2) (R 2),R 2,k2_body _ body,rfl,rfl,?_⟩
        change (addr a (j+1),2)=(rightNeighbor (addr a j),2)
        rw [right]
      have Ls := chart.length
      have jr : first+d<S.length := by omega
      have U : S.getD (first+d) fall=u := E
      have m : u∈S := by
        rw [←U,←List.getElem_eq_getD (h:=jr)]
        exact List.getElem_mem _
      obtain ⟨p,pLt,F,G⟩ := chart.edge u v m edge
      have pEq : p=first+d := (List.getD_inj (by omega) jr chart.nodup).mp (by
        rw [←List.getElem_eq_getD (h:=show p<S.length by omega),F,U])
      subst p
      have new : S.getD (first+d+1) fall=v := (List.getElem_eq_getD _).symm.trans G
      have strict : first+d+1<len := by
        by_cases eq : first+d+1=len
        · rw [eq] at new
          have K := congrArg Prod.snd (chart.terminal.symm.trans new)
          change (10 : Fin 11)=2 at K
          contradiction
        · omega
      rw [Nat.add_succ,Nat.add_succ]
      exact ⟨strict,new⟩
  intro i lo hi
  have E : seam+(i-seam)=i := by omega
  simpa only [E] using H (i-seam) (by omega)

private theorem at_rhs {a : At Sheet} (s : Side) (sh : Sheet) (H : a=⟨s,sh⟩) :
    a.side=s ∧ a.occurrence=sh := ⟨congrArg At.side H,congrArg At.occurrence H⟩

/-- Any actual mark in owner PC10 is either prep-free on the right
upstream strip, or its unique originally owned K2 submits the literal
INJECT. Retained RD has no prep in both branches. Idle, reverse, and
external work do not need caller-supplied nonrelease clauses. -/
theorem classify_release {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (w : List (Fin n)) (m : Mode)
    (G : GeneratedOwner hp base (fun t=>S.getD t fall) len origin .idle w m)
    (same : ∀ j,BStarLongFixedRouting.Layout B base j=
      BStarLongFixedRouting.Layout B (play origin w) j)
    (pc10 : pc (play origin w) (S.getD 0 fall).1=10)
    (root baseAddr e : Fin n) (width seam tail : Nat)
    (dest : Dest B base root width) (strip : WrappedStrip B base baseAddr seam tail)
    (join : addr baseAddr 0=addr root (width-1))
    (ownerHead : dataOwner (oldH6 B base) (addr baseAddr 0) (rail seam 0)=o.val) :
    NoRDPrep hp (play origin w) root e width ∧
      (NoUpPrep hp (play origin w) baseAddr e seam tail ∨
        Nonempty (ReleaseAt hp (play origin w) e baseAddr seam tail (fun t=>S.getD t fall) len m)) := by
  classical
  let y := play origin w
  let g := oldPair B y e
  let raw : Pair (BitVec LW) := ((y e).long,(y (rightNeighbor e)).long)
  let rsv := reserved (round g raw).prep
  have now := BStarGeneratedTapeCuts.at_end hp G
  have headOwn : dataOwner (oldH6 B base) (addr root (width-1)) .rd=o.val := by
    rwa [show rail seam 0=.rd from if_pos strip.seam_pos,join] at ownerHead
  have code (a : BStarLongPrep.Offer) (win : a∈(arbitration (round g raw).prep).1)
      (owned : dataOwner (oldH6 B base) (site e a.claim.lane.side) a.claim.lane.occurrence=o.val) :
      a.claim.op=.inject := by
    have E := winning_prep_pc hp chart sep G now same e a owned win
    rw [pc10] at E
    exact (Option.some.inj E).symm
  have noRD : NoRDPrep hp y root e width := by
    intro j hl s addrEq
    apply no_rd_reservation_late
    intro a win lane
    have own : dataOwner (oldH6 B base) (site e a.claim.lane.side) a.claim.lane.occurrence=o.val := by
      rw [(at_rhs _ _ lane).1,(at_rhs _ _ lane).2,addrEq]
      exact (dest_owner hp root width dest j hl).trans headOwn
    rw [code a win own]
    exact ⟨10,by decide,rfl⟩
  refine ⟨noRD,?_⟩
  by_cases existsRelease : ∃ i, 0<i ∧ i≤tail ∧ ∃ s : Side,
      site e s=addr baseAddr i ∧ (⟨s,rail seam i⟩ : At Sheet)∈rsv
  · apply Or.inr
    obtain ⟨i,ip,it,s,whereAt,used⟩ := existsRelease
    obtain ⟨a,win,lane⟩ := List.mem_map.mp used
    have laneEq := at_rhs _ _ lane
    have ownSlot := (strip_same_owner strip i it).trans ownerHead
    have own : dataOwner (oldH6 B base) (site e a.claim.lane.side) a.claim.lane.occurrence=o.val := by
      rw [laneEq.1,laneEq.2,whereAt]; exact ownSlot
    have op := code a win own
    have R : rail seam i=.rs := by
      rcases inject_or_no_reservation g raw ⟨s,rail seam i⟩
        (by by_cases H : i<seam <;> simp [rail,H])
        (fun b hb z => ⟨10,by decide,by rw [code b hb (by rw [z]; exact whereAt.symm ▸ ownSlot)]; rfl⟩)
        with no|is
      · exact (no used).elim
      · exact is.1
    have range : seam≤i := by
      by_cases H : i<seam
      · simp [rail,H] at R
      · omega
    have isRS : a.claim.lane.occurrence=.rs := laneEq.2.trans R
    have literal := canonical_inject g raw a win op isRS
    have winner : BStarCopyInjection.injection s true∈(arbitration (round g raw).prep).1 :=
      (literal.trans (congrArg (fun d => BStarCopyInjection.injection d true) laneEq.1)) ▸ win
    cases m with
    | idle =>
      have safe := safe_idle hp chart same e (addr baseAddr i) .rs
        (R ▸ ownSlot) now.2 s whereAt a win (by rwa [R] at lane)
      rcases safe with H|H|H <;> rw [op] at H <;> contradiction
    | busy m curs =>
      have oldPC := now.1.2.2.2
      have m10 : m=10 := oldPC.symm.trans pc10
      cases m10
      cases curs with
      | back k =>
        have safe := safe_returning hp chart same e (addr baseAddr i) .rs k
          (R ▸ ownSlot) now.2.1 s whereAt a win (by rwa [R] at lane)
        rcases safe with H|H|H <;> rw [op] at H <;> contradiction
      | out k =>
        obtain ⟨C,_,pay,_,active,_,_,originC,ownerC⟩ := winner_owner hp y e a win
        have H6 : oldH6 B y=oldH6 B base := funext (fun x => (congrArg Prod.fst (same x)).symm)
        rw [H6,own] at ownerC
        obtain ⟨l,E,L⟩ :=
          actual_owner_departure hp chart same e C pay (.out k) active ownerC now.2.1 now.2.2
        have Kl : l=k := (Cursor.out.inj E).symm
        subst l
        have originAt : C.source=⟨s,2⟩ := by rw [←originC,literal,laneEq.1]; rfl
        have addressAt : address e C.source=(addr baseAddr i,2) := by rw [originAt]; exact Prod.ext whereAt rfl
        have loc := L.trans addressAt
        have Cmem : C∈orderedCommands g := by
          rw [←actualOffers_claims g raw]
          exact List.mem_map.mpr ⟨_,active,rfl⟩
        have shape := raw_k2 g C Cmem (congrArg At.occurrence originAt)
        have left : C.source=BStarLongClaims.L 2 := by
          rw [shape]; cases g.2.axes.h6 <;> rfl
        have sL : s=.left := congrArg At.side (originAt.symm.trans left)
        subst s
        have markEq : e=addr baseAddr i := whereAt
        have lt : k<len := by
          have U := now.2.1.1
          by_cases E : k=len
          · subst k
            have bad := congrArg Prod.snd (chart.terminal.symm.trans loc)
            change (10 : Fin 11)=2 at bad
            contradiction
          · omega
        have only := no_competing_from_pointed hp chart same e baseAddr seam tail i k ip it strip
          ownerHead (congrArg Prod.fst loc) now.2.1 now.2.2
        exact ⟨⟨i,k,markEq,⟨range,it⟩,lt,loc,rfl,winner,only,C,pay,left,active⟩⟩
  · exact .inl (fun i ip it s E H => existsRelease ⟨i,ip,it,s,E,H⟩)


#print axioms classify_release
#print axioms k2_block
end L4.BStarCopyRightWrappedReleaseClass
