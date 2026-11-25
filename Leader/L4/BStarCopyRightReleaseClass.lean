import Leader.L4.BStarCopyRightReadyWord

namespace L4.BStarCopyRightReleaseClass
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
structure ReleaseAt (x : X) (e base : Fin n) (seam tail : Nat)
    (slot : Nat → Pos n) (len : Nat) (m : Mode) where
  i : Nat
  k : Nat
  markAt : e=addr base i
  range : seam≤i ∧ i≤tail
  strict : k<len
  ptr : slot k=(addr base i,2)
  mode : m=.busy 10 (.out k)
  win : BStarCopyInjection.injection .left true∈
    (arbitration (round (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).prep).1
  only : NoPrepExcept hp x e base seam tail i
  advance : ∃ (c : CommandClaim) (f : Payload),
    c.source=L 2 ∧
    (c,.advance f)∈actualOffers (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)

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
    (dest : Dest B base root width) (strip : Strip B base baseAddr seam tail)
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
        have only := no_competing_from_pointed hp chart same e baseAddr seam tail i k it strip
          ownerHead (congrArg Prod.fst loc) now.2.1 now.2.2
        exact ⟨⟨i,k,markEq,⟨range,it⟩,lt,loc,rfl,winner,only,C,pay,left,active⟩⟩
  · exact .inl (fun i ip it s E H => existsRelease ⟨i,ip,it,s,E,H⟩)

#print axioms classify_release
end L4.BStarCopyRightReleaseClass
