import Leader.L4.BStarCopyLeftReadyWord
import Leader.L4.BStarCopyLeftK5Past

namespace L4.BStarCopyLeftReleaseClass
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarLongPackets BStarLongPrep BStarLongCommandData BStarLongEvents BStarLongCommand
open BStarLongDoor BStarLongToken
open BStarCopyRightStrip (addr)
open BStarCopyLeftStrip BStarCopyLeftRetained BStarCopyLeftRetainedClassify
open BStarCopyLeftDataSweep BStarCopyLeftReadyWord BStarCopyLeftInjectionMark
open BStarCopyLeftK5Past BStarCopyGateAuthority BStarCopyOwnedFrozen
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
    (op : a.claim.op=.inject) (sh : a.claim.lane.occurrence=.ls) :
    a=BStarCopyInjection.injection a.claim.lane.side false := by
  have cand := winner_candidate _ _ win
  obtain ⟨C,f,q,_,_,decode,clean,mem,origin,side,sites⟩ := candidate_origin g raw a cand
  rw [op,sh] at sites
  have k2 : C.source.occurrence=5 := by
    simp only [prepSites] at sites
    split at sites
    · split at sites
      · assumption
      · split at sites <;> simp_all
    · simp at sites
  have addr : a.claim.origin=⟨a.claim.lane.side, 5⟩ :=
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
  have q2 : a.claim.lane=⟨a.claim.lane.side,.ls⟩ := by
    have eq : a.claim.lane=⟨a.claim.lane.side,a.claim.lane.occurrence⟩ := by cases a.claim.lane; rfl
    rw [sh] at eq
    exact eq
  have q3 : a=⟨a.claim,a.payload⟩ := by cases a; rfl
  calc
    _ = ⟨a.claim,a.payload⟩ := q3
    _ = _ := by
      unfold BStarCopyInjection.injection BStarCopyInjection.sourceOccurrence BStarCopyInjection.sourceLane
      have C : a.claim=⟨.inject,⟨a.claim.lane.side,5⟩,⟨a.claim.lane.side,.ls⟩⟩ :=
        q1.trans (by rw [op,addr]; exact congrArg (PrepClaim.mk .inject ⟨a.claim.lane.side,5⟩) q2)
      exact (congrArg (BStarLongPrep.Offer.mk a.claim) payload).trans
        (congrArg (fun p => (⟨p,.empty⟩ : BStarLongPrep.Offer)) C)

/-- Physical evidence for a unique left release at the original
outward cursor. No packet-byte match is used in this classification. -/
structure ReleaseAt (x : X) (e base : Fin n) (seam : Nat)
    (slot : Nat → Pos n) (len : Nat) (m : Mode) where
  i : Nat
  k : Nat
  markAt : rightNeighbor e=addr base i
  range : i<seam
  strict : k<len
  ptr : slot k=(addr base i,5)
  mode : m=.busy 10 (.out k)
  win : BStarCopyInjection.injection .right false∈
    (arbitration (round (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).prep).1
  advance : ∃ (c : CommandClaim) (f : Payload),
    c.source=R 5 ∧
    (c,.advance f)∈actualOffers (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)

private theorem at_rhs {a : At Sheet} (s : Side) (sh : Sheet) (H : a=⟨s,sh⟩) :
    a.side=s ∧ a.occurrence=sh := ⟨congrArg At.side H,congrArg At.occurrence H⟩

private theorem safe_not_inject (op : Prep)
    (H : op=.stop ∨ op=.rstop ∨ op=.enable) (E : op=.inject) : False := by
  subst op
  rcases H with H|H|H <;> cases H

/-- Any actual mark in owner PC10 is either prep-free on the left
upstream strip, or its unique originally owned K5 submits the literal
INJECT. Retained LD has no prep in both branches. Idle, reverse, and
external work do not need caller-supplied nonrelease clauses. -/
theorem classify_release {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (w : List (Fin n)) (m : Mode)
    (G : GeneratedOwner hp base (fun t=>S.getD t fall) len origin .idle w m)
    (same : ∀ j,BStarLongFixedRouting.Layout B base j=
      BStarLongFixedRouting.Layout B (play origin w) j)
    (pc10 : pc (play origin w) (S.getD 0 fall).1=10)
    (baseAddr e : Fin n) (seam width : Nat) (strip : Strip B base baseAddr seam width)
    (root : baseAddr=(S.getD 0 fall).1) :
    NoLDPrep hp (play origin w) (addr baseAddr seam) e width ∧
      (NoLSPrep hp (play origin w) baseAddr e seam ∨
        Nonempty (ReleaseAt hp (play origin w) e baseAddr seam (fun t=>S.getD t fall) len m)) := by
  classical
  let y := play origin w
  let g := oldPair B y e
  let raw : Pair (BitVec LW) := ((y e).long,(y (rightNeighbor e)).long)
  let rsv := reserved (round g raw).prep
  have now := BStarGeneratedTapeCuts.at_end hp G
  have all := all_owner hp chart baseAddr seam width strip root
  have ld (j : Nat) (J : j<width) :
      dataOwner (oldH6 B base) (addr (addr baseAddr seam) j) .ld=o.val := by
    have E : addr (addr baseAddr seam) 0=addr baseAddr seam :=
      Fin.ext (Nat.mod_eq_of_lt (addr baseAddr seam).isLt)
    have A : addr (addr baseAddr seam) j=BStarFenceReceiverChart.digitFrom (addr baseAddr seam) j := by
      simpa only [Nat.zero_add,E] using (addr_from (addr baseAddr seam) 0 j)
    rw [A,←addr_from baseAddr seam j]
    have F := all (seam+j) (by omega)
    rwa [rail,if_neg (by omega : ¬seam+j<seam)] at F
  have ls (j : Nat) (J : j<seam) :
      dataOwner (oldH6 B base) (addr baseAddr j) .ls=o.val := by
    have F := all j (by omega)
    rwa [rail,if_pos J] at F
  have code (a : BStarLongPrep.Offer) (win : a∈(arbitration (round g raw).prep).1)
      (owned : dataOwner (oldH6 B base) (site e a.claim.lane.side) a.claim.lane.occurrence=o.val) :
      a.claim.op=.inject := by
    have E := winning_prep_pc hp chart sep G now same e a owned win
    rw [pc10] at E
    exact (Option.some.inj E).symm
  have noLD : NoLDPrep hp y (addr baseAddr seam) e width := by
    intro j hl s addrEq H
    obtain ⟨a,win,lane⟩ := List.mem_map.mp H
    have own : dataOwner (oldH6 B base) (site e a.claim.lane.side) a.claim.lane.occurrence=o.val := by
      rw [lane,addrEq]
      exact ld j hl
    have op := code a win own
    obtain ⟨_,_,_,_,_,_,_,_,_,M⟩ := winner_origin g raw a win
    rw [op,lane] at M
    simp only [prepSites] at M
    split at M
    · split at M
      · simp_all
      · split at M <;> simp_all
    · simp at M
  refine ⟨noLD,?_⟩
  by_cases existsRelease : ∃ i<seam, ∃ s : Side,
      site e s=addr baseAddr i ∧ (⟨s,.ls⟩ : At Sheet)∈rsv
  · apply Or.inr
    obtain ⟨i,it,s,whereAt,used⟩ := existsRelease
    obtain ⟨a,win,lane⟩ := List.mem_map.mp used
    have laneEq := at_rhs _ _ lane
    have ownSlot := ls i it
    have own : dataOwner (oldH6 B base) (site e a.claim.lane.side) a.claim.lane.occurrence=o.val := by
      rw [laneEq.1,laneEq.2,whereAt]; exact ownSlot
    have op := code a win own
    have literal := canonical_inject g raw a win op laneEq.2
    have winner : BStarCopyInjection.injection s false∈(arbitration (round g raw).prep).1 :=
      (literal.trans (congrArg (fun d => BStarCopyInjection.injection d false) laneEq.1)) ▸ win
    cases m with
    | idle =>
      have safe := safe_idle hp chart same e (addr baseAddr i) .ls
        ownSlot now.2 s whereAt a win lane
      exact (safe_not_inject _ safe op).elim
    | busy m curs =>
      have oldPC := now.1.2.2.2
      have m10 : m=10 := oldPC.symm.trans pc10
      cases m10
      cases curs with
      | back k =>
        have safe := safe_returning hp chart same e (addr baseAddr i) .ls k
          ownSlot now.2.1 s whereAt a win lane
        exact (safe_not_inject _ safe op).elim
      | out k =>
        obtain ⟨C,_,pay,_,active,_,_,originC,ownerC⟩ := winner_owner hp y e a win
        have H6 : oldH6 B y=oldH6 B base := funext (fun x => (congrArg Prod.fst (same x)).symm)
        rw [H6,own] at ownerC
        obtain ⟨l,E,L⟩ :=
          actual_owner_departure hp chart same e C pay (.out k) active ownerC now.2.1 now.2.2
        have Kl : l=k := (Cursor.out.inj E).symm
        subst l
        have originAt : C.source=⟨s,5⟩ := by rw [←originC,literal,laneEq.1]; rfl
        have addressAt : address e C.source=(addr baseAddr i,5) := by rw [originAt]; exact Prod.ext whereAt rfl
        have loc := L.trans addressAt
        have Cmem : C∈orderedCommands g := by
          rw [←actualOffers_claims g raw]
          exact List.mem_map.mpr ⟨_,active,rfl⟩
        have shape := raw_k5 g C Cmem (congrArg At.occurrence originAt)
        have right : C.source=BStarLongClaims.R 5 := by
          rw [shape]; cases g.2.axes.h6 <;> rfl
        have sL : s=.right := congrArg At.side (originAt.symm.trans right)
        subst s
        have markEq : rightNeighbor e=addr baseAddr i := whereAt
        have lt : k<len := by
          have U := now.2.1.1
          by_cases E : k=len
          · subst k
            have bad := congrArg Prod.snd (chart.terminal.symm.trans loc)
            change (10 : Fin 11)=5 at bad
            contradiction
          · omega
        exact ⟨⟨i,k,markEq,it,lt,loc,rfl,winner,C,pay,right,active⟩⟩
  · exact .inl (fun i it s E H => existsRelease ⟨i,it,s,E,H⟩)

end L4.BStarCopyLeftReleaseClass
