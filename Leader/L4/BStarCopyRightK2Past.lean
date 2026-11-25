import Leader.L4.BStarCopyRightCapture
import Leader.L4.BStarCommitNoPrior

namespace L4.BStarCopyRightK2Past
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarLongToken BStarLongEvents BStarLongTransport BStarLongCommandData BStarLongPrep
open BStarAcquireVisitOrder BStarAcquireHistoryReturn BStarGeneratedOwner
open BStarSeparatingRail BStarResetMarkAdapter BStarResetQuiet BStarSeparatorControl
open BStarCopyOwnedFrozen BStarLongPackets BStarClearanceDataChart BStarAcquireAnchors BStarAcquireForwardTrace BStarAcquireLiteralChain BStarOwnerLaunchOrigin BStarResetRailRing BStarLongRouting BStarResetSchedule BStarAcquireHistorySample

private def geo (h i l : Bool) : LongGeometry :=
  ⟨⟨false,false,false,false,false,h⟩,i,l,0,false⟩

/-- K2 never executes a terminal or door. It takes the right link
on a body and the local K2→K3 turn on the next seam. -/
theorem raw_k2 (g : Pair LongGeometry) (C : CommandClaim)
    (M : C∈orderedCommands g) (K : C.source.occurrence=2) :
    C=if g.2.axes.h6 then link (L 2) (L 3) else link (L 2) (R 2) := by
  let test (h : Bool) (q : CommandClaim) : Bool :=
    q.source.occurrence != 2 ||
      q==(if h then link (L 2) (L 3) else link (L 2) (R 2))
  have V (I J H A : Bool) :
      (commandClaims (geo false I J,geo H A false)).all (test H)=true := by
    cases I <;> cases J <;> cases H <;> cases A <;> decide +kernel
  have raw := BStarLongFenceTopology.selected_command_raw _ _ M
  have X := List.all_eq_true.mp (V g.1.inside g.1.last g.2.axes.h6 g.2.inside) C raw
  simpa [test,K] using X

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B

/-- An actual selected K2 advance replaces old K2 forward with Trail. -/
theorem k2_departure_trail (x : X) (e : Fin n) (sep : e≠rightNeighbor e)
    (C : CommandClaim) (f : Payload)
    (M : (C,.advance f)∈actualOffers (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long))
    (K : C.source.occurrence=2) :
    atCursor (ring x e) (address e C.source)=.trail := by
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have mc : C∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨_,M,rfl⟩
  have H := raw_k2 g C mc K
  let d := if g.2.axes.h6 then L (3 : Fin 11) else R 2
  have dst : C.destination=some d := by rw [H]; cases h : g.2.axes.h6 <;> simp [d,h,link]
  have source : C.source=L 2 := by rw [H]; cases g.2.axes.h6 <;> simp [link]
  have noSelf := (BStarAcquireReturn.link_shape g C d mc dst).1
  have T := (BStarClearanceForward.move_lands g raw C f d dst M (Ne.symm noSelf)).1
  have J := BStarAcquireReturn.joined_reads _ _ _ _ _ _ _ _ _ hp (x e,x (rightNeighbor e)) C.source
    (fun hr _ => (by rw [source] at hr; contradiction))
  rw [←new_read B x e sep C.source,J]
  change decode (readRaw (patchPair (longWork g raw) raw) C.source)=_
  rw [T,BStarLongToken.decode_encode]

private theorem single {x : X} {addr : Nat → Pos n} {len : Nat} {e : Fin n}
    {z d : Cursor} (seen : Seen ring (project addr) anyTag len x z [e] d) :
    Advance len z d := by
  cases seen with
  | cons _ _ on _ tail => cases tail; exact on

/-- Selected K2 cannot be a stay. A same-op suffix ending outward
at the same K2 or earlier therefore rules out this departure. -/
theorem k2_no_depart_before_cut {base x : X} {addr : Nat→Pos n} {len op k : Nat}
    (e : Fin n) (sep : e≠rightNeighbor e) (C : CommandClaim) (f : Payload)
    (K : C.source.occurrence=2) (atK : address e C.source=addr k)
    (selected : (C,.advance f)∈actualOffers (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long))
    {z : Cursor} {w : List (Fin n)} {j : Nat}
    (E : Event hp addr len x e (.busy op (.out k)) (.busy op z))
    (rest : BusyOnly hp base addr len op (ring x e) z w (.out j)) :
    k<j := by
  obtain ⟨m,H⟩ := busy_no_back_to_out hp rest ⟨j,rfl⟩
  subst z
  have A : Advance len (.out k) (.out m) := by
    cases E with
    | transit _ _ _ _ N => exact single hp N
  have mono := BStarCommitNoPrior.outward_mono hp rest m j rfl rfl
  cases A with
  | forward => omega
  | stay =>
    have T := k2_departure_trail hp x e sep C f selected K
    have next := (busy_start hp rest).2.1.2.1
    change anyTag.F (atCursor (ring x e) (addr k)) at next
    rw [←atK,T] at next
    exact (BStarSeparatorParked.forward_not_trail next).elim

open BStarResetChartTouch BStarResetChartIndex BStarCopyGateAuthority
open BStarGeneratedBandScan BStarLongCommand

/-- No old RS preparation can touch this source on a real PC10
prefix ending at the source's own K2, even if marks spend arbitrarily
long at that K2. A winner would force the cursor strictly past it. -/
theorem no_rs_prep_until_inject {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n, e≠rightNeighbor e)
    (lead : List (Fin n)) (e i : Fin n) (k j : Nat) (kl : k≤len)
    (atSource : S.getD k fall=(i,2))
    (own : dataOwner (oldH6 B base) i .rs=o.val)
    (hist : GeneratedOwner hp base (fun t => S.getD t fall) len origin .idle lead (.busy 10 (.out j)))
    (now : Current hp base (fun t => S.getD t fall) len (BStarResetSchedule.run ring origin lead) (.busy 10 (.out j)))
    (same : ∀ i,BStarLongFixedRouting.Layout B base i=
      BStarLongFixedRouting.Layout B (BStarResetSchedule.run ring origin lead) i)
    {z : Cursor} {w : List (Fin n)}
    (E : Event hp (fun t => S.getD t fall) len (BStarResetSchedule.run ring origin lead) e
      (.busy 10 (.out j)) (.busy 10 z))
    (rest : BusyOnly hp base (fun t => S.getD t fall) len 10
      (ring (BStarResetSchedule.run ring origin lead) e) z w (.out k)) :
    let y := BStarResetSchedule.run ring origin lead
    let raw : Pair (BitVec LW) := ((y e).long,(y (rightNeighbor e)).long)
    ∀ s : Side, site e s=i → (⟨s,.rs⟩ : At Sheet)∉reserved (round (oldPair B y e) raw).prep := by
  dsimp only
  intro s siteEq M
  let y := BStarResetSchedule.run ring origin lead
  let g := oldPair B y e
  let raw : Pair (BitVec LW) := ((y e).long,(y (rightNeighbor e)).long)
  obtain ⟨a,win,lane⟩ := List.mem_map.mp M
  have owned : dataOwner (oldH6 B base) (site e a.claim.lane.side) a.claim.lane.occurrence=o.val := by
    rw [lane]
    exact siteEq.symm ▸ own
  have P := winning_prep_pc hp chart sep hist now same e a owned win
  have pc := now.1.2.2.2
  change BStarGeneratedBandScan.pc y (S.getD 0 fall).1=10 at pc
  rw [pc] at P
  have inject : a.claim.op=.inject := (Option.some.inj P).symm
  obtain ⟨D,_,_,_,_,_,_,do_,sd,PS⟩ := winner_origin g raw a win
  rw [lane,inject] at PS
  have occ : D.source.occurrence=2 := by
    simp only [prepSites] at PS
    split at PS
    · split at PS
      · simp at PS
      · split at PS <;> simp_all
    · simp at PS
  have sourceOccurrence : a.claim.origin.occurrence=2 := (congrArg At.occurrence do_).trans occ
  have sourceSide : a.claim.origin.side=s :=
    ((congrArg At.side do_).trans sd.symm).trans (congrArg At.side lane)
  obtain ⟨C,_,q,_,act,_,_,orig,owner⟩ := winner_owner hp y e a win
  have h6 : oldH6 B y=oldH6 B base := funext fun t => (congrArg Prod.fst (same t)).symm
  rw [h6,owned] at owner
  obtain ⟨l,J,atL⟩ := actual_owner_departure hp chart same e C q (.out j) act owner now.2.1 now.2.2
  have eq : l=j := Cursor.out.inj J.symm
  subst l
  have K : C.source.occurrence=2 := (congrArg At.occurrence orig).symm.trans sourceOccurrence
  have cs : C.source.side=s := (congrArg At.side orig).symm.trans sourceSide
  have matchK : address e C.source=(i,2) := by
    change (site e C.source.side,C.source.occurrence)=(i,2)
    rw [cs,K,siteEq]
  have lenJ := now.2.1.1
  have pos : j=k := (List.getD_inj (by have := chart.length; omega)
    (by have := chart.length; omega) chart.nodup).mp
    (atL.trans (matchK.trans atSource.symm))
  have cross := k2_no_depart_before_cut hp e (sep e) C q K atL.symm act E rest
  omega

end L4.BStarCopyRightK2Past
