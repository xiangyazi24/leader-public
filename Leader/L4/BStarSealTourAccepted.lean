import Leader.L4.BStarSealNoRefusal
import Leader.L4.BStarSealHealthyFlight
import Leader.L4.BStarNumericChronology
import Leader.L4.BStarAcquireAckAncestry

namespace L4.BStarSealTourAccepted
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken BStarLongCommand
open BStarLongDoor BStarLongLayout BStarLongEvents BStarLongLiteral BStarLongPublication
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarResetMarkAdapter BStarResetRailRing BStarOwnerLaunchOrigin BStarGeneratedOwner
open BStarSeparatingRail BStarAcquireForwardTrace BStarSeparatorControl
open BStarSealNoRefusal BStarSealHealthyFlight BStarSealHealthyHop BStarNumericChronology
open BStarClearanceSource BStarAcquireHistorySample BStarAcquireHistoryReturn BStarAcquireAckAncestry BStarResetChartService

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

private theorem outward_cross {base x : X} {addr : Nat → Pos n} {len op j : Nat}
    {a b : Cursor} {w : List (Fin n)}
    (H : BusyOnly hp base addr len op x a w b) :
    ∀ k l, a=.out k → b=.out l → k≤j → j<l →
      ∃ pre e post, w=pre++e::post ∧
        BusyOnly hp base addr len op x (.out k) pre (.out j) ∧
        Event hp addr len (play x pre) e (.busy op (.out j)) (.busy op (.out (j+1))) ∧
        BusyOnly hp base addr len op (step (play x pre) e) (.out (j+1)) post (.out l) := by
  induction H with
  | nil =>
    intro k l A D K L
    have := Cursor.out.inj (A.symm.trans D)
    omega
  | @cons x a next dest e w I E tail ih =>
    intro k l A D K L
    subst a
    have adv : Advance len (.out k) next := by
      cases E with
      | transit _ _ _ _ S =>
        cases S with
        | cons _ _ A _ R => cases R; exact A
    cases adv with
    | stay =>
      obtain ⟨pre,f,post,W,T,F,U⟩ := ih k l rfl D K L
      exact ⟨e::pre,f,post,congrArg (List.cons e) W,.cons I E T,F,U⟩
    | forward =>
      by_cases eq : k=j
      · subst k
        exact ⟨[],e,w,rfl,.nil I,E,D ▸ tail⟩
      · obtain ⟨pre,f,post,W,T,F,U⟩ := ih (k+1) l rfl D (by omega) L
        exact ⟨e::pre,f,post,congrArg (List.cons e) W,.cons I E T,F,U⟩
    | turn =>
      obtain ⟨_,eq⟩ := busy_no_back_to_out hp tail ⟨l,D⟩
      cases eq

/-- The genuine owner chart contains its unique H6 K1 center at a
strictly preterminal ordinal, including on a one-word ring. -/
theorem center_index {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) :
    ∃ i : Fin n, ∃ j : Nat, j<len ∧ S.getD j fall=(i,1) ∧
      oldH6 B base i=true := by
  let c := endpoint (oldH6 B base) hh o 1
  have H := endpoint_spec (oldH6 B base) hh o 1
  have slot : c.2=1 := rfl
  have active : BStarAcquireRailCoverage.active (longGeometry B (base c.1)) c.2=true := by
    rw [slot]
    rfl
  have own : BStarAcquireAnchors.commandOwner (oldH6 B base) c.1 c.2=o.val := by
    rw [slot]
    exact H.2.1
  obtain ⟨j,J,E⟩ := List.mem_iff_getElem.mp (C.cover c active own)
  have eq : S.getD j fall=c := (List.getElem_eq_getD fall).symm.trans E
  have sz := C.length
  have ne : j≠len := by
    intro N
    subst j
    have bad : (10 : Fin 11)=1 := congrArg Prod.snd (C.terminal.symm.trans eq)
    contradiction
  exact ⟨c.1,j,by omega,eq,H.1⟩

/-- A genuine SEAL launch and its same uninterrupted healthy ACK
locate the selected accepted H6 K1 and actual terminal on the original
tape; no nominated service word is substituted. -/
theorem accepted_from_tour {base start : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (door i : Fin n) (j : Nat) (J : j<len) (loc : S.getD j fall=(i,1))
    (head : oldH6 B base i=true)
    (op : (ctrlOp.read (start (S.getD 0 fall).1).long).toNat=sealOp)
    (launch : Launch (start (S.getD 0 fall).1).long ((step start door) (S.getD 0 fall).1).long)
    (d : Descriptor)
    (D : BStarLongPublication.decode (sourceDescriptor.read (start (S.getD 0 fall).1).long)=some d)
    (w : List (Fin n))
    (T : BusyOnly hp base (fun j=>S.getD j fall) len sealOp (step start door) (.out 0) w (.back 0))
    (f : Payload) (F : HealthySeal f)
    (Ack : let site := play (step start door) w (S.getD 0 fall).1
      bind (longGeometry B site) 0 (atSite site.long 0)=.reply f) :
    ∃ pre out back : List (Fin n), ∃ turn : Fin n,
      w=(pre++i::out)++turn::back ∧
      let y := play (step start door) pre
      let atTurn := play (step y i) out
      BusyOnly hp base (fun t=>S.getD t fall) len sealOp (step start door) (.out 0) pre (.out j) ∧
      Event hp (fun t=>S.getD t fall) len y i (.busy sealOp (.out j)) (.busy sealOp (.out (j+1))) ∧
      BusyOnly hp base (fun t=>S.getD t fall) len sealOp (step y i) (.out (j+1)) out (.out len) ∧
      onTerminal hp atTurn turn (fun t=>S.getD t fall) len ∧
      BusyOnly hp base (fun t=>S.getD t fall) len sealOp (step atTurn turn) (.back len) back (.back 0) ∧
      ∃ p, Well p ∧ (centerLink (oldPair B y i),.advance p)∈actualOffers (oldPair B y i)
        ((y i).long,(y (rightNeighbor i)).long) ∧
      BStarLongPublication.decode (BitVec.ofNat 7 (p.argument.toNat/2))=some d ∧
      BStarLongOutgoing.actual (y i).long d=true ∧
      readOptional (stage.read (y i).long)=some d := by
  let addr := fun t=>S.getD t fall
  let x := step start door
  obtain ⟨walk,turn,back,W,U,_,Ret⟩ := split_turn hp T
  obtain ⟨pre,e,out,V,Lead,Ev,Tail⟩ := outward_cross hp U 0 len rfl rfl (Nat.zero_le _) J
  let y := play x pre
  have turnEq : play x walk=play (step y e) out := by
    rw [V,BStarResetSchedule.run_append]
    rfl
  have ack' : let site := play (step (play x walk) turn) back (addr 0).1
      bind (longGeometry B site) 0 (atSite site.long 0)=.reply f := by
    simpa only [W,BStarResetSchedule.run_append,BStarResetSchedule.run] using Ack
  obtain ⟨p,pWalk,pH⟩ := terminal_of_ack hp C sep turn back f (busy_end hp U) Ret ack' F
  obtain ⟨s,hs,q,Q,qH,_⟩ := busy_origin hp C sep Tail len (Nat.le_refl _) p (turnEq ▸ pWalk) pH.1
  have cur := busy_end hp Lead
  have after := busy_start hp Tail
  have key := (BStarOwnerControlHistory.pointed_unique_forward _ len _ after.2.1 after.2.2 s hs).mp ⟨q,Q⟩
  subst s
  obtain ⟨K,a,offer,chosen,_,src,_⟩ :=
    ring_departure hp C e (sep e) sealOp j J cur.1 cur.2.1 cur.2.2 q Q qH
  have member : K∈orderedCommands (oldPair B y e) := by
    rw [←actualOffers_claims (oldPair B y e) ((y e).long,(y (rightNeighbor e)).long)]
    exact List.mem_map.mpr ⟨_,chosen,rfl⟩
  have at1 : K.source.occurrence.val=1 :=
    congrArg (fun u : Pos n=>u.2.val) (src.symm.trans loc)
  have equal := center_of _ K member at1
  rw [equal] at src
  have ei : e=i := congrArg Prod.fst (src.symm.trans loc)
  subst e
  have Old : Current hp base addr len (play (step y i) out) (.busy sealOp (.out len)) :=
    busy_end hp Tail
  have Ret' := turnEq ▸ Ret
  obtain ⟨Z,v,select,kind,dst,occ,atZ⟩ := BStarStageTerminalHealth.selected_turn hp C turn (sep turn)
    sealOp Old (busy_start hp Ret')
  have mem : Z∈orderedCommands (oldPair B (play (step y i) out) turn) := by
    rw [←actualOffers_claims _ (((play (step y i) out) turn).long,
      ((play (step y i) out) (rightNeighbor turn)).long)]
    exact List.mem_map.mpr ⟨_,select,rfl⟩
  obtain ⟨pay,H,sel,dec⟩ := selected_at_center hp C sep door i pre j J loc head op launch Lead d D
  obtain ⟨d',dec',auth,latch⟩ := ack_certifies_center hp C sep i j J loc head cur pay
    ⟨H.fault,H.opcode⟩ sel out turn back Tail Ret' f F (turnEq ▸ ack')
  rw [dec] at dec'
  cases dec'
  exact ⟨pre,out,back,turn,W.trans (congrArg (fun t=>t++turn::back) V),
    Lead,Ev,Tail,⟨Z,mem,kind,dst,occ,atZ⟩,Ret',pay,H,sel,dec,auth,latch⟩
end L4.BStarSealTourAccepted
