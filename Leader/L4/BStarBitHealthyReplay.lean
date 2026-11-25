import Leader.L4.BStarBitHealthyIdle

namespace L4.BStarBitHealthyReplay
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongTransport BStarLongEvents
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireForwardTrace BStarAcquireLiteralChain
open BStarLongFixedRouting BStarResetChartTouch BStarResetMarkAdapter
open BStarSeparatingRail BStarGeneratedOwner BStarOwnerLaunchOrigin
open BStarBitHealthyService BStarBitUniqueGate BStarBitGateGeometry BStarClearanceOffset BStarH6Ordinal

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- Every earlier physical mark either stutters or advances one slot,
retaining the exact well-formed BIT. No scheduler premise. -/
theorem arbitrary_pregate_step {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (l : Nat) (L : l<len) (gateK : (S.getD l fall).2=1)
    (gateH : oldOrdinal B base hh (S.getD l fall).1=4)
    (j : Nat) (J : j<l) (qx : Q x) (ready : correct (oldH6 B base) hh 5 x) (e : Fin n) (pay : Payload) (well : Wire pay)
    (cur : Current hp base (fun k=>S.getD k fall) len x (.busy bitOp (.out j)))
    (old : project (fun k=>S.getD k fall) x j=.forward pay) :
    ∃ k, j≤k ∧ k≤j+1 ∧
      Event hp (fun t=>S.getD t fall) len x e (.busy bitOp (.out j)) (.busy bitOp (.out k)) ∧
      Current hp base (fun t=>S.getD t fall) len (step x e) (.busy bitOp (.out k)) ∧
      project (fun t=>S.getD t fall) (step x e) k=.forward (if k=l then {pay with race:=1,argument:=0} else pay) ∧
      (linkAt hp x e (fun t=>S.getD t fall) len j → k=j+1) := by
  have fixed : ∀ i,oldH6 B x i=oldH6 B base i := fun i => (congrArg Prod.fst (fiber x qx i)).symm
  have on : gate bitOp (S.getD l fall).2 (longGeometry B (x (S.getD l fall).1))=true := by
    rw [gateK]
    exact (bit_gate_iff hp hh fixed ready _ 1).mpr ⟨rfl,gateH⟩
  have one (j : Nat) (J : j≤len) :
      gate bitOp (S.getD j fall).2 (longGeometry B (x (S.getD j fall).1))=true ↔ j=l :=
    ⟨fun H => chart_no_second_gate hp C fixed ready J (Nat.le_of_lt L) H on, fun E => E.symm ▸ on⟩
  have away := Bool.eq_false_iff.mpr (fun H => (Nat.ne_of_lt J) ((one j (by omega)).mp H))
  by_cases link : linkAt hp x e (fun t=>S.getD t fall) len j
  · obtain ⟨E,I,F⟩ := nominated_step hp C Q fiber closed sep qx e j pay cur old well link away
    exact ⟨j+1,by omega,Nat.le_refl _,E,I,by simpa only [one (j+1) (by omega)] using F,fun _ => rfl⟩
  · obtain ⟨m,ev,nxt⟩ := current_step hp C Q fiber closed sep qx e (.busy bitOp (.out j)) cur
    have K : j<len := by omega
    have silent := (BStarBitHealthyIdle.silent_at_bit hp C e (sep e) bitOp j cur.1 pay
      cur.2.1 old well away link (fun E => (Nat.ne_of_lt K E).elim)).2
    have F : project (fun t=>S.getD t fall) (step x e) j=.forward pay := silent.trans old
    cases ev with
    | transit _ _ d live seen =>
      cases seen with
      | cons M go adv gd tail =>
        cases tail
        cases adv with
        | stay => exact ⟨j,Nat.le_refl _,by omega,.transit _ _ _ live (.cons M go (.stay _) gd (.nil _ _)),nxt,by simpa only [if_neg (Nat.ne_of_lt J)] using F,
            fun H => (link H).elim⟩
        | forward =>
          have E := (BStarOwnerControlHistory.pointed_unique_forward _ len (j+1) nxt.2.1 nxt.2.2 j (by omega)).mp ⟨pay,F⟩
          omega
        | turn => omega

/-- A replay with the nominated ordered subsequence reaches the gate
on some prefix. Intervening marks may help but cannot undo progress or
change the well-formed BIT before that first gate cut. -/
theorem reaches_gate_of_sublist {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (l : Nat) (L : l<len) (gateK : (S.getD l fall).2=1)
    (gateH : oldOrdinal B base hh (S.getD l fall).1=4)
    (pay : Payload) (well : Wire pay)
    {ls w : List (Fin n)} (sub : ls.Sublist w) :
    ∀ (x : X) (a j : Nat), a+ls.length=l → a≤j → j≤l → Q x → correct (oldH6 B base) hh 5 x →
      Current hp base (fun t=>S.getD t fall) len x (.busy bitOp (.out j)) →
      project (fun t=>S.getD t fall) x j=.forward (if j=l then {pay with race:=1,argument:=0} else pay) →
      (∀ k (hk : k<ls.length) (y : X), (∀ i,Layout B base i=Layout B y i) →
        linkAt hp y ls[k] (fun t=>S.getD t fall) len (a+k)) →
      ∃ pre post, w=pre++post ∧
        BusyOnly hp base (fun t=>S.getD t fall) len bitOp x (.out j) pre (.out l) ∧
        project (fun t=>S.getD t fall) (play x pre) l=.forward {pay with race:=1,argument:=0} := by
  induction sub with
  | slnil =>
    intro state a j J A U _ _ I F _
    have eq : j=l := by simp at J; omega
    subst j
    exact ⟨[],[],rfl,.nil I,by simpa only [if_pos rfl,if_true,BStarResetSchedule.run] using F⟩
  | @cons ls w e sub ih =>
    intro state a j J A U q ready I F nominate
    by_cases eqa : j=l
    · subst j
      exact ⟨[],e::w,rfl,.nil I,by simpa only [if_pos rfl,if_true,BStarResetSchedule.run] using F⟩
    have jl : j<l := by omega
    rw [if_neg (Nat.ne_of_lt jl)] at F
    obtain ⟨k,jk,K,E,now,new,_⟩ := arbitrary_pregate_step hp C Q fiber closed sep l L
      gateK gateH j jl q ready e pay well I F
    have offset := stable hp _ hh state e (sep e)
      (fun i => (congrArg Prod.fst (fiber state q i)).symm)
      (BStarClearanceOffsetMask.leftFrame hp state e) ready
    obtain ⟨pre,post,W,T,P⟩ := ih (step state e) a k J (by omega) (by omega) (closed _ q e) offset
      now new nominate
    exact ⟨e::pre,post,congrArg (List.cons e) W,.cons I E T,P⟩
  | @cons_cons ls w e sub ih =>
    intro state a j J A U q ready I F nominate
    by_cases eqa : j=l
    · subst j
      exact ⟨[],e::w,rfl,.nil I,by simpa only [if_pos rfl,if_true,BStarResetSchedule.run] using F⟩
    have jl : j<l := by omega
    rw [if_neg (Nat.ne_of_lt jl)] at F
    obtain ⟨k,jk,K,E,now,new,served⟩ := arbitrary_pregate_step hp C Q fiber closed sep l L
      gateK gateH j jl q ready e pay well I F
    have kA : a+1≤k := by
      by_cases same : a=j
      · subst a
        have link := nominate 0 (by simp) state (fiber state q)
        have eq := served (by simpa using link)
        omega
      · omega
    have nom' (t : Nat) (ht : t<ls.length) (y : X) (H : ∀ i,Layout B base i=Layout B y i) :
        linkAt hp y ls[t] (fun t=>S.getD t fall) len ((a+1)+t) := by
      have link := nominate (t+1) (by simp; omega) y H
      have eq : a+(t+1)=(a+1)+t := by omega
      simpa only [List.getElem_cons_succ,eq] using link
    have offset := stable hp _ hh state e (sep e)
      (fun i => (congrArg Prod.fst (fiber state q i)).symm)
      (BStarClearanceOffsetMask.leftFrame hp state e) ready
    obtain ⟨pre,post,W,T,P⟩ := ih (step state e) (a+1) k (by simp at J; omega) kA (by omega)
      (closed _ q e) offset now new nom'
    exact ⟨e::pre,post,congrArg (List.cons e) W,.cons I E T,P⟩

open BStarClearanceSource BStarLongDoor

/-- Start the arbitrary replay theorem at a genuine canonical
ISSUE410, rather than requiring the caller to supply its packet. -/
theorem launch_replay_to_gate {base old : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (g : Fin n) (l : Nat) (L : 0<l ∧ l<len)
    (loc : S.getD l fall=(g,1)) (ord : oldOrdinal B base hh g=4)
    (door : Fin n) (op : (ctrlOp.read (old (S.getD 0 fall).1).long).toNat=bitOp)
    (launch : Launch (old (S.getD 0 fall).1).long ((step old door) (S.getD 0 fall).1).long)
    (qx : Q (step old door)) (ready : correct (oldH6 B base) hh 5 (step old door))
    (I : Current hp base (fun k=>S.getD k fall) len (step old door) (.busy bitOp (.out 0)))
    {ls w : List (Fin n)} (sub : ls.Sublist w) (size : ls.length=l)
    (nom : ∀ (k : Nat) (h : k<ls.length) (y : X), (∀ i,Layout B base i=Layout B y i) →
      linkAt hp y ls[k] (fun t=>S.getD t fall) len k) :
    ∃ pre post pay, w=pre++post ∧
      BusyOnly hp base (fun t=>S.getD t fall) len bitOp (step old door) (.out 0) pre (.out l) ∧
      atSite (play (step old door) pre g).long 1=.forward pay ∧
      pay.fault=0 ∧ pay.opcode.toNat=bitOp ∧ pay.outcome=0 ∧ pay.race=1 ∧ pay.argument=0 := by
  let x := step old door
  obtain ⟨p,P,H,_⟩ := launched_wire _ _ op launch
  have kz : (S.getD 0 fall).2=0 := congrArg Prod.snd C.root
  have init : project (fun k=>S.getD k fall) x 0=.forward (if 0=l then {p with race:=1,argument:=0} else p) := by
    change atSite (x (S.getD 0 fall).1).long (S.getD 0 fall).2=_
    rw [kz,if_neg (by omega)]
    exact P
  have atL : oldOrdinal B base hh (S.getD l fall).1=4 := by rw [loc]; exact ord
  obtain ⟨pre,post,E,T,F⟩ := reaches_gate_of_sublist hp C Q fiber closed sep l L.2
    (congrArg Prod.snd loc) atL p H sub x 0 0 (by simpa using size) (by omega) (by omega) qx ready I init
    (fun k hk y H => by simpa only [Nat.zero_add] using nom k hk y H)
  change atCursor (play x pre) (S.getD l fall)=_ at F
  rw [loc] at F
  exact ⟨pre,post,_,E,T,F,H.fault,H.op,H.outcome,rfl,rfl⟩

end L4.BStarBitHealthyReplay
