import Leader.L4.BStarSealHealthyIdle
import Leader.L4.BStarCommitHealthyFlight
import Leader.L4.BStarSealReturn

namespace L4.BStarSealHealthyFlight
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongTransport BStarLongRouting BStarLongEvents
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireForwardTrace BStarAcquireLiteralChain
open BStarLongFixedRouting BStarResetChartTouch BStarResetMarkAdapter BStarResetRailRing
open BStarSeparatingRail BStarSeparatorControl BStarSeparatorQuiet BStarResetChartService
open BStarOwnerLaunchOrigin BStarGeneratedOwner BStarAcquireHistorySample
open BStarClearanceForward BStarResetQuiet
open BStarSealHealthyOffer BStarSealHealthyHop BStarSealHealthyIdle

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

private theorem out_le {base x : X} {addr : Nat→Pos n} {len op : Nat}
    {w : List (Fin n)} {z d : Cursor} (T : BusyOnly hp base addr len op x z w d) :
    ∀ k l,z=.out k → d=.out l → k≤l := by
  induction T with
  | nil _ =>
    intro _ _ A D
    exact Nat.le_of_eq (Cursor.out.inj (A.symm.trans D))
  | @cons x z d fin e w I E T ih =>
    intro k l Z L
    subst z
    obtain ⟨k',E'⟩ := busy_no_back_to_out hp T ⟨l,L⟩
    subst d
    have A : Advance len (.out k) (.out k') := by
      cases E with
      | transit _ _ _ _ seen => cases seen with
        | cons _ _ A _ tail => cases tail; exact A
    exact Nat.le_trans (by cases A <;> omega) (ih k' l rfl L)

/-- Forward closure of exact canonical SEAL bytes through any actual
outward interval ending at a preterminal center. Earlier chart slots
are required not to be an H6 K1; no seal or future publish hypothesis
is used. A busy history cannot move out of its endpoint index and back. -/
theorem before_center {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {z d : Cursor}
    (T : BusyOnly hp base (fun j=>S.getD j fall) len sealOp x z w d) (first : Nat) :
    ∀ k l (pay : Payload), z=.out k → d=.out l → l≤len → first≤k →
      project (fun j=>S.getD j fall) x k=.forward pay → Well pay →
      (∀ pre e post,w=pre++e::post → ∀ j<l, first≤j →
        (S.getD j fall).2.val≠1 ∨ oldH6 B (play x pre) (S.getD j fall).1=false) →
      project (fun j=>S.getD j fall) (play x w) l=.forward pay := by
  induction T with
  | nil _ =>
    intro k l pay Z D _ _ F _ _
    have eq := Cursor.out.inj (Z.symm.trans D)
    exact eq ▸ F
  | @cons x z d fin e w I E T ih =>
    intro k l pay Z L bound lower F H safe
    subst z
    obtain ⟨k',D⟩ := busy_no_back_to_out hp T ⟨l,L⟩
    subst d
    have K' : k'≤l := out_le hp T k' l rfl L
    have A : Advance len (.out k) (.out k') := by
      cases E with
      | transit _ _ _ _ seen => cases seen with
        | cons _ _ A _ tail => cases tail; exact A
    let addr := fun j=>S.getD j fall
    have Q := busy_start hp T
    have uniq (j : Nat) (jL : j≤len) (f : project addr (step x e) j=.forward pay) : j=k' :=
      (BStarOwnerControlHistory.pointed_unique_forward _ len k' Q.2.1 Q.2.2 j jL).mp ⟨pay,f⟩
    have FP : project addr (step x e) k'=.forward pay := by
      by_cases link : linkAt hp x e addr len k
      · obtain ⟨kl,K,a,mem,dest,src,dst⟩ := link
        have lt : k<l := by
          cases A with
          | forward => omega
          | stay =>
            -- A logical stutter would retain F at the old slot, but
            -- this selected actual SEAL writes Trail at its source.
            exfalso
            have Hk := Q.2.1.2.1
            let pair := (x e,x (rightNeighbor e))
            let g := oldPair B x e
            let raw := ((x e).long,(x (rightNeighbor e)).long)
            have R : readK raw K.source=.forward pay :=
              (old_read x e K.source).trans ((congrArg (atCursor x) src).symm.trans F)
            have shape := BStarAcquireReturn.link_shape g K a mem dest
            have selected := selected_well g raw K pay mem (by rw [shape.2.1]; decide) H R
            have safeSource := ((frames_any hp C I.1.1 e (.out k) (by intro F; cases F)
              I.2.1 I.1.2.1 I.1.2.2.1).safe k (Nat.le_of_lt kl) K.source src).2
            have moved := (move_lands g raw K pay a dest selected (Ne.symm shape.1)).1
            have read : readK (Pair.map LargeSite.long (largePair B pair)) K.source=.trail := by
              change decode (readRaw _ K.source)=_
              erw [BStarResetQuiet.joined_work_raw _ _ _ _ _ _ _ _ _ hp pair K.source safeSource.valid,
                moved,decode_encode]
            have post := (congrArg (atCursor (step x e)) src).trans ((new_read B x e (sep e) _).symm.trans read)
            obtain ⟨q,hq⟩ := Hk
            exact Token.noConfusion (post.symm.trans hq)
        have srcSafe : K.source.occurrence.val≠1 ∨ (geometry (oldPair B x e) K.source.side).axes.h6=false := by
          have ss := safe [] e w rfl k lt lower
          change (addr k).2.val≠1 ∨ oldH6 B x (addr k).1=false at ss
          rw [src] at ss
          cases hs : K.source.side <;> simpa [address,site,oldPair,oldH6,geometry,hs,longGeometry] using ss
        have R := (old_read x e K.source).trans ((congrArg (atCursor x) src).symm.trans F)
        have out := joined_before_center k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x (rightNeighbor e))
          K a pay mem dest srcSafe R H
        have E' : project addr (step x e) (k+1)=.forward pay :=
          (congrArg (atCursor (step x e)) dst).trans ((new_read B x e (sep e) a).symm.trans out)
        exact uniq (k+1) kl E' ▸ E'
      · have noT : k=len → ¬onTerminal hp x e addr len := by
          intro E term
          obtain ⟨K,mem,kind,dest,at10,src⟩ := term
          have eq : k'=k := by cases A <;> omega
          have Raw := (old_read x e K.source).trans ((congrArg (atCursor x) src).symm.trans (E ▸ F))
          have selected := selected_well (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)
            K pay mem (by rw [kind]; decide) H Raw
          obtain ⟨q,U,_,_,_,_,_⟩ := BStarSealReturn.turn_lands_polarity hp C e (sep e) K pay src at10 dest
            selected H.fault H.opcode
          obtain ⟨f,V⟩ := Q.2.1.2.1
          have V' : project addr (step x e) len=.forward f := (eq.trans E) ▸ V
          exact Token.noConfusion (U.symm.trans V')
        obtain ⟨_,hold⟩ := silent_at_seal hp C e (sep e) sealOp k I.1 pay I.2.1 F H link noT
        have old : project addr (step x e) k=.forward pay := hold.trans F
        exact uniq k I.2.1.1 old ▸ old
    have Kmon : k≤k' := by cases A <;> omega
    exact ih k' l pay rfl L bound (Nat.le_trans lower Kmon) FP H
      (fun u a v WW j J JJ => safe (e::u) a v (congrArg (List.cons e) WW) j J JJ)

#print axioms before_center



open BStarSealParity BStarLongPublication BStarLongLayout

/-- Accepted SEAL center departure writes the exact NEED polarity to
the physical joined destination and retains full wire well-formedness. -/
theorem joined_accepted_seal (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (K : CommandClaim) (a : AtK) (pay : Payload) (d : Descriptor)
    (H : Well pay) :
    let g := Pair.map (longGeometry B) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    K.source.occurrence=1 → (geometry g K.source.side).axes.h6=true →
    K.destination=some a → (K,.advance pay)∈actualOffers g raw →
    BStarLongPublication.decode (BitVec.ofNat 7 (pay.argument.toNat/2))=some d →
    BStarLongOutgoing.actual (atOld raw K.source) d=true →
    readOptional (stage.read (atOld raw K.source))=some d →
    ∃ q : Payload, readK (Pair.map LargeSite.long (largePair B x)) a=.forward q ∧
      Well q ∧ parity q=d.need.toNat := by
  dsimp only
  intro k1 head dst sel D auth stageEq
  let g := Pair.map (longGeometry B) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  have mem : K∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨_,sel,rfl⟩
  let m := 2*(pay.argument.toNat/2)+d.need.toNat
  let q : Payload := {pay with argument:=BitVec.ofNat 34 m}
  have small : m<2^8 := by
    have P := H.small
    cases NN : d.need <;> simp [m,NN] <;> omega
  have exactArg : q.argument.toNat=m := by
    change (BitVec.ofNat 34 m).toNat=m
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have half : m/2=pay.argument.toNat/2 := by
    cases C : d.need <;> simp [m,C] <;> omega
  have width : forwardWidth sealOp q.argument.toNat=some 8 := by
    rw [exactArg]
    simp [forwardWidth,sealOp,admit,bitOp,acquire,copyLoad,stageOp,descOK,half,D]
  have qH : Well q := ⟨H.fault,H.opcode,H.race,H.outcome,width,exactArg.symm ▸ small⟩
  have par : parity q=d.need.toNat := by
    change q.argument.toNat%2=_
    rw [exactArg]
    cases C : d.need <;> simp [m,C,Nat.add_mod]
  change (geometry g K.source.side).axes.h6=true at head
  change BStarLongOutgoing.actual (atOld raw K.source) d=true at auth
  change readOptional (stage.read (atOld raw K.source))=some d at stageEq
  have carriedEq : carried g raw K pay=q := by
    have node : BStarLongArithmetic.nodeOf 409=none := by decide
    unfold carried
    simp [BStarLongArithmetic.visit,H.opcode,node,sealOp,BStarLongOutgoing.execute,k1,head,
      H.fault,D,auth,stageEq,stageOp,q,m]
  have neq := (BStarAcquireReturn.link_shape g K a mem dst).1
  have V : a=R 0 → g.2.axes.h6=true → LongDoorGuard.valid manifest raw.2=true := by
    intro E Z
    have J : a.occurrence.val=0 := congrArg (fun z : AtK => z.occurrence.val) E
    have W := (BStarAcquireJoinedHop.k0_dest g K a mem dst J).2
    simp [Z] at W
  have A := (move_lands g raw K pay a dst sel (Ne.symm neq)).2
  refine ⟨q,?_,qH,par⟩
  change BStarLongToken.decode (readRaw _ a)=_
  rw [joined_work_raw _ _ _ _ _ _ _ _ _ hp x a V,A,BStarLongToken.decode_encode,carriedEq]
  simp [arrive,qH.opcode,gate,sealOp,bitOp,admit]

private theorem busy_prefix_seal_layout {base x : X} {addr : Nat→Pos n} {len op : Nat}
    {w : List (Fin n)} {z d : Cursor} (T : BusyOnly hp base addr len op x z w d) :
    ∀ u v,w=u++v → ∀ i,oldH6 B (play x u) i=oldH6 B base i := by
  induction T with
  | nil I =>
    intro u v E i
    have U : u=[] := (List.append_eq_nil_iff.mp E.symm).1
    subst u
    exact (congrArg Prod.fst (I.1.1 i)).symm
  | @cons x z z' d e w I ev tail ih =>
    intro u v E i
    cases u with
    | nil => exact (congrArg Prod.fst (I.1.1 i)).symm
    | cons f u =>
      have E' := (List.cons.inj (show e::w=f::(u++v) from E)).2
      have H := (List.cons.inj (show e::w=f::(u++v) from E)).1
      subst f
      exact ih u v E' i

/-- Exact SEAL bytes on every actual later outward cut after the unique
owner center. K10 and later stutters at K10 are included. -/
theorem after_center {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (s l : Nat) (J : s<l) (L : l≤len)
    (centerK : (S.getD s fall).2=1)
    (centerH : oldH6 B base (S.getD s fall).1=true)
    (w : List (Fin n)) (pay : Payload) (H : Well pay)
    (old : project (fun j=>S.getD j fall) x (s+1)=.forward pay)
    (T : BusyOnly hp base (fun j=>S.getD j fall) len sealOp x (.out (s+1)) w (.out l)) :
    project (fun j=>S.getD j fall) (play x w) l=.forward pay := by
  apply before_center hp C sep T (s+1) (s+1) l pay rfl rfl L (Nat.le_refl _) old H
  intro u e v E j jl lower
  by_cases K : (S.getD j fall).2.val=1
  · right
    apply Bool.eq_false_iff.mpr
    intro head
    have A := BStarCommitHealthyFlight.unique_center_index hp C (busy_prefix_seal_layout hp T u (e::v) E)
      s j (by omega) (by omega) centerK centerH (Fin.ext K) head
    omega
  · exact .inl K

#print axioms joined_accepted_seal
#print axioms after_center

/-- Same actual center mark, outward tape, selected terminal and return
ACK. No independent old-state or same-valued payload is chosen. -/
theorem accepted_center_to_ack {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (s : Nat) (J : s<len) (center turn : Fin n)
    (loc : S.getD s fall=(center,1)) (head : oldH6 B base center=true)
    (K : CommandClaim) (a : AtK) (p f : Payload) (d : Descriptor)
    (current : Current hp base (fun j=>S.getD j fall) len x (.busy sealOp (.out s)))
    (src : K.source=L 1) (dst : K.destination=some a)
    (next : S.getD (s+1) fall=address center a)
    (selected : (K,.advance p)∈actualOffers (oldPair B x center)
      ((x center).long,(x (rightNeighbor center)).long))
    (H : Well p) (decoded : BStarLongPublication.decode (BitVec.ofNat 7 (p.argument.toNat/2))=some d)
    (auth : BStarLongOutgoing.actual (x center).long d=true)
    (staged : readOptional (stage.read (x center).long)=some d)
    (out back : List (Fin n))
    (Out : BusyOnly hp base (fun j=>S.getD j fall) len sealOp (step x center) (.out (s+1)) out (.out len))
    (term : onTerminal hp (play (step x center) out) turn (fun j=>S.getD j fall) len)
    (Ret : BusyOnly hp base (fun j=>S.getD j fall) len sealOp
      (step (play (step x center) out) turn) (.back len) back (.back 0))
    (Ack : let y := play (step (play (step x center) out) turn) back (S.getD 0 fall).1
      BStarLongCommand.bind (longGeometry B y) 0 (atSite y.long 0)=.reply f)
    (F : f.fault=0) (O : f.opcode.toNat=sealOp) :
    parity f=d.need.toNat := by
  let oldPairSite := (x center,x (rightNeighbor center))
  let g := oldPair B x center
  let raw := ((x center).long,(x (rightNeighbor center)).long)
  have hc : oldH6 B x center=true :=
    (congrArg Prod.fst (current.1.1 center)).symm.trans head
  have gh : (geometry g K.source.side).axes.h6=true := by rw [src]; exact hc
  have aa : atOld raw K.source=(x center).long := by rw [src]; rfl
  obtain ⟨q,Q,qH,bit⟩ := joined_accepted_seal hp oldPairSite K a p d H
    (congrArg (fun t : AtK => t.occurrence) src) gh dst selected decoded (aa.symm ▸ auth) (aa.symm ▸ staged)
  have atNext : project (fun j=>S.getD j fall) (step x center) (s+1)=.forward q :=
    (congrArg (atCursor (step x center)) next).trans ((new_read B x center (sep center) a).symm.trans Q)
  have atEnd := after_center hp C sep s len J (Nat.le_refl _) (congrArg Prod.snd loc)
    (by rw [loc]; exact head) out q qH atNext Out
  obtain ⟨U,mem,kind,noDst,k10,addr⟩ := term
  let y := play (step x center) out
  have rawEnd := (old_read y turn U.source).trans ((congrArg (atCursor y) addr).symm.trans atEnd)
  have offered := selected_well (oldPair B y turn) ((y turn).long,(y (rightNeighbor turn)).long)
    U q mem (by rw [kind]; decide) qH rawEnd
  exact (BStarSealReturn.terminal_to_actual_ack hp C sep turn U q f addr k10 noDst offered
    qH.fault qH.opcode back Ret Ack F O).trans bit

#print axioms accepted_center_to_ack

open BStarLongDoor BStarClearanceSource BStarResetControllerEntry BStarLongLiteral

/-- The literal old ISSUE409 descriptor becomes a canonical SEAL
packet. The old source is the given physical launch, not a recovered
same-valued template. -/
theorem launched_well (old new : BitVec LW) (op : (ctrlOp.read old).toNat=sealOp)
    (L : Launch old new) (d : Descriptor)
    (D : BStarLongPublication.decode (sourceDescriptor.read old)=some d) :
    ∃ p,atSite new 0=.forward p ∧ Well p ∧
      BStarLongPublication.decode (BitVec.ofNat 7 (p.argument.toNat/2))=some d := by
  obtain ⟨_,a,I,S⟩ := L
  let num := (sourceDescriptor.read old).toNat
  have eq : a=2*num := by
    have crop : BitVec.ofNat 7 num=sourceDescriptor.read old := by
      dsimp only [num]; simp
    rw [op] at I
    simp [initial,sealOp,acquire,copyLoad,stageOp,commitOp,crop,D,num] at I
    exact I.symm
  subst a
  let p : Payload := ⟨0,BitVec.ofNat 9 sealOp,0,0,BitVec.ofNat 34 (2*num)⟩
  have numLt : num<2^7 := (sourceDescriptor.read old).isLt
  have small : 2*num<2^8 := by omega
  have A : p.argument.toNat=2*num := by
    change (BitVec.ofNat 34 (2*num)).toNat=_
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have DD : BStarLongPublication.decode (BitVec.ofNat 7 (p.argument.toNat/2))=some d := by
    rw [A,show 2*num/2=num by omega]
    change BStarLongPublication.decode (BitVec.ofNat 7 (sourceDescriptor.read old).toNat)=_
    simpa using D
  have width : forwardWidth sealOp p.argument.toNat=some 8 := by
    simp [forwardWidth,sealOp,admit,bitOp,acquire,copyLoad,stageOp,descOK,DD]
  have E := congrArg (fun z : (Token × BitVec 2) × BitVec 9 => z.1.1) S
  change atSite new 0=forward (ctrlOp.read old).toNat (2*num) at E
  rw [op] at E
  exact ⟨p,E,⟨rfl,rfl,rfl,rfl,width,A.symm ▸ small⟩,DD⟩

/-- On the genuine outward tape from ISSUE409 to the owner center, the
selected old offer still carries the actual source descriptor. -/
theorem selected_at_center {base start : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (door e : Fin n) (w : List (Fin n)) (l : Nat) (L : l<len)
    (loc : S.getD l fall=(e,1))
    (center : oldH6 B base e=true)
    (op : (ctrlOp.read (start (S.getD 0 fall).1).long).toNat=sealOp)
    (launch : Launch (start (S.getD 0 fall).1).long ((step start door) (S.getD 0 fall).1).long)
    (T : BusyOnly hp base (fun j=>S.getD j fall) len sealOp (step start door) (.out 0) w (.out l))
    (d : Descriptor)
    (D : BStarLongPublication.decode (sourceDescriptor.read (start (S.getD 0 fall).1).long)=some d) :
    let y := play (step start door) w
    let g := oldPair B y e
    let raw := ((y e).long,(y (rightNeighbor e)).long)
    ∃ p, Well p ∧ (centerLink g,.advance p)∈actualOffers g raw ∧
      BStarLongPublication.decode (BitVec.ofNat 7 (p.argument.toNat/2))=some d := by
  let x := step start door
  let addr := fun j=>S.getD j fall
  obtain ⟨p,P,H,DD⟩ := launched_well _ _ op launch d D
  have k0 : (addr 0).2=0 := congrArg Prod.snd C.root
  have init : project addr x 0=.forward p := by
    change atSite (x (addr 0).1).long (addr 0).2=_
    rwa [k0]
  have avoid (u : List (Fin n)) (a : Fin n) (v : List (Fin n)) (E : w=u++a::v) (j : Nat) (J : j<l) :
      (addr j).2.val≠1 ∨ oldH6 B (play x u) (addr j).1=false := by
    by_cases K : (addr j).2.val=1
    · right
      apply Bool.eq_false_iff.mpr
      intro header
      have fixed := busy_prefix_seal_layout hp T u (a::v) E
      have E' := BStarCommitHealthyFlight.unique_center_index hp C fixed l j (Nat.le_of_lt L) (by omega)
        (congrArg Prod.snd loc) (by rwa [congrArg Prod.fst loc]) (Fin.ext K) header
      omega
    · exact .inl K
  have R := before_center hp C sep T 0 0 l p rfl rfl (Nat.le_of_lt L) (Nat.le_refl _) init H
    (fun u a v E j J _ => avoid u a v E j J)
  let y := play x w
  let g := oldPair B y e
  let raw := ((y e).long,(y (rightNeighbor e)).long)
  have wire : readK raw (centerLink g).source=.forward p := by
    change atSite (y e).long 1=_
    change atCursor y (S.getD l fall)=_ at R
    rwa [loc] at R
  exact ⟨p,H,selected_well g raw (centerLink g) p (center_mem g) (show Cmd.link≠Cmd.door by decide) H wire,DD⟩

#print axioms launched_well
#print axioms selected_at_center
end L4.BStarSealHealthyFlight
