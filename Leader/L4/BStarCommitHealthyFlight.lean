import Leader.L4.BStarCommitHealthyIdle
import Leader.L4.BStarBitCommitFlight

namespace L4.BStarCommitHealthyFlight
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongTransport BStarLongRouting BStarLongEvents
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireForwardTrace BStarAcquireLiteralChain
open BStarLongFixedRouting BStarResetChartTouch BStarResetMarkAdapter BStarResetRailRing
open BStarSeparatingRail BStarSeparatorControl BStarSeparatorQuiet BStarResetChartService
open BStarOwnerLaunchOrigin BStarGeneratedOwner BStarAcquireHistorySample
open BStarClearanceForward BStarResetQuiet
open BStarCommitHealthyOffer BStarCommitHealthyHop BStarCommitHealthyIdle

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

/-- Forward closure of exact canonical COMMIT bytes through any actual
outward interval ending at a preterminal center. Earlier chart slots
are required not to be an H6 K1; no seal or future publish hypothesis
is used. A busy history cannot move out of its endpoint index and back. -/
theorem before_center {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {z d : Cursor}
    (T : BusyOnly hp base (fun j=>S.getD j fall) len commitOp x z w d) :
    ∀ k l (pay : Payload), z=.out k → d=.out l → l<len →
      project (fun j=>S.getD j fall) x k=.forward pay → Well pay →
      (∀ pre e post,w=pre++e::post → ∀ j<l,
        (S.getD j fall).2.val≠1 ∨ oldH6 B (play x pre) (S.getD j fall).1=false) →
      project (fun j=>S.getD j fall) (play x w) l=.forward pay := by
  induction T with
  | nil _ =>
    intro k l pay Z D _ F _ _
    have eq := Cursor.out.inj (Z.symm.trans D)
    exact eq ▸ F
  | @cons x z d fin e w I E T ih =>
    intro k l pay Z L bound F H safe
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
            -- this selected actual COMMIT writes Trail at its source.
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
          have ss := safe [] e w rfl k lt
          change (addr k).2.val≠1 ∨ oldH6 B x (addr k).1=false at ss
          rw [src] at ss
          cases hs : K.source.side <;> simpa [address,site,oldPair,oldH6,geometry,hs,longGeometry] using ss
        have R := (old_read x e K.source).trans ((congrArg (atCursor x) src).symm.trans F)
        have out := joined_before_center k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x (rightNeighbor e))
          K a pay mem dest srcSafe R H
        have E' : project addr (step x e) (k+1)=.forward pay :=
          (congrArg (atCursor (step x e)) dst).trans ((new_read B x e (sep e) a).symm.trans out)
        exact uniq (k+1) kl E' ▸ E'
      · have kLt : k<len := by cases A <;> omega
        obtain ⟨_,hold⟩ := silent_at_commit hp C e (sep e) commitOp k I.1 pay I.2.1 F H link
          (fun E => (Nat.ne_of_lt kLt E).elim)
        have old : project addr (step x e) k=.forward pay := hold.trans F
        exact uniq k (Nat.le_of_lt kLt) old ▸ old
    exact ih k' l pay rfl L bound FP H
      (fun u a v WW j J => safe (e::u) a v (congrArg (List.cons e) WW) j J)

open BStarLongDoor BStarCommitIssue BStarAcquireAnchors BStarClearanceSource BStarLongLayout

/-- A validated ISSUE411 launches a canonical, bindable packet. -/
theorem launched_well (old new : BitVec LW)
    (op : (ctrlOp.read old).toNat=commitOp) (L : Launch old new) :
    ∃ p,atSite new 0=.forward p ∧ Well p := by
  obtain ⟨_,a,I,S⟩ := L
  rw [op,commit_initial] at I
  cases D : BStarLongPublication.decode (sourceDescriptor.read old) with
  | none => rw [D] at I; contradiction
  | some d =>
    rw [D] at I
    change (if Allows old d then some (argument old) else none)=some a at I
    split at I
    · rename_i ok
      have eq := Option.some.inj I
      subst a
      have small : argument old<2^9 := by
        unfold argument
        have V := (sourceDescriptor.read old).isLt
        have C := (choice.read old).isLt
        omega
      let p : Payload := ⟨0,BitVec.ofNat 9 commitOp,0,0,BitVec.ofNat 34 (argument old)⟩
      have argP : p.argument.toNat=argument old := by
        change (BitVec.ofNat 34 (argument old)).toNat=argument old
        rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
      have DD : BitVec.ofNat 7 (argument old/4)=sourceDescriptor.read old := by
        have C := (choice.read old).isLt
        have K : argument old / 4=(sourceDescriptor.read old).toNat := by unfold argument; omega
        rw [K]
        simp
      have CC : argument old % 4=(choice.read old).toNat := by
        have C := (choice.read old).isLt
        unfold argument
        omega
      have width : forwardWidth commitOp p.argument.toNat=some 9 := by
        rw [argP]
        simp only [forwardWidth,show (commitOp==admit || commitOp==bitOp)=false by decide,
          show (commitOp==acquire)=false by decide,show (commitOp==copyLoad)=false by decide,
          show (commitOp==stageOp)=false by decide,show (commitOp==sealOp)=false by decide,
          beq_self_eq_true,if_true,Bool.false_eq_true,if_false,DD,D,CC]
        change (if Allows old d then some 9 else none)=some 9
        simp [ok]
      have f := congrArg (fun z : (Token × BitVec 2) × BitVec 9 => z.1.1) S
      change atSite new 0=forward (ctrlOp.read old).toNat (argument old) at f
      rw [op] at f
      exact ⟨p,f,⟨rfl,rfl,rfl,rfl,width,argP ▸ small⟩⟩
    · contradiction

/-- If the target address is a real H6 K1, no other index on this very
owner rail can also be an H6 K1. This includes small logical rings. -/
theorem unique_center_index {base y : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (fixed : ∀ i,oldH6 B y i=oldH6 B base i)
    (l j : Nat) (L : l≤len) (J : j≤len)
    (centerK : (S.getD l fall).2=1)
    (centerH : oldH6 B base (S.getD l fall).1=true)
    (otherK : (S.getD j fall).2=1)
    (otherH : oldH6 B y (S.getD j fall).1=true) : j=l := by
  let h := oldH6 B base
  let a := S.getD l fall
  let b := S.getD j fall
  have sz := C.length
  have ma : a∈S := by
    change S.getD l fall∈S
    rw [←List.getElem_eq_getD (h:=show l<S.length by omega)]
    exact List.getElem_mem _
  have mb : b∈S := by
    change S.getD j fall∈S
    rw [←List.getElem_eq_getD (h:=show j<S.length by omega)]
    exact List.getElem_mem _
  have ha := (C.entries a ma).2
  have hb := (C.entries b mb).2
  change commandOwner h a.1 a.2=o.val at ha
  change commandOwner h b.1 b.2=o.val at hb
  rw [show a.2=1 from centerK] at ha
  rw [show b.2=1 from otherK] at hb
  obtain ⟨center,_,un⟩ := unique_command_header h hh o.val o.property.1 o.property.2 1
  have ea := un ⟨a.1,centerH⟩ ha
  have eb := un ⟨b.1,(fixed b.1).symm.trans otherH⟩ hb
  exact (List.getD_inj (by omega) (by omega) C.nodup).mp
    (Prod.ext (congrArg Subtype.val (eb.trans ea.symm)) (otherK.trans centerK.symm))

open BStarLongLiteral BStarResetControllerEntry

private theorem busy_prefix_layout {base x : X} {addr : Nat→Pos n} {len op : Nat}
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

/-- Actual healthy launch and an outward trace to its own center force
a healthy selected offer on the real outgoing mark of the center. This
does not require future successful publication or sealed body state. -/
theorem selected_at_center {base start : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (door e : Fin n) (w : List (Fin n)) (l : Nat) (L : l<len)
    (addrCenter : S.getD l fall=(e,1))
    (center : oldH6 B base e=true)
    (op : (ctrlOp.read (start (S.getD 0 fall).1).long).toNat=commitOp)
    (launch : Launch (start (S.getD 0 fall).1).long ((step start door) (S.getD 0 fall).1).long)
    (T : BusyOnly hp base (fun j=>S.getD j fall) len commitOp (step start door) (.out 0) w (.out l)) :
    let y := play (step start door) w
    let g := oldPair B y e
    let raw := ((y e).long,(y (rightNeighbor e)).long)
    ∃ p, Well p ∧ (centerLink g,.advance p)∈actualOffers g raw := by
  let x := step start door
  let addr := fun j=>S.getD j fall
  obtain ⟨p,P,H⟩ := launched_well _ _ op launch
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
      have fixed := busy_prefix_layout hp T u (a::v) E
      have E' := unique_center_index hp C fixed l j (Nat.le_of_lt L) (by omega)
        (congrArg Prod.snd addrCenter) (by rwa [congrArg Prod.fst addrCenter]) (Fin.ext K) header
      omega
    · exact .inl K
  have R := before_center hp C sep T 0 l p rfl rfl L init H avoid
  let y := play x w
  let g := oldPair B y e
  let raw := ((y e).long,(y (rightNeighbor e)).long)
  have wire : readK raw (centerLink g).source=.forward p := by
    change atSite (y e).long 1=_
    change atCursor y (S.getD l fall)=_ at R
    rwa [addrCenter] at R
  exact ⟨p,H,selected_well g raw (centerLink g) p (center_mem g) (show Cmd.link≠Cmd.door by decide) H wire⟩

end L4.BStarCommitHealthyFlight
