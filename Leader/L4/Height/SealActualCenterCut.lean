import Leader.L4.Height.StageSealStay
import Leader.L4.Height.SealHealthyEntry
import Leader.L4.BStarSealHealthyIdle

namespace L4.Height.SealActualCenterCut
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongDoor BStarLongLayout BStarLongPublication BStarLongGrant
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch BStarResetMarkAdapter
open BStarLongFixedRouting BStarGeneratedOwner BStarOwnerLaunchOrigin BStarResetChartService
open BStarSealBitDescriptor BStarAcquireHistoryReturn
variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step
open BStarAcquireForwardTrace BStarSeparatingRail
open BStarSeparatingProgress BStarResetChartService BStarAcquireHistoryReturn BStarSealBitDescriptor BStarAcquireHistorySample

open BStarAcquireForwardTrace BStarSeparatingRail BStarLongLiteral BStarSealHealthyFlight
open BStarSealHealthyIdle

/-- At a real preterminal H6 K1 slot, a physical outward departure can only
occur on that center's own outgoing mark. This uses source silence on all
other marks, not a successful SEAL outcome. -/
theorem departure_label {base x : X} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (k : Nat) (K : k<len) {i e : Fin n} (loc : S.getD k fall=(i,1))
    (I : Current hp base (fun j=>S.getD j fall) len x (.busy sealOp (.out k)))
    (J : Current hp base (fun j=>S.getD j fall) len (step x e) (.busy sealOp (.out (k+1))))
    (pay : Payload) (W : BStarSealHealthyHop.Well pay)
    (old : project (fun j=>S.getD j fall) x k=.forward pay) : e=i := by
  by_cases ne : e=i
  · exact ne
  exfalso
  have no : ¬linkAt hp x e (fun j=>S.getD j fall) len k := by
    rintro ⟨_,c,a,mem,_,src,_⟩
    change S.getD k fall=address e c.source at src
    have tag : c.source.occurrence.val=1 :=
      congrArg (fun q : Pos n => q.2.val) (src.symm.trans loc)
    rw [center_of _ c mem tag] at src
    exact ne (congrArg Prod.fst (src.symm.trans loc))
  have same := (silent_at_seal hp C e (sep e) sealOp k I.1 pay
      I.2.1 old W no (fun E => (Nat.ne_of_lt K E).elim)).2
  have F : project (fun j=>S.getD j fall) (step x e) k=.forward pay := same.trans old
  have eq := (BStarOwnerControlHistory.pointed_unique_forward _ len (k+1) J.2.1 J.2.2 k (by omega)).mp ⟨pay,F⟩
  omega

open BStarSealHealthyHop BStarLongTransport BStarLongEvents BStarSeparatorControl BStarLongRouting BStarSeparatorQuiet BStarSealHealthyOffer BStarResetQuiet BStarClearanceSource

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

theorem forward_at_center {base start : X} {hh : ∃ i,oldH6 B base i=true}
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
    ∃ p, Well p ∧ project (fun j=>S.getD j fall) y l=.forward p ∧ (centerLink g,.advance p)∈actualOffers g raw ∧
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
  exact ⟨p,H,R,selected_well g raw (centerLink g) p (center_mem g) (show Cmd.link≠Cmd.door by decide) H wire,DD⟩

/-- The actual prefix reaching later PC2 necessarily contains the independently
identified first SEAL launch and selected center departure, even if its eventual
reply is unhealthy. The exact precenter BusyOnly tape is preserved. -/
theorem first_center_from409 {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X→Prop)
    (fiber : ∀ y,Q y→∀ j,Layout B base j=Layout B y j)
    (closed : ∀ y,Q y→∀ e,Q (step y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (k : Nat) (K : k<len) (loc : S.getD k fall=(i,1))
    (H : oldH6 B base i=true)
    {w : List (Fin n)} {m : Mode}
    (T : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle w m)
    (qx : Q x) (d : Descriptor)
    (pc : (ctrlOp.read (x (S.getD 0 fall).1).long).toNat=sealOp)
    (dd : BStarLongPublication.decode (sourceDescriptor.read (x (S.getD 0 fall).1).long)=some d)
    (later : (ctrlOp.read (play x w (S.getD 0 fall).1).long).toNat=2) :
    ∃ idle door pre tail,
      w=idle++door::(pre++i::tail) ∧
      (∀ f∈idle,f≠RearTrace.predecessor (S.getD 0 fall).1) ∧
      (let y := play x idle
       let z := step y door
       (ctrlOp.read (y (S.getD 0 fall).1).long).toNat=sealOp ∧
       BStarLongPublication.decode (sourceDescriptor.read (y (S.getD 0 fall).1).long)=some d ∧
       door=RearTrace.predecessor (S.getD 0 fall).1 ∧
       Launch (y (S.getD 0 fall).1).long (z (S.getD 0 fall).1).long ∧
       BusyOnly hp base (fun j=>S.getD j fall) len sealOp z (.out 0) pre (.out k) ∧
       Event hp (fun j=>S.getD j fall) len (play z pre) i
         (.busy sealOp (.out k)) (.busy sealOp (.out (k+1)))) := by
  obtain ⟨idle,door,after,W,foreign,P,D,O,L,G⟩ :=
    StageSealLaunchCut.first_seal_launch hp C Q fiber closed sep T qx d pc dd later
  have later' : (ctrlOp.read (play (step (play x idle) door) after (S.getD 0 fall).1).long).toNat=2 := by
    rw [W,BStarResetSchedule.run_append] at later
    exact later
  obtain ⟨all,ack,rest,A,busy,_⟩ := StageSealCursorCut.first_consume hp (by decide : 2≠sealOp) G later'
  obtain ⟨outward,t,back,V,B',_,_⟩ := BStarAcquireAckAncestry.split_turn hp busy
  obtain ⟨pre,e,post,J,F,E,tail⟩ := StageSealCursorCut.split_outward hp B' k (Nat.zero_le _) K
  obtain ⟨pay,well,old,_,_⟩ := forward_at_center hp C sep door i pre k K loc H P L F d D
  have label : e=i := departure_label hp C sep k K loc (busy_end hp F) (busy_start hp tail) pay well old
  subst e
  exact ⟨idle,door,pre,post++t::(back++ack::rest),by rw [W,A,V,J,List.append_assoc,List.cons_append,List.append_assoc,List.cons_append],
    foreign,P,D,O,L,F,E⟩

end L4.Height.SealActualCenterCut
