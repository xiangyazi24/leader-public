import Leader.L4.BStarResetReleaseHistory
import Leader.L4.BStarResetChartService
import Leader.L4.BStarResetQuietAdapter
import Leader.L4.BStarSeparatorControl

namespace L4.BStarResetIssueClean
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongDoor BStarLongTransport BStarLongEvents
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireLiteralChain
open BStarAcquireForwardTrace BStarLongFixedRouting BStarResetChartTouch BStarResetChartService
open BStarResetMarkAdapter BStarResetRailRing BStarResetSchedule
open BStarSeparatingRail BStarResetQuiet BStarResetQuietTable BStarResetIdleRing

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
variable (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "XX" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

private theorem address_inj (e : Fin n) (he : e≠rightNeighbor e)
    (a b : AtK) (E : address e a=address e b) : a=b := by
  rcases a with ⟨s,i⟩
  rcases b with ⟨t,j⟩
  have J := congrArg Prod.snd E
  change i=j at J
  subst j
  have H := congrArg Prod.fst E
  cases s <;> cases t <;> first | rfl | exact (he H).elim | exact (he H.symm).elim

/-- The whole empty suffix survives a single source issue mark from
a completely clean rail. The new forward root cannot move on that
old-pair mark: every selected link still reads two old E slots. -/
theorem suffix_empty_after_empty_root {base x : XX} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (C : Chart hp base hh o S len fallback)
    (same : ∀ i, Layout B base i=Layout B x i)
    (clean : ∀ j≤len, project (fun j => S.getD j fallback) x j=.empty)
    (e : Fin n) (he : e≠rightNeighbor e) :
    ∀ j, 0<j → j≤len →
      project (fun j => S.getD j fallback) (AllSizeS1Geometry.step B x e) j=.empty := by
  intro j hj hlen
  let addr := fun j => S.getD j fallback
  let U := project addr x
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have read (j : Nat) (a : AtK) (H : addr j=address e a) : readK raw a=U j :=
    (old_read x e a).trans ((congrArg (atCursor x) H).symm)
  have Eread (j : Nat) (a : AtK) (H : addr j=address e a) (hl : j≤len) :
      bound g (readK raw) a=.empty := by
    have E := (read j a H).trans (clean j hl)
    exact (quiet_bound g (readK raw) a (.inl E)).trans E
  have links (i : Nat) (Lh : linkAt hp x e addr len i) :
      ∃ (a b : AtK), addr i=address e a ∧ addr (i+1)=address e b ∧
        avoids a (middle g raw) ∧ avoids b (middle g raw) := by
    obtain ⟨hi,K,d,hK,hd,hs,ht⟩ := Lh
    have ht' := Eread (i+1) d ht (by omega)
    have H : LinkHold (bound g (readK raw) K.source) (bound g (readK raw) d) := by
      rw [Eread i K.source hs (by omega),ht']
      exact .ee
    exact ⟨K.source,d,hs,ht,link_avoids g raw K d hK
      (BStarAcquireReturn.link_shape g K d hK hd).2.1 hd H⟩
  have selected (a : AtK) (H : addr j=address e a) :
      project addr (AllSizeS1Geometry.step B x e) j=.empty := by
    have hn := not_discarded hp C same e j hlen a H
    have hR : ¬(a=R 0 ∧ g.2.axes.h6=true) := by
      rintro ⟨rfl,head⟩
      have hOld : oldH6 B base (rightNeighbor e)=true :=
        (congrArg Prod.fst (same (rightNeighbor e))).trans head
      have L := C.length
      have M : addr j∈S := by
        change S.getD j fallback∈S
        rw [←List.getElem_eq_getD (h:=show j<S.length by omega)]
        exact List.getElem_mem _
      have Own := (C.entries _ M).2
      rw [H] at Own
      have atRoot := (endpoint_spec _ hh o 0).2.2 (rightNeighbor e) hOld Own
      have eq : addr j=addr 0 := H.trans (atRoot.trans C.root.symm)
      have J := (List.getD_inj (by omega) (by omega) C.nodup).mp eq
      omega
    have safe : DoorSafe g raw a := by
      by_cases A : a=R 0
      · subst a
        refine ⟨fun _ hh => (hR ⟨rfl,hh⟩).elim,?_⟩
        intro _ cl k hcl _
        have eq := (BStarK0Frame.door_eq g raw cl k hcl).1
        have M : cl∈orderedCommands g := by
          rw [←actualOffers_claims g raw]
          exact List.mem_map.mpr ⟨(cl,.door k),hcl,rfl⟩
        have hh := (BStarResetChartIndex.selected_door g cl M (eq ▸ rfl)).2.1
        exact (hR ⟨rfl,hh⟩).elim
      · exact safe_nonright _ _ _ A
    have hm : avoids a (middle g raw) := by
      apply middle_avoids_of_chart
      intro v hv ha
      have mc : v.1∈orderedCommands g := by
        rw [←actualOffers_claims g raw]
        exact List.mem_map.mpr ⟨v,hv,rfl⟩
      have K := touches hp C same e j hlen v.1 a mc ha H
      have G : avoids a (middle g raw) := by
        rcases K with ⟨Z,_,_⟩|⟨J,T⟩|L|⟨i,I,L⟩
        · omega
        · subst j
          obtain ⟨K,M,hk,_,_,S⟩ := T
          have A := address_inj e he a K.source (H.symm.trans S)
          subst a
          exact terminal_avoids g raw K M hk (by rw [Eread len K.source H hlen]; exact .e)
        · obtain ⟨b,d,HB,_,hb,_⟩ := links j L
          exact (address_inj e he a b (H.symm.trans HB)).symm ▸ hb
        · obtain ⟨b,d,_,D,_,hd⟩ := links i L
          have eq : addr j=address e d := I ▸ D
          exact (address_inj e he a d (H.symm.trans eq)).symm ▸ hd
      intro w hw
      exact G w (List.mem_flatMap.mpr ⟨v,hv,hw⟩)
    have R := idle_at hp x e he a (.inl (.inl ((read j a H).trans (clean j hlen)))) hn hm safe
    exact (congrArg (atCursor (AllSizeS1Geometry.step B x e)) H).trans
      (R.trans ((congrArg (atCursor x) H).symm.trans (clean j hlen)))
  by_cases hl : (addr j).1=e
  · exact selected (L (addr j).2) (Prod.ext hl rfl)
  · by_cases hr : (addr j).1=rightNeighbor e
    · exact selected (R (addr j).2) (Prod.ext hr rfl)
    · exact (idle_off_pair hp x e (addr j) hl hr).trans (clean j hlen)


#print axioms suffix_empty_after_empty_root

open BStarResetHealthyService BStarSeparatingProgress BStarResetReleaseHistory

/-- Every old prefix of an actual clean-start reset has exactly the
tracked live token; outward prefixes have an empty suffix as well as
the Trail prefix, while returning prefixes already carry it in Good. -/
def CleanSuffix (len : Nat) (u : BStarSeparatingRail.Rail) : Cursor → Prop
  | .out k => ∀ j, k<j → j≤len → u j=.empty
  | .back _ => True

theorem clean_prefix {base x : XX} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (C : Chart hp base hh o S len fallback)
    (Q : XX → Prop) (fiber : ∀ x,Q x → ∀ i, Layout B base i=Layout B x i)
    (closed : ∀ x e,Q x → Q (AllSizeS1Geometry.step B x e))
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (op : Nat) (ho : op<3) (cur : Cursor)
    (init : Q x ∧ Waiting hp base (S.getD 0 fallback).1 op x)
    (G : Good (healthyTag op) len (project (fun j => S.getD j fallback) x) cur)
    (clean : CleanSuffix len (project (fun j => S.getD j fallback) x) cur)
    (pre tail : List (Fin n)) (e : Fin n)
    (T : Seen (AllSizeS1Geometry.step B) (project (fun j => S.getD j fallback))
      (healthyTag op) len x cur (pre++(e::tail)) (.back 0)) :
    let y := BStarResetSchedule.run (AllSizeS1Geometry.step B) x pre
    ∃ z, z≠.back 0 ∧ (Q y ∧ Waiting hp base (S.getD 0 fallback).1 op y) ∧
      Good (healthyTag op) len (project (fun j => S.getD j fallback) y) z ∧
      CleanSuffix len (project (fun j => S.getD j fallback) y) z := by
  induction pre generalizing x cur with
  | nil =>
    cases T with
    | cons l => exact ⟨cur,l,init,G,clean⟩
  | cons f pre ih =>
    cases T with
    | cons l _ A new rest =>
      rename_i dst mk
      let st := AllSizeS1Geometry.step (n:=n) B
      let adr := fun j => S.getD j fallback
      let y := st x f
      have qy : Q y := closed x f init.1
      have W := waiting_closed_at hp C f op ho (fiber _ qy) cur l
        (weak_good _ _ _ _ G) init.2
      let svc := healthyService hp C init.2.1 f (sep f) op ho cur l G init.2.2.1 init.2.2.2.1
      have clean' : CleanSuffix len (project adr y) dst := by
        cases A with
        | stay =>
          cases cur with
          | back => exact True.intro
          | out k => exact clean_outward_step svc (healthy_forward_ne_trail op _) k k (.inl rfl) G new clean
        | forward k =>
          exact clean_outward_step svc (healthy_forward_ne_trail op _) k (k+1) (.inr rfl) G new clean
        | turn | reverse => exact True.intro
      exact ih dst ⟨qy,W⟩ new clean' rest

#print axioms clean_prefix

open BStarResetCycle BStarResetTaggedRows

/-- On a literal stage from an all-E owner cut, every interior mark
before the old reply has a single healthy owner command; the
same old source remains WAIT. -/
theorem stage_clean_prefix {base x y : XX} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (C : Chart hp base hh o S len fallback)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : XX → Prop) (good : Q x)
    (fiber : ∀ x,Q x → ∀ i, Layout B base i=Layout B x i)
    (closed : ∀ x e,Q x → Q (AllSizeS1Geometry.step B x e))
    (op : Nat) (ho : op<3)
    (clean : ∀ j≤len, project (fun j => S.getD j fallback) x j=.empty)
    (w : List (Fin n))
    (st : BStarResetHealthyCycle.Stage hp (fun j => S.getD j fallback) len op x w y) :
    let adr := fun j => S.getD j fallback
    let root := (adr 0).1
    let door := RearTrace.predecessor root
    let nextMark := AllSizeS1Geometry.step (n:=n) B
    ∃ middle, w=door::(middle++[door]) ∧
      ∀ (pre tail : List (Fin n)) (e : Fin n), middle=pre++(e::tail) →
      let a := BStarResetSchedule.run nextMark (nextMark x door) pre
      ∃ z, z≠.back 0 ∧ (Q a ∧ Waiting hp base root op a) ∧
        Good (healthyTag op) len (project adr a) z ∧ CleanSuffix len (project adr a) z := by
  dsimp only
  obtain ⟨pre,W,_,P,O,seen,_⟩ := st
  let adr := fun j => S.getD j fallback
  let root := (adr 0).1
  let door := RearTrace.predecessor root
  let nextMark := AllSizeS1Geometry.step (n:=n) B
  let z := nextMark x door
  have d : rightNeighbor door=root := RearTrace.right_predecessor root
  obtain ⟨H,K⟩ := root_header hp C (fiber x good)
  have HH : oldH6 B x (rightNeighbor door)=true := by rw [d]; exact H
  have pp : (ctrlPhase.read (x (rightNeighbor door)).long).toNat=1 := by rw [d]; exact P
  have oo : (ctrlOp.read (x (rightNeighbor door)).long).toNat=op := by rw [d]; exact O
  have M := genuine_wait hp x door (sep door) op ho HH pp oo
  rw [d] at M
  have qz : Q z := closed x door good
  have Iz : Q z ∧ Waiting hp base root op z := ⟨qz,fiber z qz,M.2.1,M.2.2⟩
  have F : project adr z 0=.forward (resetPayload op) :=
    (congrArg (atCursor z) (show adr 0=(root,0) from Prod.ext rfl K)).trans M.1
  have G : Good (healthyTag op) len (project adr z) (.out 0) :=
    ⟨Nat.zero_le _,F,fun _ H => (Nat.not_lt_zero _ H).elim⟩
  have Cy : CleanSuffix len (project adr z) (.out 0) :=
    suffix_empty_after_empty_root hp C (fiber x good) clean door (sep door)
  refine ⟨pre,W,?_⟩
  intro before after e E
  rw [E] at seen
  exact clean_prefix hp C Q fiber closed sep op ho (.out 0) Iz G Cy before after e seen

#print axioms stage_clean_prefix

private theorem end_inv {Y : Type} {m : Nat} (nextMark : Y → Fin m → Y)
    (track : Y → BStarSeparatingRail.Rail) (tag : Tag) (len : Nat) (Inv : Y → Prop)
    (closed : ∀ x e z, Inv x → z≠.back 0 → Good tag len (track x) z → Inv (nextMark x e))
    {x : Y} {u v : Cursor} {w : List (Fin m)}
    (T : Seen nextMark track tag len x u w v) (I : Inv x) (G : Good tag len (track x) u) :
    Inv (BStarResetSchedule.run nextMark x w) ∧
      Good tag len (track (BStarResetSchedule.run nextMark x w)) v := by
  induction T with
  | nil => exact ⟨I,G⟩
  | cons l _ _ g _ ih =>
    exact ih (closed _ _ _ I l G) g

/-- A completed exact reset Stage, even with a dirty old suffix,
leaves its entire chart empty after the separate consumption. In
particular the actual RCLEAR Stage supplies the all-E entry of RREL. -/
theorem stage_endpoint_clean {base x y : XX} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (C : Chart hp base hh o S len fallback)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : XX → Prop) (good : Q x)
    (fiber : ∀ x,Q x → ∀ i, Layout B base i=Layout B x i)
    (closed : ∀ x e,Q x → Q (AllSizeS1Geometry.step B x e))
    (op : Nat) (ho : op<3) (w : List (Fin n))
    (st : BStarResetHealthyCycle.Stage hp (fun j => S.getD j fallback) len op x w y) :
    ∀ j≤len, project (fun j => S.getD j fallback) y j=.empty := by
  obtain ⟨mid,W,Y,P,O,seen,_⟩ := st
  let adr := fun j => S.getD j fallback
  let root := (adr 0).1
  let door := RearTrace.predecessor root
  let nextMark := AllSizeS1Geometry.step (n:=n) B
  let z := nextMark x door
  let Inv := fun x => Q x ∧ Waiting hp base root op x
  have d : rightNeighbor door=root := RearTrace.right_predecessor root
  obtain ⟨H,K⟩ := root_header hp C (fiber x good)
  have HH : oldH6 B x (rightNeighbor door)=true := by rw [d]; exact H
  have pp : (ctrlPhase.read (x (rightNeighbor door)).long).toNat=1 := by rw [d]; exact P
  have oo : (ctrlOp.read (x (rightNeighbor door)).long).toNat=op := by rw [d]; exact O
  have M := genuine_wait hp x door (sep door) op ho HH pp oo
  rw [d] at M
  have qz : Q z := closed x door good
  have Iz : Inv z := ⟨qz,fiber z qz,M.2.1,M.2.2⟩
  have F : project adr z 0=.forward (resetPayload op) :=
    (congrArg (atCursor z) (show adr 0=(root,0) from Prod.ext rfl K)).trans M.1
  have G : Good (healthyTag op) len (project adr z) (.out 0) :=
    ⟨Nat.zero_le _,F,fun _ H => (Nat.not_lt_zero _ H).elim⟩
  have keep (a : XX) (e : Fin n) (u : Cursor) (I : Inv a) (N : u≠.back 0)
      (G : Good (healthyTag op) len (project adr a) u) : Inv (nextMark a e) := by
    have v := closed a e I.1
    exact ⟨v,waiting_closed_at hp C e op ho (fiber _ v) u N (weak_good _ _ _ _ G) I.2⟩
  obtain ⟨I,GG⟩ := end_inv nextMark (project adr) (healthyTag op) len Inv keep seen Iz G
  have eff : Clean (project adr) (resetTag op) len (BStarResetSchedule.run nextMark z mid) :=
    ⟨weakD op _ GG.2.1,GG.2.2.2⟩
  have A := (BStarResetConsumedClean.consumed_clean hp C op ho I.2 eff sep).1
  have X : w=door::(mid++[door]) := W
  rw [Y,X]
  change ∀ j≤len, project adr (BStarResetSchedule.run nextMark z (mid++[door])) j=.empty
  rw [BStarResetSchedule.run_append]
  exact A

#print axioms stage_endpoint_clean
end L4.BStarResetIssueClean
