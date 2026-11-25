import Leader.L4.BStarResetReleaseAuthority
import Leader.L4.BStarResetHealthyService
import Leader.L4.BStarResetHealthyCycle

namespace L4.BStarResetReleaseHistory
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarResetChartTouch BStarLongFixedRouting BStarResetMarkAdapter
open BStarSeparatingRail BStarSeparatingProgress BStarResetHealthyService BStarResetSchedule
open BStarResetReleaseAuthority BStarResetTaggedRows BStarLongDoor

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
variable (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B

/-- Invert the literal transition, not the arbitrary Mark witness
in Seen. If a healthy outward cursor advanced, the real selected
link had to be present at exactly the old tracked slot. -/
theorem forward_literal {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (C : Chart hp base hh o S len fallback)
    (same : ∀ i,Layout B base i=Layout B x i) (e : Fin n) (he : e≠rightNeighbor e)
    (op k : Nat) (ho : op<3)
    (old : Good (healthyTag op) len (project (fun j => S.getD j fallback) x) (.out k))
    (new : Good (healthyTag op) len (project (fun j => S.getD j fallback) (step x e)) (.out (k+1)))
    (wv : LongDoorGuard.valid manifest (x (S.getD 0 fallback).1).long=true)
    (wp : (ctrlPhase.read (x (S.getD 0 fallback).1).long).toNat=2) :
    linkAt hp x e (fun j => S.getD j fallback) len k := by
  let addr := fun j => S.getD j fallback
  let T := healthyService hp C same e he op ho (.out k) (by intro E; contradiction) old wv wp
  have L : T.mark.link k ↔ linkAt hp x e addr len k := Iff.rfl
  have H : k+1≤len := new.1
  apply L.mp
  apply Classical.byContradiction
  intro outer
  have F : (healthyTag op).F (project addr (step x e) k) := by
    by_cases incoming : ∃ j, j+1=k ∧ T.mark.link j
    · obtain ⟨j,E,J⟩ := incoming
      have A := (T.mark.tf j J (old.2.2 _ (by omega)) (by rw [E]; exact old.2.1)).2
      rwa [E] at A
    · exact (T.mark.idle k old.1 outer (fun j E J => incoming ⟨j,E,J⟩)
        (fun E _ => False.elim (by omega))).2.2.1 old.2.1
  change project addr (step x e) k=.forward (resetPayload op) at F
  have G := new.2.2 k (by omega)
  change project addr (step x e) k=.trail at G
  rw [G] at F
  contradiction

/-- Every structural forward move of a healthy RREL observation is
a literal selecting event for the still-old tracked reset token. -/
theorem rrel_forward_service {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (C : Chart hp base hh o S len fallback)
    (same : ∀ i,Layout B base i=Layout B x i) (e : Fin n) (he : e≠rightNeighbor e)
    (k : Nat)
    (old : Good (healthyTag 2) len (project (fun j => S.getD j fallback) x) (.out k))
    (new : Good (healthyTag 2) len (project (fun j => S.getD j fallback) (step x e)) (.out (k+1)))
    (wv : LongDoorGuard.valid manifest (x (S.getD 0 fallback).1).long=true)
    (wp : (ctrlPhase.read (x (S.getD 0 fallback).1).long).toNat=2) :
    serviceAt hp x e (S.getD k fallback) := by
  obtain ⟨_,c,d,hc,hd,src,_⟩ := forward_literal hp C same e he 2 k (by decide) old new wv wp
  have shape := BStarAcquireReturn.link_shape _ c d hc hd
  exact ⟨c,hc,by rw [shape.2.1]; decide,src,old.2.1⟩

#print axioms forward_literal
#print axioms rrel_forward_service

/-- Any completed outward/back trace must cross every forward index
below the terminal. Old/post states are from the same physical prefix. -/
theorem crossing {Y : Type} {m : Nat} (nextMark : Y → Fin m → Y)
    (track : Y → BStarSeparatingRail.Rail) (tag : Tag) (len : Nat)
    (Inv : Y → Prop)
    (closed : ∀ x e c, Inv x → c≠.back 0 → Good tag len (track x) c → Inv (nextMark x e))
    (x : Y) (w : List (Fin m)) (k j : Nat)
    (start : k≤j) (hj : j<len) (I : Inv x)
    (G : Good tag len (track x) (.out k))
    (H : Seen nextMark track tag len x (.out k) w (.back 0)) :
    ∃ pre e tail, w=pre++(e::tail) ∧
      Inv (BStarResetSchedule.run nextMark x pre) ∧
      Good tag len (track (BStarResetSchedule.run nextMark x pre)) (.out j) ∧
      Good tag len (track (nextMark (BStarResetSchedule.run nextMark x pre) e)) (.out (j+1)) := by
  induction w generalizing x k with
  | nil => cases H
  | cons e w ih =>
    cases H with
    | cons live _ A next tail =>
      have I' := closed x e (.out k) I live G
      cases A with
      | stay =>
        obtain ⟨pre,f,tail',eq,IG,GF,GG⟩ := ih (nextMark x e) k start I' next tail
        exact ⟨e::pre,f,tail',congrArg (List.cons e) eq,IG,GF,GG⟩
      | forward =>
        by_cases Q : k=j
        · subst k
          exact ⟨[],e,w,rfl,I,G,next⟩
        · obtain ⟨pre,f,tail',eq,IG,GF,GG⟩ := ih (nextMark x e) (k+1) (by omega) I' next tail
          exact ⟨e::pre,f,tail',congrArg (List.cons e) eq,IG,GF,GG⟩
      | turn => omega

/-- A completed healthy RREL observation on actual marks has a real
release event at every outbound index of that same physical history. -/
theorem completed_services {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (C : Chart hp base hh o S len fallback)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Inv : X → Prop)
    (closed : ∀ x e c, Inv x → c≠.back 0 →
      Good (healthyTag 2) len (project (fun j => S.getD j fallback) x) c → Inv (step x e))
    (facts : ∀ x, Inv x →
      (∀ i,Layout B base i=Layout B x i) ∧
      LongDoorGuard.valid manifest (x (S.getD 0 fallback).1).long=true ∧
      (ctrlPhase.read (x (S.getD 0 fallback).1).long).toNat=2)
    (init : Inv x)
    (G : Good (healthyTag 2) len (project (fun j => S.getD j fallback) x) (.out 0))
    (w : List (Fin n))
    (T : Seen step (project (fun j => S.getD j fallback)) (healthyTag 2) len x (.out 0) w (.back 0))
    (j : Nat) (hj : j<len) :
    ∃ pre e tail, w=pre++(e::tail) ∧ serviceAt hp (BStarResetSchedule.run step x pre) e (S.getD j fallback) := by
  obtain ⟨pre,e,tail,W,I,G',Y⟩ := crossing step (project (fun j => S.getD j fallback)) _
    len Inv closed x w 0 j (Nat.zero_le _) hj init G T
  obtain ⟨layout,v,p⟩ := facts _ I
  exact ⟨pre,e,tail,W,rrel_forward_service hp C layout e (sep e) j G' Y v p⟩

#print axioms completed_services

/-- Every hardwired reader/writer incidence of the chart owner is
physically cleared at a mark in this very healthy RREL history. -/
theorem incidence_release {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (C : Chart hp base hh o S len fallback)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Inv : X → Prop)
    (closed : ∀ x e c, Inv x → c≠.back 0 →
      Good (healthyTag 2) len (project (fun j => S.getD j fallback) x) c → Inv (step x e))
    (facts : ∀ x, Inv x →
      (∀ i,Layout B base i=Layout B x i) ∧
      LongDoorGuard.valid manifest (x (S.getD 0 fallback).1).long=true ∧
      (ctrlPhase.read (x (S.getD 0 fallback).1).long).toNat=2)
    (init : Inv x)
    (G : Good (healthyTag 2) len (project (fun j => S.getD j fallback) x) (.out 0))
    (w : List (Fin n)) (T : Seen step (project (fun j => S.getD j fallback))
      (healthyTag 2) len x (.out 0) w (.back 0))
    (i : Fin n) (j : Fin 3)
    (own : BStarAcquireAnchors.commandOwner (oldH6 B base) i ⟨j.val,by omega⟩=o.val) :
    ∃ pre e tail, w=pre++(e::tail) ∧
      (BStarLongLayout.grant j).read ((step (BStarResetSchedule.run step x pre) e) i).long=0 := by
  let k : Fin 11 := ⟨j.val,by omega⟩
  have a : BStarAcquireRailCoverage.active (longGeometry B (base i)) k=true := by
    change (((j.val != 8) && (j.val != 9)) || (longGeometry B (base i)).inside)=true
    have J := j.isLt
    have a : j.val≠8 := by omega
    have b : j.val≠9 := by omega
    simp [a,b]
  have M := C.cover (i,k) a own
  obtain ⟨t,ht,E⟩ := List.mem_iff_getElem.mp M
  have eq : S.getD t fallback=(i,k) := (List.getElem_eq_getD _).symm.trans E
  have L := C.length
  have small : t<len := by
    by_cases Z : t=len
    · have Q := congrArg (fun v : Pos n => v.2.val) (eq.symm.trans (Z ▸ C.terminal))
      change j.val=10 at Q
      have J := j.isLt
      omega
    · omega
  obtain ⟨pre,e,tail,W,H⟩ := completed_services hp C sep Inv closed facts init G w T t small
  rw [eq] at H
  exact ⟨pre,e,tail,W,service_zero hp _ e (sep e) (i,k) j rfl H⟩

#print axioms incidence_release

open BStarResetChartService BStarResetCycle

/-- A stage witness supplies the real old issue, its live controller
invariant and the same marked release cuts. The first and final
door services remain distinct marks. -/
theorem stage_release {base x y : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (C : Chart hp base hh o S len fallback)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X → Prop) (good : Q x)
    (fiber : ∀ x, Q x → ∀ i, Layout B base i=Layout B x i)
    (closed : ∀ x e, Q x → Q (step x e))
    (w : List (Fin n))
    (st : BStarResetHealthyCycle.Stage hp (fun j => S.getD j fallback) len 2 x w y)
    (i : Fin n) (j : Fin 3)
    (own : BStarAcquireAnchors.commandOwner (oldH6 B base) i ⟨j.val,by omega⟩=o.val) :
    ∃ pre e tail, w=pre++(e::tail) ∧
      (BStarLongLayout.grant j).read ((step (BStarResetSchedule.run step x pre) e) i).long=0 := by
  obtain ⟨w',W,_,P,O,seen,_⟩ := st
  let root := (S.getD 0 fallback).1
  let door := RearTrace.predecessor root
  let z := step x door
  let adr := fun j => S.getD j fallback
  let Inv := fun x => Q x ∧ Waiting hp base root 2 x
  have d : rightNeighbor door=root := RearTrace.right_predecessor root
  obtain ⟨H,K⟩ := root_header hp C (fiber x good)
  have HH : oldH6 B x (rightNeighbor door)=true := by rw [d]; exact H
  have pp : (ctrlPhase.read (x (rightNeighbor door)).long).toNat=1 := by rw [d]; exact P
  have oo : (ctrlOp.read (x (rightNeighbor door)).long).toNat=2 := by rw [d]; exact O
  have M := genuine_wait hp x door (sep door) 2 (by decide) HH pp oo
  rw [d] at M
  have qz : Q z := closed x door good
  have Iz : Inv z := ⟨qz,fiber z qz,M.2.1,M.2.2⟩
  have F : project adr z 0=.forward (resetPayload 2) :=
    (congrArg (BStarAcquireForwardTrace.atCursor z) (show adr 0=(root,0) from Prod.ext rfl K)).trans M.1
  have G : Good (healthyTag 2) len (project adr z) (.out 0) :=
    ⟨Nat.zero_le _,F,fun _ H => (Nat.not_lt_zero _ H).elim⟩
  have keep (a : X) (e : Fin n) (u : Cursor) (I : Inv a) (N : u≠.back 0)
      (G : Good (healthyTag 2) len (project adr a) u) : Inv (step a e) := by
    have v := closed a e I.1
    exact ⟨v,waiting_closed_at hp C e 2 (by decide) (fiber _ v) u N (weak_good _ _ _ _ G) I.2⟩
  have facts (a : X) (I : Inv a) :
      (∀ i, Layout B base i=Layout B a i) ∧
      LongDoorGuard.valid manifest (a root).long=true ∧
      (ctrlPhase.read (a root).long).toNat=2 :=
    ⟨I.2.1,I.2.2.1,I.2.2.2.1⟩
  obtain ⟨pre,e,tail,T,A⟩ := incidence_release hp C sep Inv keep facts Iz G w' seen i j own
  refine ⟨door::pre,e,tail++[door],?_,A⟩
  rw [W,T]
  simp only [List.cons_append,List.append_assoc,door,root]

#print axioms stage_release

/-- Under actual service a clean outward suffix remains clean. For
a parked front the current link cannot have serviced that front;
for a moving front the newly occupied destination is excluded
from the suffix. No cleanliness is inferred from Good alone. -/
theorem clean_outward_step {tag : Tag} {len : Nat} {u v : BStarSeparatingRail.Rail}
    (s : Service tag len u v)
    (distinct : ∀ i, ¬ (tag.F (v i) ∧ v i=.trail))
    (k l : Nat) (K : l=k ∨ l=k+1)
    (old : Good tag len u (.out k)) (new : Good tag len v (.out l))
    (clean : ∀ j, k<j → j≤len → u j=.empty) :
    ∀ j, l<j → j≤len → v j=.empty := by
  have rank : k≤l := by omega
  intro j H J
  by_cases O : s.mark.link j
  · exact (s.mark.ee j O (clean j (by omega) J)
      (clean _ (by omega) (s.mark.bound j O))).1
  · by_cases I : ∃ i, i+1=j ∧ s.mark.link i
    · obtain ⟨i,E,L⟩ := I
      have notK : i≠k := by
        intro eq
        subst i
        have lK : l=k := by omega
        subst l
        exact distinct k ⟨new.2.1,(s.forced _ L old.2.1).1⟩
      have R := (s.mark.ee i L (clean i (by omega) (by omega))
        (clean (i+1) (by omega) (by omega))).2
      rwa [E] at R
    · by_cases T : j=len ∧ s.mark.terminal
      · obtain ⟨rfl,E⟩ := T
        exact s.mark.termE E (clean _ (by omega) (Nat.le_refl _))
      · exact (s.mark.idle j J O (fun i E L => I ⟨i,E,L⟩)
          (fun eq P => T ⟨eq,P⟩)).2.1 (clean _ (by omega) J)

theorem healthy_forward_ne_trail (op : Nat) (v : BStarSeparatingRail.Rail) :
    ∀ i, ¬ ((healthyTag op).F (v i) ∧ v i=.trail) := by
  rintro i ⟨A,T⟩
  change v i = .forward (resetPayload op) at A
  rw [T] at A
  contradiction

#print axioms clean_outward_step
end L4.BStarResetReleaseHistory
