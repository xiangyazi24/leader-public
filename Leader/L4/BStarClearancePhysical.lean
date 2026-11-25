import Leader.L4.BStarClearanceSource
import Leader.L4.BStarClearanceForwardService
import Leader.L4.BStarClearanceRingDT
import Leader.L4.BStarClearanceLex
import Leader.L4.BStarClearanceSettled

namespace L4.BStarClearancePhysical
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarAcquireLiteralChain BStarAcquireVisitOrder BStarLongFiberOwner
open BStarH6WordChart hiding total
open BStarAcquireForwardTrace BStarLongFixedRouting BStarResetMarkAdapter
open BStarClearanceReturnCharge BStarClearanceIndexedSum BStarClearanceCommandSum
open BStarClearanceSource BStarResetChartTouch BStarClearanceRingDT
open BStarClearanceIndexedWait BStarClearanceOffset BStarClearanceLex BStarClearanceAggregate
open BStarClearanceReplyService BStarLongEvents

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B

/-- The single fixed chart is used in all four coordinates. In
particular the return distance is positive and increases away from the
door, whereas the forward distance decreases toward the terminal. -/
noncomputable def coord (base : X) (hh : ∃ i,oldH6 B base i=true)
    (o : Owners (oldH6 B base)) (S : List (Pos n)) (x : X) : Four :=
  ⟨total (physicalRank B base x (distance S)) S,
   BStarClearanceMobileRing.ringRank hp base hh x o.val,
   total (physicalDT x true (replyDistance S)) S,
   total (physicalDT x false (fun _ => 1)) S⟩

/-- Before source service every actual mark is weak for this owner's
entire lexicographic rank. No condition is imposed on other owners at
that mark. In particular their source doors may issue. -/
theorem before_weak {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (same : ∀ i, Layout B base i=Layout B x i)
    (cb : correct (oldH6 B base) hh 5 base) (cx : correct (oldH6 B base) hh 5 x)
    (e : Fin n) (he : e≠rightNeighbor e)
    (hold : Held (x (endpoint (oldH6 B base) hh o 0).1).long) :
    Weak (coord hp base hh o S (step x e)) (coord hp base hh o S x) := by
  have wait := held_before hp x _ e hold
  have F := pre_service_sum hp chart same cb cx e he wait
  have DT := indexed_DT hp chart same cb cx e he wait
  apply weak_of_conditional
  · exact F.1
  · intro tie
    change total (physicalRank B base (step x e) (distance S)) S=
      total (physicalRank B base x (distance S)) S at tie
    exact (BStarClearanceMobileRing.ring_compare hp base x hh same o.val e he (by
      intro C q H own
      exact Nat.lt_irrefl _ (tie ▸ F.2 ⟨C,q,H,own⟩))).1
  · intro ft _
    exact (DT ft).1
  · intro ft _ rt
    exact (DT ft).2 rt

#print axioms before_weak

open BStarAcquireAnchors BStarAcquireRailCoverage BStarLongTransport BStarClearanceChartFootprint

/-- The four-priority dispatch on arbitrary bytes at a held owner:
raw F, occupied active mobile, raw D, and finally a trail of an E/T
suffix. The chosen mark strictly decreases the entire owner rank. -/
theorem held_nominate {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (same : ∀ i, Layout B base i=Layout B x i)
    (cb : correct (oldH6 B base) hh 5 base) (cx : correct (oldH6 B base) hh 5 x)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true)
    (headx : ∀ i, let g := longGeometry B (x i); (!g.axes.h6 || g.inside)=true)
    (contx : ∀ i, let g := oldPair B x i; continuation g.1 g.2=true)
    (hold : Held (x (endpoint (oldH6 B base) hh o 0).1).long) :
    ∃ e, Falls (coord hp base hh o S (step x e)) (coord hp base hh o S x) := by
  classical
  have weak (e : Fin n) := before_weak hp chart same cb cx e (sep e) hold
  have wait (e : Fin n) := held_before hp x _ e hold
  let u := fun j => S.getD j fall
  have root := chart.root
  have zero : (u 0).2=0 := (BStarResetChartService.root_header hp chart same).2
  have t0 : atCursor x (u 0)=atSite (x (endpoint (oldH6 B base) hh o 0).1).long 0 := by
    change atSite (x (u 0).1).long (u 0).2=_
    rw [zero,show (u 0).1=(endpoint (oldH6 B base) hh o 0).1 from congrArg Prod.fst root]
  have mem (j : Nat) (J : j≤len) : u j∈S := by
    have L := chart.length
    change S.getD j fall∈S
    rw [←List.getElem_eq_getD (h:=show j<S.length by omega)]
    exact List.getElem_mem _
  by_cases F : ∃ j≤len, ∃ q, atCursor x (u j)=.forward q
  · obtain ⟨j,hj,q,F⟩ := F
    obtain ⟨e,P⟩ := BStarClearanceForwardService.nominate_held hp chart same cb cx sep
      head cont headx contx hold j hj ⟨q,F⟩
    exact ⟨e,falls_of_weak_ne (weak e) (P.elim (fun A => .inl (Nat.ne_of_lt A))
      (fun A => .inr (.inl (Nat.ne_of_lt A)) ))⟩
  have noF (j : Nat) (hj : j≤len) (q : Payload) : atCursor x (u j)≠.forward q :=
    fun E => F ⟨j,hj,q,E⟩
  by_cases M : 0 < (coord hp base hh o S x).mobile
  · obtain ⟨e,P⟩ := BStarClearanceMobileRing.rightmost_fixed hp base x hh same o.val sep
      headx contx ((BStarClearanceMobileRing.rank_positive hp base x hh o.val).mp M)
    rcases P with P|P
    · exact ⟨e,falls_of_weak_ne (weak e) (.inr (.inl (Nat.ne_of_lt P)))⟩
    · exact ⟨e,.inl ((pre_service_sum hp chart same cb cx e (sep e) (wait e)).2 P)⟩
  by_cases D : ∃ j≤len, ∃ q, atCursor x (u j)=.reply q
  · obtain ⟨j,hj,q,D⟩ := D
    cases j with
    | zero =>
      rw [t0] at D
      rcases hold.2.2 with T|⟨p,F⟩
      · rw [T] at D; contradiction
      · rw [F] at D; contradiction
    | succ j =>
      obtain ⟨e,C,a,p,P,U,_,_,_⟩ := nominate_reverse hp chart head cont same
        (show j<len by omega) q D (noF j (by omega))
      have J : address e C.source∈S := by rw [U]; exact mem j (by omega)
      have own : physicalOwner (oldH6 B base) e cmdDispl C.source=o.val :=
        (chart.entries (address e C.source) J).2
      refine ⟨e,falls_of_weak_ne (weak e) ?_⟩
      by_cases tie : (coord hp base hh o S (step x e)).forward=(coord hp base hh o S x).forward
      · have decrease := (indexed_DT_paying hp chart same cb cx e (sep e) (wait e) tie).2.1
          ⟨C,.reply p,P,own⟩
        exact .inr (.inr (.inl (Nat.ne_of_lt decrease)))
      · exact .inl tie
  have quiet (j : Nat) (hj : j≤len) :
      atCursor x (u j)=.empty ∨ atCursor x (u j)=.trail := by
    cases Z : atCursor x (u j) with
    | empty => exact .inl rfl
    | trail => exact .inr rfl
    | forward q => exact (noF j hj q Z).elim
    | reply q => exact (D ⟨j,hj,q,Z⟩).elim
  have start : atCursor x (u 0)=.trail := by
    rcases hold.2.2 with T|⟨p,P⟩
    · exact t0.trans T
    · exact (noF 0 (by omega) p (t0.trans P)).elim
  obtain ⟨e,C,K,⟨j,hj,U⟩,A⟩ := nominate_trail hp chart head cont same quiet ⟨0,by omega,start⟩
  have chosen : address e C.source∈S := by rw [←U]; exact mem j hj
  have rankPaid := trail_footprint_payment hp x e (sep e) C K A
  refine ⟨e,falls_of_weak_ne (weak e) ?_⟩
  by_cases ft : (coord hp base hh o S (step x e)).forward=(coord hp base hh o S x).forward
  · by_cases dt : (coord hp base hh o S (step x e)).reply=(coord hp base hh o S x).reply
    · have drop := ((indexed_DT_paying hp chart same cb cx e (sep e) (wait e) ft).2.2 dt).2
        ⟨C,K,chosen,rankPaid⟩
      exact .inr (.inr (.inr (Nat.ne_of_lt drop)))
    · exact .inr (.inr (.inl dt))
  · exact .inl ft

#print axioms held_nominate

/-- Access to the physical source from arbitrary long/controller bytes
over a closed lower layout. The already selected five-cover offset
repair can be prepended; no probability or schedule fairness is used. -/
theorem reach_nonheld {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true)
    (Q : X → Prop) (closed : ∀ y e, Q y → Q (step y e))
    (same : ∀ y, Q y → ∀ i, Layout B base i=Layout B y i)
    (heads : ∀ y, Q y → ∀ i, let g := longGeometry B (y i); (!g.axes.h6 || g.inside)=true)
    (conts : ∀ y, Q y → ∀ i, let g := oldPair B y i; continuation g.1 g.2=true)
    (cb : correct (oldH6 B base) hh 5 base) (I : Q x) (cx : correct (oldH6 B base) hh 5 x) :
    let root := (endpoint (oldH6 B base) hh o 0).1
    ∃ w, Q (BStarResetSchedule.run step x w) ∧
      correct (oldH6 B base) hh 5 (BStarResetSchedule.run step x w) ∧
      ¬ Held ((BStarResetSchedule.run step x w) root).long := by
  dsimp only
  let Ready : X → Prop := fun y => ¬Held (y (endpoint (oldH6 B base) hh o 0).1).long
  let Inv : X → Prop := fun y => Q y ∧ correct (oldH6 B base) hh 5 y
  have stepClosed (y : X) (e : Fin n) (J : Inv y) : Inv (step y e) :=
    BStarClearanceSettled.settled_step hp _ hh sep Q closed
      (fun z I i => (congrArg Prod.fst (same z I i)).symm) y e J
  obtain ⟨w,_,J,R⟩ := @nominated_ready_word X n (AllSizeS1Geometry.step B) Inv Ready
    (coord hp base hh o S) (fun y e I _ => stepClosed y e I)
    (fun y J R => by
      obtain ⟨e,E⟩ := held_nominate hp chart (same y J.1) cb J.2 sep
        head cont (heads y J.1) (conts y J.1) (Classical.not_not.mp R)
      exact ⟨e,.inr E⟩) x ⟨I,cx⟩
  exact ⟨w,J.1,J.2,R⟩

/-- Once the held-source rank has cleared, consume at most two repair
marks and then select an actual fresh launch. The output names the old
prefix and the independent incoming launch mark, never a byte match. -/
theorem reach_launch {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true)
    (Q : X → Prop) (closed : ∀ y e, Q y → Q (step y e))
    (same : ∀ y, Q y → ∀ i, Layout B base i=Layout B y i)
    (heads : ∀ y, Q y → ∀ i, let g := longGeometry B (y i); (!g.axes.h6 || g.inside)=true)
    (conts : ∀ y, Q y → ∀ i, let g := oldPair B y i; continuation g.1 g.2=true)
    (cb : correct (oldH6 B base) hh 5 base) (I : Q x) (cx : correct (oldH6 B base) hh 5 x) :
    let root := (endpoint (oldH6 B base) hh o 0).1
    let e := RearTrace.predecessor root
    ∃ u : List (Fin n), let z := BStarResetSchedule.run step x u
      Q z ∧ Q (step z e) ∧
      Launch (z root).long (step z e root).long := by
  dsimp only
  let root := (endpoint (oldH6 B base) hh o 0).1
  let e := RearTrace.predecessor root
  obtain ⟨w,J,_,R⟩ := reach_nonheld hp chart sep head cont Q closed same heads conts cb I cx
  let y := BStarResetSchedule.run step x w
  have H (z : X) (K : Q z) : oldH6 B z root=true := by
    have Hdr := (BStarResetChartService.root_header hp chart (same z K)).1
    have Y := congrArg Prod.fst chart.root
    change oldH6 B z (S.getD 0 fall).1=true at Hdr
    rwa [Y] at Hdr
  have J₁ := closed y e J
  have J₂ := closed (step y e) e J₁
  have T := nonheld_three hp root y sep R (H y J) ⟨H _ J₁,H _ J₂⟩
  rcases T with T|T|T
  · exact ⟨w,J,J₁,T⟩
  · refine ⟨w++[e],?_⟩
    rw [BStarResetSchedule.run_append]
    exact ⟨J₁,J₂,T⟩
  · refine ⟨w++[e,e],?_⟩
    rw [BStarResetSchedule.run_append]
    exact ⟨J₂,closed _ e J₂,T⟩

#print axioms reach_nonheld
#print axioms reach_launch
end L4.BStarClearancePhysical
