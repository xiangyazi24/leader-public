import Leader.L4.WindowA0GapOne
import Leader.L4.WindowA0GapOneWord
import Leader.L4.WindowA0ApproachOwned

namespace L4.WindowA0GapOneTrace
open FixedResidual WindowA0ReleaseCredit WindowA0GapOne

structure FrameAt {p c n : Nat} (z0 : Config p c n) (S : WindowA0Ledger.Scope n)
    (i : Fin n) (q : Trip (2*c)) (k : Fin 3) (x : WindowA0Ledger.State p c n) : Prop where
  live : WindowA0Ledger.Live z0 S x
  iSlot_eq : x.iSlot=ask i 0
  jSlot_eq : x.jSlot=i
  empty : (x.ledger.config i).stock=false
  rail : (x.ledger.config i).rail=if k.val=0 then outward q else inward q
  waiting : (x.ledger.config (rightNeighbor i)).source=waitingFor q

structure DoorResult {p c n : Nat} (i : Fin n) (q : Trip (2*c))
    (y : WindowA0Ledger.State p c n) : Prop where
  top : rightNeighbor y.iSlot=i
  left : (y.ledger.config i).rail=(serviceDoor (waitingFor q) (inward q)).left
  source : (y.ledger.config (rightNeighbor i)).source=
    (if (serviceDoor (waitingFor q) (inward q)).fire then .off
      else (serviceDoor (waitingFor q) (inward q)).source)
  leader : (y.ledger.config (rightNeighbor i)).leader=(serviceDoor (waitingFor q) (inward q)).fire

private theorem stay_slots {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (x : WindowA0Ledger.State p c n) (e : Fin n)
    (hr : x.reason=none) (hNo : ¬ WindowA0Ledger.done (WindowA0Ledger.next S x e))
    (hi : e≠x.iSlot) (hj : e≠x.jSlot) :
    (WindowA0Ledger.next S x e).iSlot=x.iSlot ∧
      (WindowA0Ledger.next S x e).jSlot=x.jSlot := by
  have hkeep := Classical.byContradiction (fun h =>
    hNo ((WindowA0Ledger.physical_exit_iff S x e hr).mpr h))
  simp [WindowA0Ledger.next,hr,hkeep,WindowFourHeadTrace.landing,WindowFourHeadTrace.moves,hi,hj]

private theorem agree_sockets {p c n : Nat} (hn : 4≤n) (i : Fin n)
    (x y : Config p c n) (H : WindowA0Release.Agree (farLeft i) x y) :
    x i=y i ∧ x (rightNeighbor i)=y (rightNeighbor i) := by
  have hi := (two_labels hn i).2
  change i=liftedSite (farLeft i) 2 at hi
  refine ⟨?_,?_⟩
  · rw [hi]; exact H 2 (by decide) (by decide)
  · have hj : rightNeighbor i=liftedSite (farLeft i) 3 := by
      calc
        _ = rightNeighbor (liftedSite (farLeft i) 2) := congrArg rightNeighbor hi
        _ = _ := (liftedSite_succ _ 2).symm
    rw [hj]; exact H 3 (by decide) (by decide)

theorem one_mark {p c n : Nat} {z0 : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (i : Fin n) (q : Trip (2*c))
    (x : WindowA0Ledger.State p c n) (k : Fin 3) (e : Fin n)
    (hk : k.val≤1) (H : FrameAt z0 S i q k x) :
    let y := next S i (x,.waiting k) e
    (y.2=.success ∧ (WindowA0Ledger.done y.1 ∨ DoorResult i q y.1)) ∨
      y.2=.failed ∨
      ∃ k', k'.val≤1 ∧ y.2=.waiting k' ∧ FrameAt z0 S i q k' y.1 := by
  let y := WindowA0Ledger.next S x e
  rcases H.live with ⟨hv,hr,htI,htJ,_,hgi,hgj⟩
  have hright : rightNeighbor x.iSlot=i := by
    rw [H.iSlot_eq,show ask i 0=GGStage.incoming i 0 from rfl,
      GGStage.incoming_right,liftedSite_zero]
  rw [hright] at hgi
  rw [H.jSlot_eq] at hgj htJ
  by_cases hs : y.reason.isSome=true
  · exact .inl ⟨by simp [next,y,hs], .inl hs⟩
  have hNo : ¬ WindowA0Ledger.done y := hs
  have hy := (WindowA0Ledger.live_or_terminal hn S x e H.live).resolve_left hNo
  by_cases he : e=ask i k
  · subst e
    by_cases h0 : k.val=0
    · have keq : k=0 := Fin.ext h0
      subst k
      have H1 := first_request_authenticates hn S x i q H.iSlot_eq H.jSlot_eq hr
        hv.markCover hv.sourceCover hv.covers htI (H.jSlot_eq ▸ htJ)
        hgi H.empty H.rail (H.iSlot_eq.symm ▸ hNo)
      have H1' : y.iSlot=x.iSlot ∧ y.jSlot=x.jSlot ∧
          (y.ledger.config i).leader=false ∧ (y.ledger.config i).mark=true ∧
          (y.ledger.config i).stock=false ∧ (y.ledger.config i).rail=inward q ∧
          y.ledger.config (rightNeighbor i)=x.ledger.config (rightNeighbor i) := by
        simpa only [y,H.iSlot_eq] using H1
      exact .inr (.inr ⟨1,by decide,by simp [next,y,hs],⟨hy,
        H1'.1.trans H.iSlot_eq,H1'.2.1.trans H.jSlot_eq,H1'.2.2.2.2.1,
        H1'.2.2.2.2.2.1,H1'.2.2.2.2.2.2 ▸ H.waiting⟩⟩)
    · have hi : ask i k=i := by simp [ask,h0]
      have hm : (x.ledger.config i).mark=true := by simpa [htJ] using (hv.covers i).symm
      have H2 := second_request_authenticates hn S x i q hr hv.markCover hv.sourceCover
        htJ hm hgi hgj H.empty (by simpa [h0] using H.rail) H.waiting
      have H2' : DoorResult i q y := by
        rw [show y=WindowA0Ledger.next S x i by simp [y,hi]]
        refine ⟨?_,H2.1,H2.2.1,H2.2.2.1⟩
        have hkeep : WindowA0Route.routeTwo S.group S.iTag S.jTag x.ledger i=.keep := by
          apply Classical.byContradiction
          intro h
          exact hNo (by change WindowA0Ledger.done (WindowA0Ledger.next S x (ask i k)); rw [hi]; exact (WindowA0Ledger.physical_exit_iff S x i hr).mpr h)
        have hne : i≠x.iSlot := by
          intro heq
          have H' : liftedSite i 1=liftedSite i 0 := by
            simpa only [liftedSite_succ,liftedSite_zero] using (congrArg rightNeighbor heq).trans hright
          have := liftedSite_inj i (show 1<n by omega) (show 0<n by omega) H'
          omega
        have eq : (WindowA0Ledger.next S x i).iSlot=x.iSlot := by
          simp [WindowA0Ledger.next,hr,hkeep,WindowFourHeadTrace.landing,WindowFourHeadTrace.moves,hne]
        rwa [eq]
      exact .inl ⟨by simp [next,y,hs,h0],.inr H2'⟩
  · by_cases hb : e ∈ labelsAt i
    · exact .inr (.inl (by simp [next,y,hs,he,hb]))
    · have hi : e≠x.iSlot := fun h => hb (h ▸ H.iSlot_eq ▸ ask_mem hn i 0)
      have hj : e≠x.jSlot := fun h => hb ((h.trans H.jSlot_eq).symm ▸ (script_labels_mem hn i).2.1)
      have hh := stay_slots S x e hr hNo hi hj
      have fr := agree_sockets hn i y.ledger.config x.ledger.config
        (off_guard_frame S i (x,.waiting k) e hb)
      exact .inr (.inr ⟨k,hk,by simp [next,y,hs,he,hb],⟨hy,
        hh.1.trans H.iSlot_eq,hh.2.trans H.jSlot_eq,by change (y.ledger.config i).stock=false; rw [fr.1]; exact H.empty,
        by change (y.ledger.config i).rail=_; rw [fr.1]; exact H.rail,by change (y.ledger.config (rightNeighbor i)).source=_; rw [fr.2]; exact H.waiting⟩⟩)

/-- Read the original word, stopping at the first terminal of the monitor.
The returned count is the length of the consumed prefix. -/
def firstStop {p c n : Nat} (S : WindowA0Ledger.Scope n) (i : Fin n) :
    WindowA0GapOne.State p c n → List (Fin n) → Nat × WindowA0GapOne.State p c n
  | z, [] => (0,z)
  | z, e::es => match z.2 with
    | .waiting _ => let r := firstStop S i (next S i z e) es; (r.1+1,r.2)
    | _ => (0,z)

theorem firstStop_projection {p c n : Nat} (S : WindowA0Ledger.Scope n) (i : Fin n)
    (w : List (Fin n)) (z : WindowA0GapOne.State p c n) :
    let r := firstStop S i z w
    r.1≤w.length ∧ r.2.1=(w.take r.1).foldl (WindowA0Ledger.next S) z.1 := by
  induction w generalizing z with
  | nil => simp [firstStop]
  | cons e es ih =>
    cases h : z.2 with
    | success => simp [firstStop,h]
    | failed => simp [firstStop,h]
    | waiting k =>
      have H := ih (next S i z e)
      simpa only [firstStop,h,List.length_cons,List.take_succ_cons,List.foldl_cons] using
        And.intro (Nat.succ_le_succ H.1) (show _ = (es.take (firstStop S i (next S i z e) es).1).foldl (WindowA0Ledger.next S) (WindowA0Ledger.next S z.1 e) from H.2)

/-- Successful first stop authenticates an official exit or the literal
second request, on the actual raw prefix, not at a later padded state. -/
theorem firstStop_authenticates {p c n : Nat} {z0 : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (i : Fin n) (q : Trip (2*c))
    (w : List (Fin n)) (x : WindowA0Ledger.State p c n) (k : Fin 3)
    (hk : k.val≤1) (H : FrameAt z0 S i q k x) :
    let r := firstStop S i (x,.waiting k) w
    r.2.2=.success →
      WindowA0Ledger.done ((w.take r.1).foldl (WindowA0Ledger.next S) x) ∨
        DoorResult i q ((w.take r.1).foldl (WindowA0Ledger.next S) x) := by
  intro r hs
  rw [←(firstStop_projection S i w (x,.waiting k)).2]
  change WindowA0Ledger.done r.2.1 ∨ DoorResult i q r.2.1
  subst r
  revert hk H hs
  induction w generalizing x k with
  | nil =>
    intro _ _ hs
    change Phase.waiting k = .success at hs
    cases hs
  | cons e es ih =>
    intro hk H hs
    let y := next S i (x,.waiting k) e
    change (firstStop S i y es).2.2=.success at hs
    change WindowA0Ledger.done (firstStop S i y es).2.1 ∨ DoorResult i q (firstStop S i y es).2.1
    rcases one_mark hn S i q x k e hk H with ⟨hy,hR⟩ | hy | ⟨k',hk',hy,H'⟩
    · change y.2=.success at hy
      change WindowA0Ledger.done y.1 ∨ DoorResult i q y.1 at hR
      cases es <;> simpa [firstStop,hy] using hR
    · change y.2=.failed at hy
      cases es <;> simp [firstStop,hy] at hs
    · have hy' : y=(y.1,.waiting k') := Prod.ext rfl hy
      rw [hy'] at hs ⊢
      exact ih y.1 k' hk' H' hs

#print axioms one_mark
#print axioms firstStop_authenticates


open WindowFiveStages RootedAssembly

theorem approached_frame {p c n : Nat} {z0 : Config p c n}
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat)
    (z : WindowA0ClosedEntry.State p c n) (q : Trip (2*c))
    (ha : WindowA0ClosedEntry.Admitted z0 S J H z)
    (hn : ¬ WindowA0Ledger.done z.tag) (hg : z.gap=1)
    (hw : WindowA0ApproachOwned.Physical J q z 0) :
    FrameAt z0 S (rightNeighbor z.tag.iSlot) q 0 z.tag := by
  obtain ⟨hcut,hLive,hJ⟩ := ha.resolve_left hn
  have htop : rightNeighbor (rightNeighbor z.tag.iSlot)=J := by
    simpa [WindowA0IH.target,WindowA0ClosedEntry.cut,hg,liftedSite_succ,liftedSite_zero] using hcut.fixedRight
  refine ⟨hLive,?_,FreshSeparation.succ_inj (hJ.trans htop.symm),?_,?_,?_⟩
  · apply FreshSeparation.succ_inj
    rw [show ask (rightNeighbor z.tag.iSlot) 0=GGStage.incoming (rightNeighbor z.tag.iSlot) 0 from rfl,
      GGStage.incoming_right,liftedSite_zero]
  · simpa [WindowA0ClosedEntry.cut,liftedSite_zero] using hcut.empty 0 (by simp [WindowA0ClosedEntry.cut,hg])
  · simpa [WindowA0ApproachOwned.rails,WindowA0ClosedEntry.cut,liftedSite_zero] using hw.2.worker
  · rw [htop]; exact hw.1

private theorem snoc_ind {α : Type} (P : List α → Prop) (h0 : P [])
    (hs : ∀ u e, P u → P (u ++ [e])) (w : List α) : P w := by
  have aux : ∀ v : List α, P v.reverse := by
    intro v
    induction v with
    | nil => exact h0
    | cons e u ih => rw [List.reverse_cons]; exact hs _ _ ih
  simpa using aux w.reverse

theorem clean_word {p c n : Nat} {z0 : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (i : Fin n) (q : Trip (2*c))
    (x : WindowA0Ledger.State p c n) (H : FrameAt z0 S i q 0 x)
    (w : Word n) (hc : Clean (fun v => WindowA0GapOneWord.stopped
      (WindowA0GapOneWord.observe S i x v)) w) :
    let y := WindowA0GapOneWord.observe S i x w
    (y.2=.success ∧ (WindowA0Ledger.done y.1 ∨ DoorResult i q y.1)) ∨
      y.2=.failed ∨
      ∃ k : Fin 3, k.val≤1 ∧ y.2=.waiting k ∧ FrameAt z0 S i q k y.1 := by
  induction w using snoc_ind with
  | h0 => exact .inr (.inr ⟨0,by decide,rfl,H⟩)
  | hs u e ih =>
    change Clean _ (wordNext u e) at hc
    obtain ⟨hu,hNot⟩ := (clean_child _ u e).mp hc
    change let y := WindowA0GapOneWord.observe S i x (wordNext u e);
      (y.2=.success ∧ (WindowA0Ledger.done y.1 ∨ DoorResult i q y.1)) ∨ y.2=.failed ∨
      ∃ k : Fin 3, k.val≤1 ∧ y.2=.waiting k ∧ FrameAt z0 S i q k y.1
    let y := WindowA0GapOneWord.observe S i x u
    rw [WindowA0GapOneWord.observe_step]
    rcases ih hu with ⟨h,_⟩ | h | ⟨k,hk,h,F⟩
    · exact (hNot (by simp [WindowA0GapOneWord.stopped,done,h])).elim
    · exact (hNot (by simp [WindowA0GapOneWord.stopped,done,h])).elim
    · have E : y=(y.1,.waiting k) := Prod.ext rfl h
      change let z := next S i y e;
        (z.2=.success ∧ (WindowA0Ledger.done z.1 ∨ DoorResult i q z.1)) ∨ z.2=.failed ∨
        ∃ k : Fin 3, k.val≤1 ∧ z.2=.waiting k ∧ FrameAt z0 S i q k z.1
      rw [E]
      exact one_mark hn S i q y.1 k e hk F

#print axioms approached_frame
#print axioms clean_word

theorem success_word {p c n : Nat} {z0 : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (i : Fin n) (q : Trip (2*c))
    (x : WindowA0Ledger.State p c n) (H : FrameAt z0 S i q 0 x)
    (w : Word n) (hc : FirstExit (fun v => WindowA0GapOneWord.stopped
      (WindowA0GapOneWord.observe S i x v)) w)
    (hs : (WindowA0GapOneWord.observe S i x w).2=.success) :
    WindowA0Ledger.done (WindowA0GapOneWord.observe S i x w).1 ∨
      DoorResult i q (WindowA0GapOneWord.observe S i x w).1 := by
  rcases clean_word hn S i q x H w hc.1 with ⟨_,a⟩ | a | ⟨k,_,a,_⟩
  · exact a
  · rw [hs] at a; cases a
  · rw [hs] at a; cases a

def authenticatedCreditLayer {p c n : Nat} {z0 : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (i : Fin n) (q : Trip (2*c))
    (x : WindowA0Ledger.State p c n) (H : FrameAt z0 S i q 0 x) :
    WindowA0AttemptCredit.Layer wordNext
      (fun w => WindowA0Ledger.done (WindowA0GapOneWord.observe S i x w).1)
      (fun w => w=[])
      (fun w => WindowA0Ledger.done (WindowA0GapOneWord.observe S i x w).1 ∨
        DoorResult i q (WindowA0GapOneWord.observe S i x w).1) 216 :=
  WindowA0GapOneWord.creditLayer hn S i x _ _
    (by
      intro w hc hd
      rcases clean_word hn S i q x H w hc with ⟨h,_⟩ | h | ⟨_,_,_,F⟩
      · simp [WindowA0GapOneWord.stopped,done,h]
      · simp [WindowA0GapOneWord.stopped,done,h]
      · simp [WindowA0Ledger.done,F.live.2.1] at hd)
    (success_word hn S i q x H)

def authenticatedTimingLayer {p c n : Nat} {z0 : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (i : Fin n) (q : Trip (2*c))
    (x : WindowA0Ledger.State p c n) (H : FrameAt z0 S i q 0 x)
    (ready : Word n → Prop)
    (fail_ready : ∀ w, FirstExit (fun v => WindowA0GapOneWord.stopped
      (WindowA0GapOneWord.observe S i x v)) w →
      WindowA0GapOneWord.failed (WindowA0GapOneWord.observe S i x w) → ready w) :
    WindowA0Trial.TimedLayer wordNext ready (fun w => w=[])
      (fun w => WindowA0Ledger.done (WindowA0GapOneWord.observe S i x w).1 ∨
        DoorResult i q (WindowA0GapOneWord.observe S i x w).1) (n*2) :=
  WindowA0GapOneWord.timingLayer S i x ready _ fail_ready (success_word hn S i q x H)

#print axioms authenticatedCreditLayer
#print axioms authenticatedTimingLayer

/-- Nonterminal acceptance is already the next outward COUNT worker,
at the very same top. No additional launch mark or grace term. -/
theorem relaunch_physical {p c n : Nat} {z0 : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (i : Fin n) (H : Nat)
    (z : WindowA0ClosedEntry.State p c n) (q : Trip (2*c))
    (hc : 0<2*c)
    (ha : WindowA0ClosedEntry.Admitted z0 S (rightNeighbor i) H z)
    (hNo : ¬ WindowA0Ledger.done z.tag) (D : DoorResult i q z.tag) :
    z.gap=1 ∧ ∃ k : Fin (2*c), WindowA0ApproachOwned.Physical (rightNeighbor i) (.count k) z 0 := by
  have HL := (ha.resolve_left hNo).1
  have ht : (WindowA0ClosedEntry.cut z).top=i := D.top
  have hg : z.gap=1 := by
    apply liftedSite_inj i HL.noWrap (show 1<n by omega)
    have htarget := HL.fixedRight
    unfold WindowA0IH.target at htarget
    simpa [ht,WindowA0ClosedEntry.cut,liftedSite_succ,liftedSite_zero,D.top] using htarget
  have make (k : Fin (2*c))
      (hs : (z.tag.ledger.config (rightNeighbor i)).source=.await k)
      (hr : (z.tag.ledger.config i).rail=.uc) :
      WindowA0ApproachOwned.Physical (rightNeighbor i) (.count k) z 0 := by
    refine ⟨hs,⟨by omega,?_,?_,?_⟩⟩
    · simpa [WindowA0ApproachOwned.rails,WindowA0ClosedEntry.cut,D.top,liftedSite_zero,outward] using hr
    · intro a b d; omega
    · intro a b; omega
  refine ⟨hg,?_⟩
  cases q with
  | init =>
    exact ⟨⟨0,hc⟩,make _ (by simpa [waitingFor,inward,door_init_accept hc] using D.source)
      (by simpa [waitingFor,inward,door_init_accept hc] using D.left)⟩
  | count k =>
    by_cases hk : k.val+1<2*c
    · exact ⟨⟨k.val+1,hk⟩,make _ (by simpa [waitingFor,inward,door_count_accept k hk] using D.source)
        (by simpa [waitingFor,inward,door_count_accept k hk] using D.left)⟩
    · have hL : (z.tag.ledger.config (rightNeighbor i)).leader=true := by
        simpa [waitingFor,inward,door_terminal_accept k hk] using D.leader
      have ho := HL.rightGhost
      change (z.tag.ledger.config (rightNeighbor i)).leader=false at ho
      rw [hL] at ho
      cases ho

#print axioms relaunch_physical
end L4.WindowA0GapOneTrace
