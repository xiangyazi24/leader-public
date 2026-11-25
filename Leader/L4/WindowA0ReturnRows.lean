import Leader.L4.WindowA0ReturnStep

/-! Physical preservation of the authenticated return at stationary
boundary marks. Every clause refers to the advanced closed ledger. -/
namespace L4.WindowA0ReturnRows
open WindowA0ReturnEntry WindowA0ReturnMonitor FixedResidual

private theorem reason_none {p c n} (z : WindowA0Ledger.State p c n)
    (h : ¬WindowA0Ledger.done z) : z.reason=none := by
  cases E : z.reason <;> simp_all [WindowA0Ledger.done]

theorem stationary {p c n H} (hn : 4≤n) {J : Fin n} {z0 : Config p c n}
    {S : WindowA0Ledger.Scope n} {x : WindowA0ClosedEntry.State p c n}
    {q : Trip (2*c)} {d : Nat} {b b' : Bool} (e : Fin n)
    (h : Ready z0 S J H x q d b) (hs : WindowA0XSweep.topShift x e=0)
    (hreceivers : let a := WindowA0ClosedEntry.cut x
      ∀ i, 0<i → i<a.gap → liftedSite a.top i≠rightNeighbor e)
    (hboundary : let a := WindowA0ClosedEntry.cut x
      ∀ i, i<a.gap → (liftedSite a.top i=e ∨ liftedSite a.top i=rightNeighbor e) →
        (step a.config e (liftedSite a.top i)).rail=(a.config (liftedSite a.top i)).rail)
    (hdoor : let a := WindowA0ClosedEntry.cut x
      (step a.config e J).source=waitingFor q)
    (hcold : b'=false → e≠RearTrace.predecessor x.tag.iSlot)
    (hb : b'=false → b=false) :
    let y := WindowA0ClosedEntry.next S x e
    WindowA0Ledger.done y.tag ∨ Ready z0 S J H y q d b' := by
  let a := WindowA0ClosedEntry.cut x
  let y := WindowA0ClosedEntry.next S x e
  let z := WindowA0ClosedEntry.cut y
  change WindowA0Ledger.done y.tag ∨ Ready z0 S J H y q d b'
  by_cases hd : WindowA0Ledger.done y.tag
  · exact .inl hd
  obtain ⟨cfg,tp,gp⟩ := WindowA0XSweep.cut_keep_fields S x e h.running hd
  change z.config=step a.config e at cfg
  have ht : z.top=a.top := by simpa only [hs,liftedSite_zero] using tp
  have hg : z.gap=a.gap := by simpa only [hs,Nat.sub_zero] using gp
  have old := (h.admitted.resolve_left (by simp [WindowA0Ledger.done,h.running])).1
  have hclose := WindowA0ClosedEntry.close hn S J H x e h.admitted
  have hl : y.tag.iSlot=x.tag.iSlot := FreshSeparation.succ_inj ht
  refine .inr ⟨hclose,reason_none _ hd,h.positive,?_,?_,?_,?_⟩
  · change RailShape z.config z.top z.gap d q
    rw [cfg,ht,hg]
    refine ⟨h.shape.1,?_⟩
    intro i hi
    by_cases p : liftedSite a.top i=e
    · exact (hboundary i hi (.inl p)).trans (h.shape.2 i hi)
    by_cases q' : liftedSite a.top i=rightNeighbor e
    · exact (hboundary i hi (.inr q')).trans (h.shape.2 i hi)
    simpa only [step,p,q',if_false] using h.shape.2 i hi
  · intro i hi hg'
    change i<z.gap at hg'
    rw [hg] at hg'
    change (z.config (liftedSite z.top i)).source=.off
    rw [cfg,ht]
    have nr : liftedSite a.top i≠rightNeighbor e := hreceivers i hi hg'
    have oldOff : (a.config (liftedSite a.top i)).source=.off := h.interiorOff i hi hg' 
    by_cases E : liftedSite a.top i=e
    · simpa only [step,E,if_true,FreshEpochAuthentication.pair_left_source]
        using oldOff
    · simpa only [step,E,nr,if_false] using oldOff
  · change (z.config J).source=waitingFor q
    rw [cfg]; exact hdoor
  · intro hb'
    change (z.config y.tag.iSlot).leader=false ∧ (z.config y.tag.iSlot).stock=false
    rw [cfg,hl]
    apply cold_donor_stays_cold _ _ _ (h.coldBeforeRefill (hb hb')) _ (hcold hb')
    change (a.config a.top).stock=false
    simpa only [liftedSite_zero] using old.empty 0 old.gapPos

private theorem incoming_eq {n} (s : Fin n) : GGStage.incoming (rightNeighbor s) 0=s := by
  apply FreshSeparation.succ_inj
  rw [GGStage.incoming_right,liftedSite_zero]

private theorem off_door {p c n} (a : WindowA0IH.Cut p c n) (q : Trip (2*c))
    (e J : Fin n) (hn : J≠rightNeighbor e) (hs : (a.config J).source=waitingFor q) :
    (step a.config e J).source=waitingFor q := by
  by_cases h : J=e
  · simpa only [step,h,if_true,FreshEpochAuthentication.pair_left_source] using hs
  · simpa only [step,h,hn,if_false] using hs

/-- Unpaid old incoming-top service preserves the running worker; the
arbitrary upstream controller at the top need not be OFF. -/
theorem unpaid_top {p c n H} (hn : 4≤n) {J : Fin n} {z0 : Config p c n}
    {S : WindowA0Ledger.Scope n} {x : WindowA0ClosedEntry.State p c n}
    {q : Trip (2*c)} {d : Nat} {b : Bool}
    (h : Ready z0 S J H x q d b) (short : x.gap+1<n)
    (hp : geometricPay (x.tag.ledger.config x.tag.iSlot)
      (x.tag.ledger.config (rightNeighbor x.tag.iSlot))=false) :
    let y := WindowA0ClosedEntry.next S x x.tag.iSlot
    WindowA0Ledger.done y.tag ∨ Ready z0 S J H y q d b := by
  let a := WindowA0ClosedEntry.cut x
  let e := x.tag.iSlot
  have old := (h.admitted.resolve_left (by simp [WindowA0Ledger.done,h.running])).1
  have sr : rightNeighbor e=a.top := rfl
  have sh : a.gap+1<n := short
  have noleft (i : Nat) (hi : i<a.gap) : liftedSite a.top i≠e := by
    intro L
    have R := congrArg rightNeighbor L
    rw [←liftedSite_succ,sr] at R
    have := liftedSite_inj a.top (show i+1<n by omega) (show 0<n by omega)
      (R.trans (liftedSite_zero _).symm)
    omega
  have noright (i : Nat) (hi : i<a.gap) (hpos : 0<i) :
      liftedSite a.top i≠rightNeighbor e := by
    rw [sr]
    intro R
    have := liftedSite_inj a.top (show i<n by omega) (show 0<n by omega)
      (R.trans (liftedSite_zero _).symm)
    omega
  have shift : WindowA0XSweep.topShift x e=0 := by
    simp [WindowA0XSweep.topShift,WindowFourHeadTrace.moves,e,hp]
  refine stationary hn e h shift (fun i hi hg => noright i hg hi) ?_ ?_ ?_ id
  · dsimp only
    intro i hi incident
    have H : i=0 := by
      rcases incident with L|R
      · exact (noleft i hi L).elim
      · by_cases E : 0<i
        · exact (noright i hi E R).elim
        · omega
    subst i
    rw [liftedSite_zero,←sr]
    obtain ⟨hPrefixL,hPrefixR⟩ : (stepPrefix (a.config e) (a.config (rightNeighbor e))).1.mark=true ∧
        (stepPrefix (a.config e) (a.config (rightNeighbor e))).2.leader=false := by
      have hm : (a.config e).mark=true := by
        have H : (a.config (GGStage.incoming a.top 0)).mark=true := old.markTop
        simpa only [show GGStage.incoming a.top 0=e from incoming_eq e] using H
      unfold stepPrefix
      let v := native (materialize (a.config e) (a.config (rightNeighbor e))) (a.config (rightNeighbor e))
      change (payment v.1 v.2).1.mark=true ∧ (payment v.1 v.2).2.leader=false
      have M : v.1.mark=true := by
        change (native (materialize (a.config e) (a.config (rightNeighbor e))) (a.config (rightNeighbor e))).1.mark=true
        rw [FreshEpochAuthentication.native_preserves_mark]
        simp [materialize,hm]
      have L : v.2.leader=false := FreshEpochAuthentication.old_follower_native _ _ old.topGhost
      change (!v.2.leader && v.1.mark && payer v.1)=false at hp
      have N : payer v.1=false := by simpa only [L,M,Bool.not_false,Bool.true_and] using hp
      simp [payment,M,L,N]
    have eq := top_shape (a.config e) (a.config (rightNeighbor e)) q d hPrefixR hPrefixL
      (by rw [sr]; simpa only [liftedSite_zero] using h.shape.2 0 old.gapPos)
    have ne : rightNeighbor e≠e := by simpa only [liftedSite_zero,←sr] using noleft 0 old.gapPos
    simpa only [step,ne,if_false,if_true] using eq
  · apply off_door a q e J _ h.matchingDoor
    rw [sr,←old.fixedRight]
    intro E
    have := liftedSite_inj a.top old.noWrap (show 0<n by omega)
      (E.trans (liftedSite_zero _).symm)
    have := old.gapPos
    omega
  · intro _
    intro E
    have A := congrArg rightNeighbor E
    rw [RearTrace.right_predecessor] at A
    have AA : rightNeighbor e=e := A
    exact noleft 0 old.gapPos (by simpa only [liftedSite_zero,←sr] using AA)


/-- Exterior labels, including J as initiator, cannot affect the
authenticated rail. The fresh label opens the payment opportunity
even when that interaction delivers no stock. -/
theorem exterior {p c n H} (hn : 4≤n) {J : Fin n} {z0 : Config p c n}
    {S : WindowA0Ledger.Scope n} {x : WindowA0ClosedEntry.State p c n}
    {q : Trip (2*c)} {d : Nat} {b : Bool} (e : Fin n)
    (h : Ready z0 S J H x q d b)
    (he : e≠x.tag.iSlot) (hj : rightNeighbor e≠J)
    (off : let a := WindowA0ClosedEntry.cut x
      ∀ i, i<a.gap → liftedSite a.top i≠e ∧ liftedSite a.top i≠rightNeighbor e) :
    let y := WindowA0ClosedEntry.next S x e
    WindowA0Ledger.done y.tag ∨ Ready z0 S J H y q d
      (if e=RearTrace.predecessor x.tag.iSlot then true else b) := by
  have shift : WindowA0XSweep.topShift x e=0 := by
    simp [WindowA0XSweep.topShift,WindowFourHeadTrace.moves,he]
  refine stationary hn e h shift (fun i _ hi => (off i hi).2)
    ?_ (off_door _ _ _ _ (Ne.symm hj) h.matchingDoor) ?_ ?_
  · dsimp only
    intro i hi H
    rcases H with H|H
    · exact ((off i hi).1 H).elim
    · exact ((off i hi).2 H).elim
  · intro F E
    simp only [E,if_true] at F
    contradiction
  · intro F
    split at F
    · contradiction
    · exact F

/-- A fixed-door mark before the worker is adjacent preserves this
return, including the real stock/leader cold condition. -/
theorem separated_door {p c n H} (hn : 4≤n) {J : Fin n} {z0 : Config p c n}
    {S : WindowA0Ledger.Scope n} {x : WindowA0ClosedEntry.State p c n}
    {q : Trip (2*c)} {d : Nat} {b : Bool}
    (h : Ready z0 S J H x q d b) (hd : d+1<x.gap) (short : x.gap+1<n) :
    let y := WindowA0ClosedEntry.next S x x.tag.jSlot
    WindowA0Ledger.done y.tag ∨ Ready z0 S J H y q d b := by
  let a := WindowA0ClosedEntry.cut x
  let e := x.tag.jSlot
  have hd' : d+1<a.gap := hd
  obtain ⟨old,_,jr⟩ := h.admitted.resolve_left (by simp [WindowA0Ledger.done,h.running])
  have gl : a.gap<n := old.noWrap
  have sh : a.gap+1<n := short
  have t : rightNeighbor x.tag.iSlot=a.top := rfl
  have ed : e=liftedSite a.top (a.gap-1) := by
    apply FreshSeparation.succ_inj
    rw [jr,←liftedSite_succ,show a.gap-1+1=a.gap by omega]
    exact old.fixedRight.symm
  have he : e≠x.tag.iSlot := by
    intro E
    have K := liftedSite_inj a.top gl (show 0<n by omega)
      (old.fixedRight.trans ((jr.symm.trans (congrArg rightNeighbor E)).trans
        (t.trans (liftedSite_zero _).symm)))
    omega
  have shift : WindowA0XSweep.topShift x e=0 := by
    simp [WindowA0XSweep.topShift,WindowFourHeadTrace.moves,he]
  have off (i : Nat) (hi : i<a.gap) : liftedSite a.top i≠rightNeighbor e := by
    rw [jr,←old.fixedRight]
    intro E
    have := liftedSite_inj a.top (Nat.lt_trans hi gl) gl E
    omega
  have facts := (WindowA0ReturnStationary.actual_door hn h).2 hd
  have config : (WindowA0ClosedEntry.cut (WindowA0ClosedEntry.next S x e)).config=step a.config e := by
    change (WindowA0Ledger.next S x.tag e).ledger.config=_
    rw [WindowA0Ledger.physical_step]
    rfl
  change ((WindowA0ClosedEntry.cut (WindowA0ClosedEntry.next S x e)).config e).rail=.t ∧
    ((WindowA0ClosedEntry.cut (WindowA0ClosedEntry.next S x e)).config J).source=waitingFor q ∧ _ at facts
  rw [config] at facts
  refine stationary hn e h shift (fun i _ hi => off i hi) ?_ facts.2.1 ?_ id
  · dsimp only
    intro i hi E
    rcases E with E|E
    · have R : (a.config (liftedSite a.top (a.gap-1))).rail=railShape d (inward q) (a.gap-1) := h.shape.2 _ (show a.gap-1<a.gap by omega)
      rw [E,facts.1,ed,R]
      simp [railShape,show ¬a.gap-1<d by omega,show a.gap-1≠d by omega]
    · exact (off i hi E).elim
  · intro _ E
    have A := congrArg rightNeighbor E
    rw [RearTrace.right_predecessor,jr] at A
    have B := congrArg rightNeighbor A
    have jf : liftedSite a.top a.gap=J := old.fixedRight
    rw [←jf,←liftedSite_succ,t] at B
    have := liftedSite_inj a.top sh (show 0<n by omega) (B.trans (liftedSite_zero _).symm)
    omega

#print axioms unpaid_top
#print axioms exterior
#print axioms separated_door

theorem exterior_of_not_initiator {p c n H} (hn : 4≤n) {J : Fin n} {z0 : Config p c n}
    {S : WindowA0Ledger.Scope n} {x : WindowA0ClosedEntry.State p c n}
    {q : Trip (2*c)} {d : Nat} {b : Bool} (e : Fin n)
    (h : Ready z0 S J H x q d b)
    (hi : e≠x.tag.iSlot) (hj : e≠x.tag.jSlot)
    (hout : let a := WindowA0ClosedEntry.cut x
      ∀ i, i+1<a.gap → liftedSite a.top i≠e) :
    let y := WindowA0ClosedEntry.next S x e
    WindowA0Ledger.done y.tag ∨ Ready z0 S J H y q d
      (if e=RearTrace.predecessor x.tag.iSlot then true else b) := by
  let a := WindowA0ClosedEntry.cut x
  obtain ⟨old,_,jr⟩ := h.admitted.resolve_left (by simp [WindowA0Ledger.done,h.running])
  have jf : liftedSite a.top a.gap=J := old.fixedRight
  have right : rightNeighbor e≠J := by
    intro E
    exact hj (FreshSeparation.succ_inj (E.trans jr.symm))
  apply exterior hn e h hi right
  dsimp only
  intro i H
  change i<a.gap at H
  constructor
  · by_cases K : i+1<a.gap
    · exact hout i K
    · intro E
      apply right
      rw [←E,←liftedSite_succ,show i+1=a.gap by omega,jf]
  · intro E
    cases i with
    | zero =>
      rw [liftedSite_zero] at E
      have t : rightNeighbor x.tag.iSlot=a.top := rfl
      exact hi (FreshSeparation.succ_inj (E.symm.trans t.symm))
    | succ i =>
      rw [liftedSite_succ] at E
      exact hout i H (FreshSeparation.succ_inj E)

#print axioms exterior_of_not_initiator

/-- Every mark of an active physical return is classified, with routed
stops taking priority. The contact branch retains the real inward rail
at offset zero, and all other kept outcomes have their actual next
ownership predicate. -/
theorem step_classify {p c n H} (hn : 4≤n) (hQ : 0<2*c) {J : Fin n}
    {z0 : Config p c n} {S : WindowA0Ledger.Scope n}
    {x : WindowA0ClosedEntry.State p c n}
    {q : Trip (2*c)} {d : Nat} {b : Bool}
    (h : Ready z0 S J H x q d b) (short : x.gap+2<n) (e : Fin n) :
    let a := WindowA0ClosedEntry.cut x
    let y := WindowA0ClosedEntry.next S x e
    WindowA0Ledger.done y.tag ∨
    (if e=x.tag.iSlot then
      if geometricPay (a.config e) (a.config (rightNeighbor e)) then
        b=true ∧ ((d=1 ∧ RailShape (WindowA0ClosedEntry.cut y).config
                (WindowA0ClosedEntry.cut y).top y.gap 0 q) ∨
          Ready z0 S J H y q (d-1) false)
      else Ready z0 S J H y q d b
    else if e=x.tag.jSlot then
      if d+1=x.gap then
        ∃ k, WindowA0ReturnStep.successor q=some k ∧
          WindowA0ApproachOwned.Physical J (.count k) y d
      else Ready z0 S J H y q d b
    else Ready z0 S J H y q
      (if e=liftedSite a.top d then d+1 else d)
      (if e=RearTrace.predecessor x.tag.iSlot then true else b)) := by
  let a := WindowA0ClosedEntry.cut x
  let y := WindowA0ClosedEntry.next S x e
  have shape := h.shape.1
  have pos := h.positive
  by_cases hy : WindowA0Ledger.done y.tag
  · exact .inl hy
  refine .inr ?_
  split
  · rename_i eq
    subst e
    split
    · rename_i hp
      have B : b=true := by
        cases b with
        | true => rfl
        | false =>
          have F := WindowA0ReturnStep.ready_no_pay h
          exact False.elim (Bool.noConfusion (F.symm.trans hp))
      exact ⟨B,(routed_paid hn h (by omega) hp).resolve_left hy⟩
    · rename_i hp
      exact (unpaid_top hn h (by omega) (Bool.eq_false_iff.mpr hp)).resolve_left hy
  · rename_i ni
    split
    · rename_i eq
      subst e
      split
      · rename_i E
        cases K : WindowA0ReturnStep.successor q with
        | none =>
          have F := WindowA0ReturnStep.accept_boundary hn hQ h E
          dsimp only at F
          rw [K] at F
          exact (hy F.1).elim
        | some k =>
          exact ⟨k,rfl,(WindowA0ReturnStep.accept_owned hn hQ h E K hy).2⟩
      · rename_i E
        exact (separated_door hn h (by change d<x.gap at shape; omega) (by omega)).resolve_left hy
    · rename_i nj
      have ag : a.gap=x.gap := rfl
      have gl : a.gap<n := by omega
      have dl : d<a.gap := shape
      have old := (h.admitted.resolve_left (by simp [WindowA0Ledger.done,h.running]))
      have hd : x.tag.jSlot=liftedSite a.top (a.gap-1) := by
        apply FreshSeparation.succ_inj
        rw [old.2.2,←liftedSite_succ,show a.gap-1+1=a.gap by omega]
        exact old.1.fixedRight.symm
      by_cases I : ∃ j, j+1<a.gap ∧ e=liftedSite a.top j
      · obtain ⟨j,hj,rfl⟩ := I
        have notFresh : liftedSite a.top j≠RearTrace.predecessor x.tag.iSlot := by
          intro E
          have A := congrArg rightNeighbor E
          rw [←liftedSite_succ,RearTrace.right_predecessor] at A
          have B := congrArg rightNeighbor A
          change rightNeighbor (liftedSite a.top (j+1))=a.top at B
          rw [←liftedSite_succ] at B
          have := liftedSite_inj a.top (show j+1+1<n by omega) (show 0<n by omega)
            (B.trans (liftedSite_zero _).symm)
          omega
        have iffEq : liftedSite a.top j=liftedSite a.top d ↔ j=d :=
          ⟨liftedSite_inj a.top (by omega) (by omega),congrArg (liftedSite a.top)⟩
        change Ready z0 S J H y q
          (if liftedSite a.top j=liftedSite a.top d then d+1 else d)
          (if liftedSite a.top j=RearTrace.predecessor x.tag.iSlot then true else b)
        simp only [if_neg notFresh,iffEq]
        exact (WindowA0ReturnStationary.routed_ordinary hn h (j:=j) (by omega) short).resolve_left hy
      · have notWorker : e≠liftedSite a.top d := by
          intro ed
          by_cases H : d+1<a.gap
          · exact I ⟨d,H,ed⟩
          · exact nj (by rw [hd,show a.gap-1=d by omega]; exact ed)
        rw [if_neg notWorker]
        exact (exterior_of_not_initiator hn e h ni nj
          (fun j hj E => I ⟨j,hj,E.symm⟩)).resolve_left hy

#print axioms step_classify
end L4.WindowA0ReturnRows
