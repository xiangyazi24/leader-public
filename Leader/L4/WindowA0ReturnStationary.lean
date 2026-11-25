import Leader.L4.WindowA0ReturnEntry

/-! Routed stationary return cases. All configurations come from the
literal physical edge map, with the existing ledger retaining priority. -/
namespace L4.WindowA0ReturnStationary
open WindowA0ReturnEntry WindowA0ReturnMonitor FixedResidual

private theorem incoming_eq {n} (a : Fin n) :
    GGStage.incoming (rightNeighbor a) 0=a := by
  apply FreshSeparation.succ_inj
  rw [GGStage.incoming_right,liftedSite_zero]

private theorem neq_site {n} (a : Fin n) {i j : Nat} (hi : i<n) (hj : j<n)
    (h : i≠j) : liftedSite a i≠liftedSite a j :=
  fun hh => h (liftedSite_inj a hi hj hh)

private theorem rail_next_left {Q} (q : Trip Q) (j : Nat) :
    railShape (j+1) (inward q) j=.e := by
  simp [railShape,show j<j+1 by omega]

private theorem rail_next_right {Q} (q : Trip Q) (j : Nat) :
    railShape (j+1) (inward q) (j+1)=inward q := by
  simp [railShape]

private theorem rail_next_else {Q} (q : Trip Q) (j i : Nat)
    (hi : i≠j) (hi' : i≠j+1) :
    railShape j (inward q) i=railShape (j+1) (inward q) i := by
  by_cases h : i<j
  · simp [railShape,h,show i<j+1 by omega]
  · simp [railShape,h,hi,hi',show ¬ i<j+1 by omega]

/-- Exact invariant on the next tagged state for every ordinary retained
mark; the only distance change is the actual D/T crossing. -/
theorem routed_ordinary {p c n H} (hn : 4≤n) {J : Fin n} {z0 : Config p c n}
    {S : WindowA0Ledger.Scope n} {x : WindowA0ClosedEntry.State p c n}
    {q : Trip (2*c)} {d j : Nat} {b : Bool}
    (h : Ready z0 S J H x q d b) (hj : j+1<x.gap)
    (hshort : x.gap+2<n) :
    let e := liftedSite (WindowA0ClosedEntry.cut x).top j
    let y := WindowA0ClosedEntry.next S x e
    WindowA0Ledger.done y.tag ∨ Ready z0 S J H y q (if j=d then d+1 else d) b := by
  let a := WindowA0ClosedEntry.cut x
  let e := liftedSite a.top j
  let y := WindowA0ClosedEntry.next S x e
  let z := WindowA0ClosedEntry.cut y
  let D := if j=d then d+1 else d
  change WindowA0Ledger.done y.tag ∨ Ready z0 S J H y q D b
  by_cases hx : WindowA0Ledger.done y.tag
  · exact .inl hx
  have old : WindowA0IH.Live J H a := (h.admitted.resolve_left
    (by simp [WindowA0Ledger.done,h.running])).1
  have hm := old.openBonds j hj
  have heTop : e≠x.tag.iSlot := by
    intro H
    have hh : liftedSite a.top (j+1)=liftedSite a.top 0 := by
      rw [liftedSite_succ,show liftedSite a.top j=e from rfl,H,liftedSite_zero]; rfl
    have := liftedSite_inj a.top (show j+1<n by omega) (show 0<n by omega) hh
    omega
  have stay : WindowA0XSweep.topShift x e=0 := by
    simp [WindowA0XSweep.topShift,WindowFourHeadTrace.moves,heTop]
  obtain ⟨hcfg,ht,hg⟩ := WindowA0XSweep.cut_keep_fields S x e h.running hx
  change z.config=step a.config e at hcfg
  have zt : z.top=a.top := by simpa [stay,liftedSite_zero] using ht
  have zg : z.gap=a.gap := by simpa [stay] using hg
  have hclose := WindowA0ClosedEntry.close hn S J H x e h.admitted
  have hrun : y.tag.reason=none := by
    cases H : y.tag.reason
    · rfl
    · exact (hx (by simp [WindowA0Ledger.done,H])).elim
  have hOff := h.interiorOff (j+1) (by omega) hj
  have pairs := actual_interior_pair old q d j h.shape hj hOff
  have hlt : j+1<n := by omega
  have gl : a.gap<n := old.noWrap
  have hj' : j+1<a.gap := hj
  have right : rightNeighbor e=liftedSite a.top (j+1) := (liftedSite_succ _ _).symm
  have pairOff : (step a.config e (liftedSite a.top (j+1))).source=.off := by
    have hl : (a.config (liftedSite a.top (j+1))).leader=false := by
      apply Bool.eq_false_iff.mpr
      intro H
      have HH := old.mc e (.inl (by rwa [right]))
      change (a.config e).mark=false at hm
      rw [hm] at HH
      contradiction
    have hr : (a.config (liftedSite a.top (j+1))).residue=
        nextResidue (a.config e).residue := by
      apply Classical.byContradiction
      intro H
      have HH := old.mc e (.inr (by rwa [right]))
      change (a.config e).mark=false at hm
      rw [hm] at HH
      contradiction
    obtain ⟨m,l⟩ := FreshEpochAuthentication.ordinary_prefix_flags _ _ hm hr hl
    have hh : liftedSite a.top (j+1)≠e := neq_site a.top hlt (by omega) (by omega)
    simp only [step,hh,right,if_true,if_false]
    exact ordinary_off _ _ l m hOff
  have cold : b=false →
      (z.config y.tag.iSlot).leader=false ∧ (z.config y.tag.iSlot).stock=false := by
    intro hb
    have same : y.tag.iSlot=x.tag.iSlot := by
      apply FreshSeparation.succ_inj
      exact zt
    have heRight : rightNeighbor e≠x.tag.iSlot := by
      intro H
      have E : liftedSite a.top (j+2)=liftedSite a.top 0 := by
        rw [liftedSite_succ,←right,H,liftedSite_zero]; rfl
      have := liftedSite_inj a.top (show j+2<n by omega) (show 0<n by omega) E
      omega
    rw [same,hcfg]
    simpa only [step,Ne.symm heTop,Ne.symm heRight,if_false] using h.coldBeforeRefill hb
  refine .inr ⟨hclose,hrun,?_,?_,?_,?_,cold⟩
  · unfold D
    split <;> have := h.positive <;> omega
  · change RailShape z.config z.top z.gap D q
    rw [hcfg,zt,zg]
    refine ⟨?_,?_⟩
    · unfold D
      split
      · rename_i hEq
        omega
      · exact h.shape.1
    · intro i hi
      have hnI : i<n := by omega
      by_cases hh : j=d
      · have pair : ((step a.config e e).rail,
            (step a.config e (liftedSite a.top (j+1))).rail)=(.e,inward q) := by
          dsimp only at pairs
          rw [if_pos hh] at pairs
          exact pairs
        have dEq : D=j+1 := by simp [D,hh]
        rw [dEq]
        by_cases h0 : i=j
        · subst i
          exact (congrArg Prod.fst pair).trans (rail_next_left q j).symm
        · by_cases h1 : i=j+1
          · subst i
            exact (congrArg Prod.snd pair).trans (rail_next_right q j).symm
          · have hL : liftedSite a.top i≠e := neq_site a.top hnI (by omega) h0
            have hR : liftedSite a.top i≠rightNeighbor e := right ▸ neq_site a.top hnI hlt h1
            simp only [step,hL,hR,if_false]
            exact (h.shape.2 i hi).trans (hh ▸ rail_next_else q j i h0 h1)
      · have pair : ((step a.config e e).rail,
            (step a.config e (liftedSite a.top (j+1))).rail)=
            ((a.config e).rail,(a.config (liftedSite a.top (j+1))).rail) := by
          simpa only [hh,if_false] using pairs
        have dEq : D=d := by simp [D,hh]
        rw [dEq]
        by_cases h0 : i=j
        · subst i
          exact (congrArg Prod.fst pair).trans (h.shape.2 _ hi)
        · by_cases h1 : i=j+1
          · subst i
            exact (congrArg Prod.snd pair).trans (h.shape.2 _ hi)
          · have hL : liftedSite a.top i≠e := neq_site a.top hnI (by omega) h0
            have hR : liftedSite a.top i≠rightNeighbor e := right ▸ neq_site a.top hnI hlt h1
            simpa only [step,hL,hR,if_false] using h.shape.2 i hi
  · intro i hpos hI
    change i<z.gap at hI
    rw [zg] at hI
    change (z.config (liftedSite z.top i)).source=.off
    rw [hcfg,zt]
    by_cases h0 : i=j+1
    · simpa [h0] using pairOff
    · have nr : liftedSite a.top i≠rightNeighbor e := right ▸ neq_site a.top (by omega) hlt h0
      by_cases hu : liftedSite a.top i=e
      · rw [hu]
        simpa [step,FreshEpochAuthentication.pair_left_source] using (hu ▸ h.interiorOff i hpos hI)
      · simpa only [step,hu,nr,if_false] using h.interiorOff i hpos hI
  · change (z.config J).source=waitingFor q
    have JE : J=liftedSite a.top a.gap := old.fixedRight.symm
    have hL : J≠e := JE ▸ neq_site a.top gl (by omega) (by omega)
    have hR : J≠rightNeighbor e := by
      rw [JE,right]
      exact neq_site a.top gl hlt (by omega)
    simpa only [hcfg,step,hL,hR,if_false] using h.matchingDoor

/-- The fixed J-boundary mark is a true simultaneous timer row.
When D sits at the last socket it accepts on that same raw mark,
whether or not the ledger also credits the resulting selected birth.
For a shorter return it keeps T and the matching waiting source. -/
theorem actual_door {p c n H} (hn : 4≤n) {J : Fin n} {z0 : Config p c n}
    {S : WindowA0Ledger.Scope n} {x : WindowA0ClosedEntry.State p c n}
    {q : Trip (2*c)} {d : Nat} {b : Bool}
    (h : Ready z0 S J H x q d b) :
    let e := x.tag.jSlot
    let y := (WindowA0ClosedEntry.cut (WindowA0ClosedEntry.next S x e)).config
    (d+1=x.gap → let t := serviceDoor (waitingFor q) (inward q)
      (y e).rail=t.left ∧
      (y J).source=(if t.fire then .off else t.source) ∧ (y J).leader=t.fire) ∧
    (d+1<x.gap → (y e).rail=.t ∧
      (y J).source=waitingFor q ∧ (y J).leader=false) := by
  let a := WindowA0ClosedEntry.cut x
  let e := x.tag.jSlot
  let x' := WindowA0ClosedEntry.next S x e
  let y := (WindowA0ClosedEntry.cut x').config
  obtain ⟨old,_,jr⟩ := h.admitted.resolve_left
    (by simp [WindowA0Ledger.done,h.running])
  have hcfg : y=step a.config e := by
    change (WindowA0Ledger.next S x.tag e).ledger.config=_
    rw [WindowA0Ledger.physical_step]
    rfl
  have npos : 0<a.gap := old.gapPos
  have right : rightNeighbor e=J := jr
  have edge : e=liftedSite a.top (a.gap-1) := by
    apply FreshSeparation.succ_inj
    rw [right,←liftedSite_succ,show a.gap-1+1=a.gap by have := old.gapPos; omega]
    exact old.fixedRight.symm
  have eN : J≠e := by
    intro H
    have w : liftedSite e 1=liftedSite e 0 := by
      rw [liftedSite_succ,liftedSite_zero,right,H]
    have := liftedSite_inj e (show 1<n by omega) (show 0<n by omega) w
    omega
  have L : (a.config e).leader=false := by
    rw [edge]
    match hh : a.gap-1 with
    | 0 => simpa only [liftedSite_zero] using old.topGhost
    | k+1 =>
      apply Bool.eq_false_iff.mpr
      intro hL
      have hm := old.mc (liftedSite a.top k) (.inl (by rwa [←liftedSite_succ]))
      have hk : k+1<a.gap := by omega
      rw [old.openBonds k hk] at hm
      contradiction
  have M : (a.config e).mark=true := by rw [edge]; exact old.markRight
  have gap : a.gap=x.gap := rfl
  have F : (a.config e).stock=false := by
    rw [edge]
    exact old.empty _ (by change a.gap-1<a.gap; omega)
  have shape : (a.config e).rail=railShape d (inward q) (a.gap-1) := by
    rw [edge]
    exact h.shape.2 _ (by omega)
  have R := door_envelope (a.config e) (a.config J) q M L old.rightGhost F h.matchingDoor
  change (d+1=x.gap → let t := serviceDoor (waitingFor q) (inward q)
    (y e).rail=t.left ∧ (y J).source=(if t.fire then .off else t.source) ∧
      (y J).leader=t.fire) ∧
    (d+1<x.gap → (y e).rail=.t ∧ (y J).source=waitingFor q ∧ (y J).leader=false)
  constructor
  · intro hd
    have D : (a.config e).rail=inward q := by
      rw [shape,show a.gap-1=d by omega]
      simp [railShape]
    simpa only [hcfg,step,eN,right,if_true,if_false] using R.2 D
  · intro hd
    have T : (a.config e).rail=.t := by
      rw [shape]
      simp [railShape,show ¬a.gap-1<d by omega,show a.gap-1≠d by omega]
    simpa only [hcfg,step,eN,right,if_true,if_false] using R.1 T

end L4.WindowA0ReturnStationary
