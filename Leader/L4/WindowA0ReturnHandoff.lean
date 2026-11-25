import Leader.L4.WindowA0ReturnWord
import Leader.L4.WindowFiveStages

/-! The first favorable stop hands the unpadded physical state to the
next COUNT leg, with its actual successor ordinal. -/
namespace L4.WindowA0ReturnHandoff
open WindowA0ReturnWord WindowA0ReturnStep FixedResidual
open WindowA0ReturnEntry WindowFiveStages RootedAssembly

def ordinal {Q : Nat} : Trip Q → Nat
  | .init => 0
  | .count k => k.val+1

theorem successor_ordinal {Q : Nat} {q : Trip Q} {k : Fin Q}
    (h : successor q=some k) :
    ordinal (.count k)=ordinal q+1 := by
  cases q with
  | init =>
    by_cases hQ : 0<Q
    · have E : (⟨0,hQ⟩ : Fin Q)=k := Option.some.inj (by simpa [successor,hQ] using h)
      rw [←E]; rfl
    · simp [successor,hQ] at h
  | count k' =>
    by_cases H : k'.val+1<Q
    · have E : (⟨k'.val+1,H⟩ : Fin Q)=k := Option.some.inj (by simpa [successor,H] using h)
      rw [←E]; rfl
    · simp [successor,H] at h

theorem last_ordinal {Q : Nat} (hQ : 0<Q) {q : Trip Q} (h : successor q=none) :
    ordinal q=Q := by
  cases q with
  | init => simp [successor,hQ] at h
  | count k =>
    by_cases K : k.val+1<Q
    · simp [successor,K] at h
    · have L := k.isLt
      simp only [ordinal]
      omega

private theorem last_mark {n : Nat} (w : Word n) (hn : w≠[]) :
    ∃ v e, w=wordNext v e := by
  induction w with
  | nil => contradiction
  | cons e t ih =>
    by_cases H : t=[]
    · subst t
      exact ⟨[],e,rfl⟩
    · obtain ⟨v,f,rfl⟩ := ih H
      exact ⟨e::v,f,rfl⟩

theorem favorable_mark {p c n H : Nat} (hn : 4≤n) (hQ : 0<2*c)
    {x₀ : Config p c n} {S : WindowA0Ledger.Scope n} {J : Fin n}
    {q : Trip (2*c)} {z : Obs p c n} (e : Fin n)
    (hg : Good (H:=H) x₀ S J q z)
    (ha : ¬WindowA0Return.done (pos z))
    (hs : pos (tick S q z e)=.accepted) :
    let y := (tick S q z e).physical
    WindowA0Ledger.done y.tag ∨
      ∃ (k : Fin (2*c)) (d : Nat), successor q=some k ∧ ordinal (.count k)=ordinal q+1 ∧
        (tick S q z e).mode=.accepted k d ∧ d+1=y.gap ∧
        WindowA0ClosedEntry.Admitted x₀ S J H y ∧
        WindowA0ApproachOwned.Physical J (.count k) y d := by
  obtain ⟨x,m⟩ := z
  cases m with
  | contact | routed | accepted => exact False.elim (ha True.intro)
  | active d b =>
    obtain ⟨h,_⟩ := hg
    change Ready x₀ S J H x q d b at h
    let y := WindowA0ClosedEntry.next S x e
    by_cases hy : WindowA0Ledger.done y.tag
    · exact .inl hy
    have hb : ¬y.tag.reason.isSome=true := hy
    have hs' : pos ⟨y,nextMode q x y e (.active d b)⟩=.accepted := hs
    simp only [nextMode,if_neg hb] at hs'
    by_cases hi : e=x.tag.iSlot
    · rw [if_pos hi] at hs'
      split at hs'
      · split at hs' <;> cases hs'
      · cases hs'
    rw [if_neg hi] at hs'
    by_cases hj : e=x.tag.jSlot
    · rw [if_pos hj] at hs'
      by_cases hd : d+1=x.gap
      · rw [if_pos hd] at hs'
        subst e
        cases K : successor q with
        | none =>
          have T := accept_boundary hn hQ h hd
          dsimp only at T
          rw [K] at T
          exact (hy T.1).elim
        | some k =>
          obtain ⟨ad,ow⟩ := accept_owned hn hQ h hd K hy
          have shifted : WindowA0XSweep.topShift x x.tag.jSlot=0 := by
            simp [WindowA0XSweep.topShift,WindowFourHeadTrace.moves,hi]
          have eqGap : (WindowA0ClosedEntry.cut y).gap=(WindowA0ClosedEntry.cut x).gap := by
            simpa only [shifted,Nat.sub_zero] using
              (WindowA0XSweep.cut_keep_fields S x x.tag.jSlot h.running hy).2.2
          have exactGap : d+1=y.gap := hd.trans eqGap.symm
          refine .inr ⟨k,d,rfl,successor_ordinal K,?_,exactGap,ad,ow⟩
          change nextMode q x y x.tag.jSlot (.active d b)=.accepted k d
          simp only [nextMode,if_neg hb,if_neg hi,if_true,if_pos hd,K]
      · rw [if_neg hd] at hs'; cases hs'
    · rw [if_neg hj] at hs'; cases hs'

theorem favorable_first_exit {p c n H : Nat} (hn : 4≤n) (hQ : 0<2*c)
    {x₀ : Config p c n} {S : WindowA0Ledger.Scope n} {J : Fin n}
    {q : Trip (2*c)} {z : WindowA0ClosedEntry.State p c n} {d : Nat} {b : Bool}
    (h : Ready x₀ S J H z q d b) (short : z.gap+2<n) (w : Word n)
    (first : FirstExit (fun v => WindowA0Return.done
      (pos (GGTiming.runMarks (tick S q) (initial z d b) v))) w)
    (favorable : pos (GGTiming.runMarks (tick S q) (initial z d b) w)=.accepted) :
    let y := GGTiming.runMarks (WindowA0ClosedEntry.next S) z w
    WindowA0Ledger.done y.tag ∨
      ∃ (k : Fin (2*c)) (d' : Nat), successor q=some k ∧
        ordinal (.count k)=ordinal q+1 ∧
        (GGTiming.runMarks (tick S q) (initial z d b) w).mode=.accepted k d' ∧ d'+1=y.gap ∧
        WindowA0ClosedEntry.Admitted x₀ S J H y ∧
        WindowA0ApproachOwned.Physical J (.count k) y d' := by
  let run := GGTiming.runMarks (tick S q) (initial z d b)
  have wn : w≠[] := by
    intro H
    subst w
    exact first.2
  obtain ⟨v,e,rfl⟩ := last_mark w wn
  have prior : ¬WindowA0Return.done (pos (run v)) := (clean_child _ _ _).mp first.1 |>.2
  have gv := word_good hn hQ (initial z d b) v (show Good (H:=H) x₀ S J q (initial z d b) from ⟨h,short⟩)
  have eq : run (wordNext v e)=tick S q (run v) e := GGTiming.runMarks_append _ _ _ _
  have award := favorable_mark hn hQ e gv prior (eq ▸ favorable)
  have projects := projection S q (initial z d b) (wordNext v e)
  change WindowA0Ledger.done (GGTiming.runMarks (WindowA0ClosedEntry.next S) z (wordNext v e)).tag ∨ _
  change (run (wordNext v e)).physical=GGTiming.runMarks (WindowA0ClosedEntry.next S) z (wordNext v e) at projects
  rw [←projects]
  change WindowA0Ledger.done (run (wordNext v e)).physical.tag ∨
    ∃ (k : Fin (2*c)) (d' : Nat), successor q=some k ∧
      ordinal (.count k)=ordinal q+1 ∧ (run (wordNext v e)).mode=.accepted k d' ∧
      d'+1=(run (wordNext v e)).physical.gap ∧
      WindowA0ClosedEntry.Admitted x₀ S J H (run (wordNext v e)).physical ∧
      WindowA0ApproachOwned.Physical J (.count k) (run (wordNext v e)).physical d'
  rw [eq]
  exact award

#print axioms favorable_mark
#print axioms favorable_first_exit
end L4.WindowA0ReturnHandoff
