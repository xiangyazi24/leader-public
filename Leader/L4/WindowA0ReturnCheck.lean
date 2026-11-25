import Leader.L4.WindowA0ReturnHandoff
import Leader.L4.WindowA0SpliceTrial

/-! The contact loss and genuine success branches on the unpadded raw word. -/
namespace L4.WindowA0ReturnCheck
open WindowA0ReturnWord WindowA0ReturnHandoff WindowA0ReturnEntry
open WindowA0ReturnStep FixedResidual WindowFiveStages RootedAssembly
open TripleRenewal WindowA0SpliceTrial

noncomputable def check {p c n} (S : WindowA0Ledger.Scope n) (q : Trip (2*c))
    (x : WindowA0ClosedEntry.State p c n) (d : Nat) (b : Bool) : Check n :=
  let run := GGTiming.runMarks (tick S q) (initial x d b)
  ⟨fun w => WindowA0Return.done (pos (run w)), fun w => pos (run w)=.contact⟩

private theorem cost_pull {α : Type} {n} (tick : α → Fin n → α)
    (ready : α → Prop) (t : Nat) (x : α) (w : Word n) :
    iidHitCost wordNext (fun v => ready (GGTiming.runMarks tick x v)) t w =
      iidHitCost tick ready t (GGTiming.runMarks tick x w) := by
  induction t generalizing w with
  | zero => rfl
  | succ t ih =>
    simp only [iidHitCost,ih,wordNext,GGTiming.runMarks_append]
    rfl

private theorem mass_pull {α : Type} {n} (tick : α → Fin n → α)
    (ready bad : α → Prop) (t : Nat) (x : α) (w : Word n) :
    terminalMass wordNext (fun v => ready (GGTiming.runMarks tick x v))
      (fun v => bad (GGTiming.runMarks tick x v)) t w =
      terminalMass tick ready bad t (GGTiming.runMarks tick x w) := by
  induction t generalizing w with
  | zero => rfl
  | succ t ih =>
    simp only [terminalMass,ih,wordNext,GGTiming.runMarks_append]
    rfl

theorem mean {p c n H} (hn : 4≤n) (hQ : 0<2*c) {J : Fin n} {x₀ : Config p c n}
    {S : WindowA0Ledger.Scope n} {q : Trip (2*c)} {x : WindowA0ClosedEntry.State p c n}
    {d : Nat} {b : Bool} (h : Ready x₀ S J H x q d b) (short : x.gap+2<n) :
    IIDExpectedHittingTimeAtMost wordNext (check S q x d b).stop [] (n*(x.gap-d)) := by
  intro t
  unfold check
  dsimp only
  rw [cost_pull (tick S q) (fun v => WindowA0Return.done (pos v)) t (initial x d b) []]
  exact WindowA0ReturnWord.mean hn hQ h short t

theorem failure {p c n H} (hn : 4≤n) (hQ : 0<2*c) {J : Fin n} {x₀ : Config p c n}
    {S : WindowA0Ledger.Scope n} {q : Trip (2*c)} {x : WindowA0ClosedEntry.State p c n}
    {d : Nat} {b : Bool} (h : Ready x₀ S J H x q d b) (short : x.gap+2<n) :
    ∀ t, 3*terminalMass wordNext (check S q x d b).stop (check S q x d b).bad t []≤2*n^t := by
  intro t
  unfold check
  dsimp only
  rw [mass_pull (tick S q) (fun v => WindowA0Return.done (pos v)) (fun v => pos v=.contact) t (initial x d b) []]
  exact contact_bound hn hQ h short t

private theorem contact_mark_not_done {p c n} (S : WindowA0Ledger.Scope n) (q : Trip (2*c))
    (z : Obs p c n) (e : Fin n) (act : ¬WindowA0Return.done (pos z))
    (contact : pos (tick S q z e)=.contact) :
    ¬WindowA0Ledger.done (tick S q z e).physical.tag := by
  obtain ⟨x,m⟩ := z
  cases m with
  | accepted | routed | contact => exact (act True.intro).elim
  | active d b =>
    intro hd
    let y := WindowA0ClosedEntry.next S x e
    have yes : y.tag.reason.isSome=true := hd
    change pos ⟨y,nextMode q x y e (.active d b)⟩=.contact at contact
    simp only [nextMode,if_pos yes] at contact
    cases contact

private theorem last_mark {n} (w : Word n) (hn : w≠[]) :
    ∃ v e, w=wordNext v e := by
  induction w with
  | nil => contradiction
  | cons e t ih =>
    by_cases H : t=[]
    · subst t
      exact ⟨[],e,rfl⟩
    · obtain ⟨v,f,rfl⟩ := ih H
      exact ⟨e::v,f,rfl⟩

theorem first_contact_not_done {p c n} (S : WindowA0Ledger.Scope n) (q : Trip (2*c))
    (x : WindowA0ClosedEntry.State p c n) (d : Nat) (b : Bool) (w : Word n)
    (first : FirstExit (check S q x d b).stop w) (bad : (check S q x d b).bad w) :
    ¬WindowA0Ledger.done (GGTiming.runMarks (WindowA0ClosedEntry.next S) x w).tag := by
  let run := GGTiming.runMarks (tick S q) (initial x d b)
  obtain ⟨v,e,rfl⟩ := last_mark w (by intro E; subst w; exact first.2)
  have before : ¬WindowA0Return.done (pos (run v)) := ((clean_child _ _ _).mp first.1).2
  have eq : run (wordNext v e)=tick S q (run v) e := GGTiming.runMarks_append _ _ _ _
  have bad' : pos (run (wordNext v e))=.contact := bad
  rw [eq] at bad'
  have proper := contact_mark_not_done S q (run v) e before bad'
  have pr : (run (wordNext v e)).physical=
      GGTiming.runMarks (WindowA0ClosedEntry.next S) x (wordNext v e) :=
    projection S q (initial x d b) _
  rw [←pr,eq]
  exact proper

theorem first_exit {p c n H} (hn : 4≤n) (hQ : 0<2*c) {J : Fin n} {x₀ : Config p c n}
    {S : WindowA0Ledger.Scope n} {q : Trip (2*c)} {x : WindowA0ClosedEntry.State p c n}
    {d : Nat} {b : Bool} (h : Ready x₀ S J H x q d b) (short : x.gap+2<n)
    (w : Word n) (first : FirstExit (check S q x d b).stop w) :
    let y := GGTiming.runMarks (WindowA0ClosedEntry.next S) x w
    let X := check S q x d b
    (X.bad w ∧ ¬WindowA0Ledger.done y.tag) ∨
    (¬X.bad w ∧ (WindowA0Ledger.done y.tag ∨
      ∃ (k : Fin (2*c)) (d' : Nat), successor q=some k ∧
        ordinal (.count k)=ordinal q+1 ∧ d'+1=y.gap ∧ WindowA0ClosedEntry.Admitted x₀ S J H y ∧
        WindowA0ApproachOwned.Physical J (.count k) y d')) := by
  by_cases hb : (check S q x d b).bad w
  · exact .inl ⟨hb,first_contact_not_done S q x d b w first hb⟩
  refine .inr ⟨hb,?_⟩
  have stop := first.2
  let s := pos (GGTiming.runMarks (tick S q) (initial x d b) w)
  change ¬(s=.contact) at hb
  change WindowA0Return.done s at stop
  have yes : s=.accepted := by
    cases E : s with
    | active k => rw [E] at stop; exact False.elim stop
    | contact => exact (hb E).elim
    | accepted => rfl
  rcases favorable_first_exit hn hQ h short w first yes with done|⟨k,d',hk,ho,_,hg,ha,hp⟩
  · exact .inl done
  · exact .inr ⟨k,d',hk,ho,hg,ha,hp⟩

end L4.WindowA0ReturnCheck
