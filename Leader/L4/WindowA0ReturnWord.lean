import Leader.L4.WindowA0ReturnRows

/-! A sticky physical return observer. Terminal bookkeeping freezes;
the genuine tagged ledger still takes every raw scheduler mark. -/
namespace L4.WindowA0ReturnWord
open WindowA0Return WindowA0ReturnMonitor WindowA0ReturnEntry
open WindowA0ReturnRows FixedResidual WindowA0ClosedEntry

inductive Mode (Q : Nat) where
  | active (d : Nat) (b : Bool)
  | contact
  | accepted (k : Fin Q) (d : Nat)
  | routed

structure Obs (p c n : Nat) where
  physical : WindowA0ClosedEntry.State p c n
  mode : Mode (2*c)

def initial {p c n : Nat} (x : WindowA0ClosedEntry.State p c n) (d : Nat) (b : Bool) : Obs p c n :=
  ⟨x,.active d b⟩

noncomputable def nextMode {p c n : Nat} (q : Trip (2*c)) (x y : WindowA0ClosedEntry.State p c n) (e : Fin n) :
    Mode (2*c) → Mode (2*c)
  | .active d b =>
    if y.tag.reason.isSome then .routed
    else if e=x.tag.iSlot then
      if geometricPay (x.tag.ledger.config e) (x.tag.ledger.config (rightNeighbor e)) then
        if d=1 then .contact else .active (d-1) false
      else .active d b
    else if e=x.tag.jSlot then
      if d+1=x.gap then
        match WindowA0ReturnStep.successor q with
        | some k => .accepted k d
        | none => .routed
      else .active d b
    else .active (if e=liftedSite (cut x).top d then d+1 else d)
        (if e=RearTrace.predecessor x.tag.iSlot then true else b)
  | m => m

noncomputable def tick {p c n : Nat} (S : WindowA0Ledger.Scope n) (q : Trip (2*c))
    (z : Obs p c n) (e : Fin n) : Obs p c n :=
  let y := WindowA0ClosedEntry.next S z.physical e
  ⟨y,nextMode q z.physical y e z.mode⟩

def pos {p c n : Nat} (z : Obs p c n) : Position :=
  match z.mode with
  | .active d b => .active (exponent 0 d b)
  | .contact => .contact
  | .accepted _ _ | .routed => .accepted

def Good {p c n H : Nat} (x₀ : Config p c n) (S : WindowA0Ledger.Scope n)
    (J : Fin n) (q : Trip (2*c)) (z : Obs p c n) : Prop :=
  match z.mode with
  | .active d b => Ready x₀ S J H z.physical q d b ∧ z.physical.gap+2<n
  | _ => True

theorem projection {p c n} (S : WindowA0Ledger.Scope n) (q : Trip (2*c))
    (z : Obs p c n) (w : List (Fin n)) :
    (GGTiming.runMarks (tick S q) z w).physical=
      GGTiming.runMarks (WindowA0ClosedEntry.next S) z.physical w := by
  induction w generalizing z with
  | nil => rfl
  | cons e w ih => exact ih (tick S q z e)

private theorem gap_mono {p c n} (S : WindowA0Ledger.Scope n) (x : WindowA0ClosedEntry.State p c n)
    (e : Fin n) : (WindowA0ClosedEntry.next S x e).gap≤x.gap := by
  simp only [WindowA0ClosedEntry.next]
  split
  · exact Nat.le_refl _
  · exact Nat.sub_le ..

private theorem done_iff {p c n} {x : WindowA0ClosedEntry.State p c n} :
    WindowA0Ledger.done x.tag ↔ x.tag.reason.isSome=true := Iff.rfl

set_option linter.unusedSimpArgs false in
theorem keep {p c n H} (hn : 4≤n) (hQ : 0<2*c) {J : Fin n}
    {x₀ : Config p c n} {S : WindowA0Ledger.Scope n} {q : Trip (2*c)}
    (z : Obs p c n) (e : Fin n) (hg : Good (H:=H) x₀ S J q z) :
    Good (H:=H) x₀ S J q (tick S q z e) := by
  obtain ⟨x,m⟩ := z
  cases m with
  | routed | accepted | contact => exact True.intro
  | active d b =>
    obtain ⟨h,sh⟩ := hg
    change Ready x₀ S J H x q d b at h
    change x.gap+2<n at sh
    let y := WindowA0ClosedEntry.next S x e
    have ys : y.gap+2<n := by have K : y.gap≤x.gap := gap_mono S x e; omega
    have C := step_classify hn hQ h sh e
    change Good x₀ S J q ⟨y,nextMode q x y e (.active d b)⟩
    simp only [nextMode]
    by_cases nd : y.tag.reason.isSome=true
    · rw [if_pos nd]; exact True.intro
    rw [if_neg nd]
    dsimp only at C
    have K := C.resolve_left (fun hd => nd (done_iff.mp hd))
    by_cases hi : e=x.tag.iSlot
    · simp only [hi,if_true] at K ⊢
      subst e
      by_cases hp : geometricPay (x.tag.ledger.config x.tag.iSlot) (x.tag.ledger.config (rightNeighbor x.tag.iSlot))=true
      · simp only [cut,hp,if_true] at K ⊢
        by_cases hd : d=1
        · rw [if_pos hd]; exact True.intro
        · rw [if_neg hd]; exact ⟨K.2.resolve_left (fun R => hd R.1),ys⟩
      · simp only [cut,show geometricPay (x.tag.ledger.config x.tag.iSlot) (x.tag.ledger.config (rightNeighbor x.tag.iSlot))=false from Bool.eq_false_iff.mpr hp,Bool.false_eq_true,if_false] at K ⊢
        exact ⟨K,ys⟩
    · simp only [hi,if_false] at K ⊢
      by_cases hj : e=x.tag.jSlot
      · simp only [hj,if_true] at K ⊢
        subst e
        by_cases hd : d+1=x.gap
        · rw [if_pos hd]; cases WindowA0ReturnStep.successor q <;> exact True.intro
        · simp only [hd,if_false] at K ⊢
          exact ⟨K,ys⟩
      · simp only [hj,if_false] at K ⊢
        exact ⟨K,ys⟩

#print axioms keep
#print axioms projection

theorem terminal_sticky {p c n} (S : WindowA0Ledger.Scope n) (q : Trip (2*c))
    (z : Obs p c n) (w : List (Fin n)) (h : done (pos z)) :
    (GGTiming.runMarks (tick S q) z w).mode=z.mode := by
  induction w generalizing z with
  | nil => rfl
  | cons e w ih =>
    have E : (tick S q z e).mode=z.mode := by
      obtain ⟨x,m⟩ := z
      cases m with
      | active d b => exact h.elim
      | routed | contact | accepted => rfl
    have P : pos (tick S q z e)=pos z := by unfold pos; rw [E]
    exact (ih (tick S q z e) (P.symm ▸ h)).trans E

theorem word_good {p c n H} (hn : 4≤n) (hQ : 0<2*c) {J : Fin n}
    {x₀ : Config p c n} {S : WindowA0Ledger.Scope n} {q : Trip (2*c)}
    (z : Obs p c n) (w : List (Fin n)) (h : Good (H:=H) x₀ S J q z) :
    Good (H:=H) x₀ S J q (GGTiming.runMarks (tick S q) z w) := by
  induction w generalizing z with
  | nil => exact h
  | cons e w ih => exact ih (tick S q z e) (keep hn hQ z e h)

private theorem pos_step {p c n} (S : WindowA0Ledger.Scope n) (q : Trip (2*c))
    (x : WindowA0ClosedEntry.State p c n) (d : Nat) (b : Bool) (e : Fin n) (hp : 0<d) :
    pos (tick S q (initial x d b) e) =
      if (WindowA0ClosedEntry.next S x e).tag.reason.isSome then .accepted
      else if e=x.tag.iSlot then
        if geometricPay (x.tag.ledger.config e) (x.tag.ledger.config (rightNeighbor e)) then
          locate (d-1) false
        else locate d b
      else if e=x.tag.jSlot then
        if d+1=x.gap then .accepted else locate d b
      else locate (if e=liftedSite (cut x).top d then d+1 else d)
        (if e=RearTrace.predecessor x.tag.iSlot then true else b) := by
  change pos ⟨WindowA0ClosedEntry.next S x e,nextMode q x (WindowA0ClosedEntry.next S x e) e (.active d b)⟩ = _
  simp only [nextMode]
  by_cases hd : (WindowA0ClosedEntry.next S x e).tag.reason.isSome=true
  · simp only [if_pos hd]; rfl
  simp only [if_neg hd]
  by_cases hi : e=x.tag.iSlot
  · simp only [if_pos hi]
    by_cases hpay : geometricPay (x.tag.ledger.config e) (x.tag.ledger.config (rightNeighbor e))=true
    · simp only [if_pos hpay]
      by_cases h₁ : d=1
      · simp only [if_pos h₁,locate,show d-1=0 by omega,if_true]; rfl
      · simp only [if_neg h₁,locate,show d-1≠0 by omega,if_false]; rfl
    · simp only [if_neg hpay]
      simp only [locate,if_neg (show d≠0 by omega)]
      rfl
  simp only [if_neg hi]
  by_cases hj : e=x.tag.jSlot
  · simp only [if_pos hj]
    by_cases hh : d+1=x.gap
    · simp only [if_pos hh]
      cases WindowA0ReturnStep.successor q <;> rfl
    · simp only [if_neg hh,locate,if_neg (show d≠0 by omega)]
      rfl
  simp only [if_neg hj,locate,if_neg (show (if e=liftedSite (cut x).top d then d+1 else d)≠0 by split <;> omega)]
  rfl


private theorem labels {p c n H} {J : Fin n} {x₀ : Config p c n}
    {S : WindowA0Ledger.Scope n} {q : Trip (2*c)} {x : WindowA0ClosedEntry.State p c n}
    {d : Nat} {b : Bool} (h : Ready x₀ S J H x q d b) (short : x.gap+2<n) :
    let r := liftedSite (cut x).top d
    let f := RearTrace.predecessor x.tag.iSlot
    r≠f ∧ r≠x.tag.iSlot ∧ f≠x.tag.iSlot ∧ f≠x.tag.jSlot ∧
      (r=x.tag.jSlot ↔ d+1=x.gap) := by
  dsimp only
  let a := cut x
  let f := RearTrace.predecessor x.tag.iSlot
  have i : GGStage.incoming a.top 0=x.tag.iSlot := by
    apply FreshSeparation.succ_inj
    rw [GGStage.incoming_right,liftedSite_zero]; rfl
  have R := actual_labels a.top d h.positive (by have := h.shape.1; omega)
  dsimp only at R
  rw [i] at R
  obtain ⟨old,_,jr⟩ := h.admitted.resolve_left (by simp [WindowA0Ledger.done,h.running])
  have jf : liftedSite a.top a.gap=J := old.fixedRight
  have ends : liftedSite f 2=a.top := by
    rw [liftedSite_succ,liftedSite_succ,liftedSite_zero,RearTrace.right_predecessor]; rfl
  refine ⟨R.1,R.2,?_,?_,?_⟩
  · intro E
    have H : liftedSite f 0=liftedSite f 1 := by
      rw [liftedSite_zero,liftedSite_succ,liftedSite_zero,RearTrace.right_predecessor]
      exact E
    have := liftedSite_inj f (show 0<n by omega) (show 1<n by omega) H
    omega
  · intro E
    have P := congrArg rightNeighbor E
    rw [RearTrace.right_predecessor,jr] at P
    have T : liftedSite a.top (a.gap+1)=a.top := by
      rw [liftedSite_succ,jf,←P]; rfl
    have sh : a.gap+2<n := short
    have := liftedSite_inj a.top (show a.gap+1<n by omega) (show 0<n by omega)
      (T.trans (liftedSite_zero _).symm)
    omega
  · constructor
    · intro E
      have Z := congrArg rightNeighbor E
      rw [←liftedSite_succ,jr,←jf] at Z
      have sh : a.gap+2<n := short
      have dl : d<a.gap := h.shape.1
      exact liftedSite_inj a.top (by omega) (by omega) Z
    · intro E
      apply FreshSeparation.succ_inj
      rw [←liftedSite_succ,E,jr]; exact jf

private noncomputable def initial_events {p c n H} {J : Fin n} {x₀ : Config p c n}
    {S : WindowA0Ledger.Scope n} {q : Trip (2*c)} {x : WindowA0ClosedEntry.State p c n}
    {d : Nat} {b : Bool} (h : Ready x₀ S J H x q d b) (short : x.gap+2<n) :
    LocalEvents (H:=2*(H+1)) (tick S q) pos (initial x d b) (exponent 0 d b) := by
  let r := liftedSite (cut x).top d
  let f := RearTrace.predecessor x.tag.iSlot
  let i := x.tag.iSlot
  obtain ⟨RF,RI,FI,FJ,RJ⟩ := labels h short
  have rf : r≠f := RF
  have ri : r≠x.tag.iSlot := RI
  have fi : f≠x.tag.iSlot := FI
  have fj : f≠x.tag.jSlot := FJ
  have rj : r=x.tag.jSlot ↔ d+1=x.gap := RJ
  have hp := h.positive
  have cap : d+1≤H := by
    have L := (h.admitted.resolve_left (by simp [WindowA0Ledger.done,h.running])).1.bounded
    change x.gap≤H at L
    have := h.shape.1
    omega
  apply event_kernel (tick S q) pos (initial x d b) r f i rf ri d hp b (by omega)
  · rw [pos_step S q x d b r hp]
    by_cases E : (WindowA0ClosedEntry.next S x r).tag.reason.isSome=true
    · exact .inl (if_pos E)
    simp only [if_neg E,if_neg ri]
    by_cases K : r=x.tag.jSlot
    · exact .inl (by rw [if_pos K,if_pos (rj.mp K)])
    · have RR : r=liftedSite (cut x).top d := rfl
      have FF : r≠RearTrace.predecessor x.tag.iSlot := rf
      exact .inr (by simp only [if_neg K,if_pos RR,if_neg FF])
  · intro _
    rw [pos_step S q x d b f hp]
    by_cases E : (WindowA0ClosedEntry.next S x f).tag.reason.isSome=true
    · exact .inl (if_pos E)
    · have F : f=RearTrace.predecessor x.tag.iSlot := rfl
      have NR : f≠liftedSite (cut x).top d := Ne.symm rf
      exact .inr (by simp only [if_neg E,if_neg fi,if_neg fj,if_neg NR,if_pos F])
  · intro _
    rw [pos_step S q x d b i hp]
    by_cases E : (WindowA0ClosedEntry.next S x i).tag.reason.isSome=true
    · exact .inl (if_pos E)
    · have ii : i=x.tag.iSlot := rfl
      simp only [if_neg E,if_pos ii]
      split
      · exact .inr (.inr rfl)
      · subst b
        exact .inr (.inl rfl)
  · intro e ner nea
    rw [pos_step S q x d b e hp]
    by_cases E : (WindowA0ClosedEntry.next S x e).tag.reason.isSome=true
    · exact .inl (if_pos E)
    simp only [if_neg E]
    by_cases K : e=x.tag.iSlot
    · have B : b=false := by
        cases b with
        | false => rfl
        | true => exact (nea K).elim
      subst b
      have unpaid := WindowA0ReturnStep.ready_no_pay h
      subst e
      exact .inr (by simp only [if_true,unpaid,Bool.false_eq_true,if_false])
    simp only [if_neg K]
    by_cases V : e=x.tag.jSlot
    · have N : d+1≠x.gap := fun hD => ner (V.trans (rj.mpr hD).symm)
      exact .inr (by simp only [if_pos V,if_neg N])
    have NR : e≠liftedSite (cut x).top d := ner
    simp only [if_neg V,if_neg NR]
    apply Or.inr
    cases b with
    | false =>
      have fa : e≠RearTrace.predecessor x.tag.iSlot := nea
      rw [if_neg fa]
    | true => split <;> rfl

/-- At every horizon, the exact original-word first-contact mass is
at most two thirds. No conditioning on the guard or return service. -/
theorem contact_bound {p c n H} (hn : 4≤n) (hQ : 0<2*c) {J : Fin n} {x₀ : Config p c n}
    {S : WindowA0Ledger.Scope n} {q : Trip (2*c)} {x : WindowA0ClosedEntry.State p c n}
    {d : Nat} {b : Bool} (h : Ready x₀ S J H x q d b) (short : x.gap+2<n) (t : Nat) :
    3*TripleRenewal.terminalMass (tick S q) (fun z => done (pos z))
      (fun z => pos z=.contact) t (initial x d b)≤2*n^t := by
  refine contact_of_events (H:=2*(H+1)) (tick S q) pos (Good (H:=H) x₀ S J q)
    (fun z e _ hg _ => keep hn hQ z e hg) ?_ t (initial x d b) ⟨h,short⟩ rfl
  intro z k hg hk
  obtain ⟨y,m⟩ := z
  cases m with
  | contact | routed | accepted => cases hk
  | active d b =>
    obtain ⟨hr,hs⟩ := hg
    have K : exponent 0 d b=k := Position.active.inj hk
    subst k
    exact ⟨initial_events hr hs⟩

#print axioms initial_events
#print axioms contact_bound

def work {p c n} (z : Obs p c n) : Nat :=
  match z.mode with
  | .active d _ => z.physical.gap-d
  | _ => 0

private theorem raw_work {p c n H} {J : Fin n} {x₀ : Config p c n}
    {S : WindowA0Ledger.Scope n} {q : Trip (2*c)} {x : WindowA0ClosedEntry.State p c n}
    {d : Nat} {b : Bool} (h : Ready x₀ S J H x q d b) (short : x.gap+2<n) (e : Fin n) :
    work (tick S q (initial x d b) e) +
      (if e=liftedSite (cut x).top d then 1 else 0) ≤ x.gap-d := by
  let r := liftedSite (cut x).top d
  let y := WindowA0ClosedEntry.next S x e
  have dl : d<x.gap := h.shape.1
  have gm : y.gap≤x.gap := gap_mono S x e
  have hp := h.positive
  obtain ⟨_,RN,_,_,RJ⟩ := labels h short
  have rn : r≠x.tag.iSlot := RN
  have rj : r=x.tag.jSlot ↔ d+1=x.gap := RJ
  change work ⟨y,nextMode q x y e (.active d b)⟩ + (if e=r then 1 else 0) ≤ x.gap-d
  simp only [nextMode]
  by_cases hd : y.tag.reason.isSome=true
  · rw [if_pos hd]
    change 0+(if e=r then 1 else 0)≤x.gap-d
    split <;> omega
  rw [if_neg hd]
  by_cases hi : e=x.tag.iSlot
  · have ne : e≠r := fun E => rn (E.symm.trans hi)
    rw [if_pos hi,if_neg ne]
    by_cases pay : geometricPay (x.tag.ledger.config e) (x.tag.ledger.config (rightNeighbor e))=true
    · rw [if_pos pay]
      by_cases h₁ : d=1
      · rw [if_pos h₁]
        exact Nat.zero_le _
      · rw [if_neg h₁]
        have shifted : y.gap=x.gap-1 := by
          have M : WindowFourHeadTrace.moves x.tag.ledger e x.tag.iSlot := by
            exact ⟨hi,pay⟩
          change (if y.tag.reason.isSome then x.gap
            else x.gap-(if WindowFourHeadTrace.moves x.tag.ledger e x.tag.iSlot then 1 else 0))=_
          rw [if_neg hd,if_pos M]
        change y.gap-(d-1)+0≤x.gap-d
        omega
    · rw [if_neg pay]
      change y.gap-d+0≤x.gap-d
      omega
  rw [if_neg hi]
  by_cases hj : e=x.tag.jSlot
  · rw [if_pos hj]
    by_cases E : d+1=x.gap
    · rw [if_pos E]
      cases WindowA0ReturnStep.successor q <;>
        change 0+(if e=r then 1 else 0)≤x.gap-d <;> split <;> omega
    · have ne : e≠r := fun A => E (rj.mp (A.symm.trans hj))
      rw [if_neg E,if_neg ne]
      change y.gap-d+0≤x.gap-d
      omega
  rw [if_neg hj]
  change y.gap-(if e=r then d+1 else d)+(if e=r then 1 else 0)≤x.gap-d
  split <;> omega

/-- Exact expected number of raw marks to first contact, accepted
return, or routed exit. Bound is the actual retained distance to J. -/
theorem mean {p c n H} (hn : 4≤n) (hQ : 0<2*c) {J : Fin n} {x₀ : Config p c n}
    {S : WindowA0Ledger.Scope n} {q : Trip (2*c)} {x : WindowA0ClosedEntry.State p c n}
    {d : Nat} {b : Bool} (h : Ready x₀ S J H x q d b) (short : x.gap+2<n) :
    IIDExpectedHittingTimeAtMost (tick S q) (fun z => done (pos z))
      (initial x d b) (n*(x.gap-d)) := by
  apply nominated_mean (tick S q) (fun z => done (pos z)) (Good (H:=H) x₀ S J q) work
    (fun z e hg _ => keep hn hQ z e hg) _ (initial x d b) ⟨h,short⟩
  intro z hz hd
  obtain ⟨y,m⟩ := z
  cases m with
  | contact | routed | accepted => exact (hd trivial).elim
  | active d b =>
    obtain ⟨hr,hs⟩ := hz
    let r := liftedSite (cut y).top d
    refine ⟨⟨r,?_⟩,?_⟩
    · have A := raw_work hr hs r
      have E : r=liftedSite (cut y).top d := rfl
      change work (tick S q (initial y d b) r)+1≤y.gap-d
      simpa only [if_pos E] using A
    · intro e
      have A := raw_work hr hs e
      change work (tick S q (initial y d b) e) ≤ y.gap-d
      exact Nat.le_trans (Nat.le_add_right _ _) A

#print axioms mean
end L4.WindowA0ReturnWord
