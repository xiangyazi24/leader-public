import Leader.L4.WindowA0ApproachJoin

/-! Feed exact first cuts to later phases on the same raw word.
The continuation is a function of the completed prefix and can be
chosen from a proof of the physical state at that cut. -/
namespace L4.WindowA0SpliceTrial

open WindowFiveStages RootedAssembly TripleRenewal TaggedTail
open WindowA0ApproachJoin WindowA0AttemptCredit WindowA0Trial Classical

structure Check (n : Nat) where
  stop : Word n → Prop
  bad : Word n → Prop

/-- Local failure terminates immediately at the cut. A favorable cut
starts its continuation at once; a continuation can itself be ready
on the empty suffix (including a same-mark next launch). -/
def join {n : Nat} (X : Check n) (Y : Word n → Check n) : Check n :=
  ⟨splice X.stop (fun a u => X.bad a ∨ (Y a).stop u),
   splice X.stop (fun a u => X.bad a ∨ (Y a).bad u)⟩

noncomputable def joinCredit {n : Nat} (X : Check n) (Y : Word n → Check n)
    (d : Nat) (localBudget : ∀ t,
      d*terminalMass wordNext X.stop X.bad t []≤(d-1)*n^t) :
    Layer wordNext (join X Y).stop (fun w => w=[])
      (fun w => FirstExit X.stop w ∧ ¬X.bad w) d where
  localDone := X.stop
  localBad := X.bad
  live := Clean X.stop
  enter _ h := h.symm ▸ clean_nil _
  keep _ e h hs := (clean_child _ _ e).mpr ⟨h,hs⟩
  notEarly := splice_notEarly _ _
  pass _ h hs hb := ⟨⟨h,hs⟩,hb⟩
  budget _ h := h.symm ▸ localBudget

noncomputable def joinTiming {n : Nat} (X : Check n) (Y : Word n → Check n)
    (P : Nat) (localMean : IIDExpectedHittingTimeAtMost wordNext X.stop [] P) :
    TimedLayer wordNext (join X Y).stop (fun w => w=[])
      (fun w => FirstExit X.stop w ∧ ¬X.bad w) P where
  stop := X.stop
  live := Clean X.stop
  enter _ h := h.symm ▸ clean_nil _
  keep _ e h hs := (clean_child _ _ e).mpr ⟨h,hs⟩
  finish w h hs hg := ⟨⟨h,hs⟩,fun hb => hg ⟨w,[],List.append_nil w |>.symm,⟨h,hs⟩,.inl hb⟩⟩
  mean _ h := h.symm ▸ localMean

theorem join_mean {n P B : Nat} (X : Check n) (Y : Word n → Check n)
    (localMean : IIDExpectedHittingTimeAtMost wordNext X.stop [] P)
    (tailMean : ∀ a, FirstExit X.stop a → ¬X.bad a →
      IIDExpectedHittingTimeAtMost wordNext (Y a).stop [] B) :
    IIDExpectedHittingTimeAtMost wordNext (join X Y).stop [] (P+B) := by
  apply timed_compose (joinTiming X Y P localMean) _ [] rfl
  rintro a ⟨ha,hb⟩ t
  have E := rebase_cost (join X Y).stop (Y a).stop a
    (fun u => (splice_at X.stop _ a u ha).trans (by simp [hb])) t []
  rw [List.append_nil] at E
  rw [E]
  exact tailMean a ha hb t

theorem join_failure {n d D : Nat} (X : Check n) (Y : Word n → Check n)
    (hd : 0<d) (hD : 0<D)
    (localBudget : ∀ t, d*terminalMass wordNext X.stop X.bad t []≤(d-1)*n^t)
    (tailBudget : ∀ a, FirstExit X.stop a → ¬X.bad a → ∀ t,
      D*terminalMass wordNext (Y a).stop (Y a).bad t []≤(D-1)*n^t) :
    ∀ t, (d*D)*terminalMass wordNext (join X Y).stop (join X Y).bad t []≤(d*D-1)*n^t := by
  intro t
  apply product_failure wordNext _ _ _ _ (joinCredit X Y d localBudget) D hd hD _ t [] rfl
  rintro a ⟨ha,hb⟩ u
  have E := rebase_mass (join X Y).stop (join X Y).bad (Y a).stop (Y a).bad a
    (fun v => (splice_at X.stop _ a v ha).trans (by simp [hb]))
    (fun v => (splice_at X.stop _ a v ha).trans (by simp [hb])) u []
  rw [List.append_nil] at E
  rw [E]
  exact tailBudget a ha hb u

/-- Invert an actual first stop. The branch bad bit is read at its
own original cut, and a passing continuation gets the exact suffix. -/
theorem join_first {n : Nat} (X : Check n) (Y : Word n → Check n) (w : Word n)
    (hw : FirstExit (join X Y).stop w) :
    ∃ a u, w=a++u ∧ FirstExit X.stop a ∧
      ((X.bad a ∧ u=[] ∧ (join X Y).bad w) ∨
        (¬X.bad a ∧ FirstExit (Y a).stop u ∧ ((join X Y).bad w ↔ (Y a).bad u))) := by
  obtain ⟨a,u,eq,ha,hu⟩ := splice_first X.stop _ w hw
  refine ⟨a,u,eq,ha,?_⟩
  by_cases hb : X.bad a
  · have E : u=[] := by
      cases u with
      | nil => rfl
      | cons e es => exact (hu.1 0 (by simp) (.inl hb)).elim
    exact .inl ⟨hb,E,⟨a,u,eq,ha,.inl hb⟩⟩
  · exact .inr ⟨hb,⟨fun k hk h => hu.1 k hk (.inr h),hu.2.resolve_left hb⟩,by
      rw [eq]
      exact (splice_at X.stop _ a u ha).trans (by simp [hb])⟩

/-- A finite raw-word experiment with both quantitative bounds and an
exact first-stop interpretation in the original physical goal. -/
structure Verified {n : Nat} (goal : Word n → Prop) (P d : Nat) where
  check : Check n
  mean : IIDExpectedHittingTimeAtMost wordNext check.stop [] P
  mass : ∀ t, d*terminalMass wordNext check.stop check.bad t []≤(d-1)*n^t
  classify : ∀ w, FirstExit check.stop w → (check.bad w ↔ ¬goal w)

private theorem mass_first {n : Nat} (stop bad₁ bad₂ : Word n → Prop)
    (align : ∀ w, FirstExit stop w → (bad₁ w ↔ bad₂ w)) (t : Nat)
    (w : Word n) (hc : Clean stop w) :
    terminalMass wordNext stop bad₁ t w=terminalMass wordNext stop bad₂ t w := by
  induction t generalizing w with
  | zero =>
    by_cases hh : stop w
    · simp [terminalMass,hh,align w ⟨hc,hh⟩]
    · simp [terminalMass,hh]
  | succ t ih =>
    by_cases hh : stop w
    · simp [terminalMass,hh,align w ⟨hc,hh⟩]
    · simp only [terminalMass,hh,if_false]
      apply congrArg sumEdge
      funext e
      exact ih (wordNext w e) ((clean_child stop w e).mpr ⟨hc,hh⟩)

theorem Verified.goalMass {n P d : Nat} {goal : Word n → Prop} (V : Verified goal P d)
    (t : Nat) : d*terminalMass wordNext V.check.stop (fun w => ¬goal w) t []≤(d-1)*n^t := by
  rw [←mass_first V.check.stop V.check.bad (fun w => ¬goal w) V.classify t [] (clean_nil _)]
  exact V.mass t

def acceptNow (n : Nat) : Check n := ⟨fun _ => True,fun _ => False⟩

def acceptNowCert {n P d : Nat} (goal : Word n → Prop) (h : goal []) :
    Verified goal P d where
  check := acceptNow n
  mean := fun t => by
    rw [iidHitCost_of_target _ _ _ (show (acceptNow n).stop [] from trivial)]
    exact Nat.zero_le _
  mass := fun t => by cases t <;> simp [acceptNow,terminalMass]
  classify := by
    intro w hw
    have he : w=[] := by
      cases w with
      | nil => rfl
      | cons e es => exact (hw.1 0 (by simp) True.intro).elim
    subst w
    simp [acceptNow,h]

/-- Stitch a certified continuation chosen at a favorable physical cut.
Its certification is only needed at genuine first stops. -/
noncomputable def verifiedJoin {n P B d D : Nat} (goal : Word n → Prop) (X : Check n)
    (hd : 0<d) (hD : 0<D)
    (localMean : IIDExpectedHittingTimeAtMost wordNext X.stop [] P)
    (localBudget : ∀ t, d*terminalMass wordNext X.stop X.bad t []≤(d-1)*n^t)
    (localBadSound : ∀ a, FirstExit X.stop a → X.bad a → ¬goal a)
    (Y : ∀ a, FirstExit X.stop a → ¬X.bad a → Verified (fun u => goal (a++u)) B D) :
    Verified goal (P+B) (d*D) := by
  let out (a : Word n) : Check n :=
    if ha : FirstExit X.stop a then
      if hb : ¬X.bad a then (Y a ha hb).check else acceptNow n
    else acceptNow n
  have out_eq (a : Word n) (ha : FirstExit X.stop a) (hb : ¬X.bad a) :
      out a=(Y a ha hb).check := by simp [out,ha,hb]
  refine ⟨join X out, ?_, ?_, ?_⟩
  · exact join_mean X out localMean (fun a ha hb => out_eq a ha hb ▸ (Y a ha hb).mean)
  · apply join_failure X out hd hD localBudget
    intro a ha hb
    rw [out_eq a ha hb]
    exact (Y a ha hb).mass
  · intro w hw
    obtain ⟨a,u,E,ha,hb|hg⟩ := join_first X out w hw
    · obtain ⟨ab,eu,H⟩ := hb
      subst u
      refine iff_of_true H ?_
      simpa [E] using localBadSound a ha ab
    · obtain ⟨ab,stop,bad⟩ := hg
      rw [out_eq a ha ab] at stop bad
      exact bad.trans (E ▸ (Y a ha ab).classify u stop)

/-- All earlier exits stay on their physical word; these obligations
concern just the favorable or spoiled first stop of one leg. -/
structure LegFamily {α : Type} {n : Nat} (step : α → Fin n → α)
    (goal : α → Prop) (start : Nat → α → Prop) (K P d : Nat) where
  cut : ∀ j x, j<K → start j x → Check n
  mean : ∀ j x (hj : j<K) (hx : start j x),
    IIDExpectedHittingTimeAtMost wordNext (cut j x hj hx).stop [] P
  mass : ∀ j x (hj : j<K) (hx : start j x) t,
    d*terminalMass wordNext (cut j x hj hx).stop (cut j x hj hx).bad t []≤(d-1)*n^t
  bad : ∀ j x (hj : j<K) (hx : start j x) w,
    FirstExit (cut j x hj hx).stop w → (cut j x hj hx).bad w →
      ¬goal (GGTiming.runMarks step x w)
  pass : ∀ j x (hj : j<K) (hx : start j x) w,
    FirstExit (cut j x hj hx).stop w → ¬(cut j x hj hx).bad w →
      goal (GGTiming.runMarks step x w) ∨ start (j+1) (GGTiming.runMarks step x w)
  last : ∀ x, start K x → goal x

/-- Assemble the exact remaining ordinal count, using a uniform
per-leg probability and clock but no independence at handoffs. -/
noncomputable def certifyLegs {α : Type} {n K P d : Nat} {step : α → Fin n → α}
    {goal : α → Prop} {start : Nat → α → Prop}
    (L : LegFamily step goal start K P d) (hd : 0<d) (m : Nat) :
    ∀ j, j+m=K → ∀ x, start j x →
    Verified (fun w => goal (GGTiming.runMarks step x w)) (m*P) (d^m) := by
  induction m with
  | zero =>
    intro j hj x hx
    have E : j=K := by omega
    exact acceptNowCert _ (L.last x (E ▸ hx))
  | succ m ih =>
    intro j hj x hx
    have before : j<K := by omega
    have after : j+1+m=K := by omega
    let X := L.cut j x before hx
    have C := verifiedJoin (fun w => goal (GGTiming.runMarks step x w)) X
      hd (Nat.pow_pos hd) (L.mean j x before hx) (L.mass j x before hx) (L.bad j x before hx)
      (fun a ah ab => by
        rw [show (fun u => goal (GGTiming.runMarks step x (a++u))) =
            (fun u => goal (GGTiming.runMarks step (GGTiming.runMarks step x a) u)) by
              funext u; rw [GGTiming.runMarks_append]]
        by_cases hg : goal (GGTiming.runMarks step x a)
        · exact acceptNowCert (P:=m*P) _ hg
        · exact ih (j+1) after _ ((L.pass j x before hx a ah ab).resolve_left hg))
    simpa only [Nat.succ_mul,Nat.add_comm,Nat.pow_succ'] using C

end L4.WindowA0SpliceTrial
