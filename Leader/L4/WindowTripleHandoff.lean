import Leader.L4.WindowTripleEntry
import Leader.L4.WindowFrontDone
import Leader.L4.WindowFiveStages

/-! Synchronize the scoped certified-triple clock with the actual
joined Ownership front; the selected death installs its named protected
cursor on the very mark that stops the triple clock. -/
namespace L4.WindowTripleHandoff
open SevenTagCharge WindowLocal WindowScopedRace WindowOwnership
open WindowLatch WindowProtectedOuter WindowFiveStages RootedAssembly

noncomputable def joined {p c n} {x : Config p c n} {g : List (Fin n)}
    (hp : 2≤p) (hc : 12≤c) (hn : 4≤n) :
    WindowLatch.Cursor (Front x g) x g → Fin n → WindowLatch.Cursor (Front x g) x g :=
  joinedNext (front hn (WindowOwnership.decide hp hc hn))

def AtTriple {p c n} {x : Config p c n} {g : List (Fin n)}
    (cert : List (Fin n)) (s : Front x g) : Prop :=
  ∃ P, s.mode=.owned P ∧ P.cert=cert ∧ cert.length=3

def RewardAt {p c n} {x : Config p c n} {g : List (Fin n)} (a : Fin n)
    (z : WindowLatch.Cursor (Front x g) x g) : Prop :=
  ∃ s proof, z=.inl s ∧ s.mode=.reward a proof

private theorem target_none {p c n} {z : Ledger p c n} {g : List (Fin n)}
    (P : Progress z g) (h : P.cert.length=3) : P.target=none := by
  simp [Progress.target,h]

theorem step_agrees {p c n} {x : Config p c n} {g cert : List (Fin n)}
    (hp : 2≤p) (hc : 12≤c) (hn : 4≤n) (s : Front x g)
    (h : AtTriple cert s) (e : Fin n) :
    let z := joined hp hc hn (.inl s) e
    let y := cursorNext g cert (s.ledger,false) e
    project Front.ledger z=y.1 ∧
      match route g cert none s.ledger e with
      | .keep => y.2=false ∧ ∃ f, z=.inl f ∧ AtTriple cert f
      | .reward a => y.2=true ∧ RewardAt a z
      | .prefixDeath a post => y.2=true ∧ ∃ k : Named x g s.ledger e,
          k.victim=a ∧ k.post=post ∧ z=.inr (startRunning (k.entry hn))
      | .targetBirth _ _ => False := by
  refine ⟨step_projects hn (WindowOwnership.decide hp hc hn) (.inl s) e,?_⟩
  obtain ⟨old,hM,hcert,h3⟩ := h
  obtain ⟨ledger,valid,quiet,m⟩ := s
  change m=.owned old at hM
  rw [hM]
  subst cert
  have target : old.target=none := target_none old h3
  cases hr : route g old.cert none ledger e with
  | keep =>
    have R : route g old.cert old.target ledger e=.keep := target ▸ hr
    let f : Front x g := ⟨advance ledger e,valid_step hn ledger x e valid,
      RootedFresh.quiet_step ledger.config e hp hc hn quiet,.owned (old.onKeep hn valid e R)⟩
    refine ⟨by simp [cursorNext,hr],f,?_,⟨old.onKeep hn valid e R,rfl,rfl,h3⟩⟩
    have D : WindowOwnership.decide hp hc hn ⟨ledger,valid,quiet,.owned old⟩ e =
        .ordinary f rfl := by
      unfold WindowOwnership.decide
      dsimp only
      split
      · rfl
      all_goals rename_i E; rw [R] at E; cases E
    simp only [joined,joinedNext,front,D]
    rfl
  | reward a =>
    have R : route g old.cert old.target ledger e=.reward a := target ▸ hr
    obtain ⟨lost,mem⟩ := (reward_iff g old.cert old.target ledger e a).mp R
    have loss : a∈(advance ledger e).losses ∧ a∈g :=
      ⟨List.mem_append_left _ (by simp [lost]),mem⟩
    let f : Front x g := ⟨advance ledger e,valid_step hn ledger x e valid,
      RootedFresh.quiet_step ledger.config e hp hc hn quiet,.reward a loss⟩
    refine ⟨by simp [cursorNext,hr],f,loss,?_,rfl⟩
    have D : WindowOwnership.decide hp hc hn ⟨ledger,valid,quiet,.owned old⟩ e =
        .ordinary f rfl := by
      unfold WindowOwnership.decide
      dsimp only
      split
      all_goals first | rfl | (rename_i E; rw [R] at E; cases E <;> rfl)
    simp only [joined,joinedNext,front,D]
    rfl
  | prefixDeath a post =>
    have R : route g old.cert old.target ledger e=.prefixDeath a post := target ▸ hr
    let k := Classical.choice (WindowNamedFront.named_of_route hn ledger g old.cert old.target
      e a post valid quiet old.owned.contained R)
    refine ⟨by simp [cursorNext,hr],k.val,k.property.1,k.property.2,?_⟩
    have D : WindowOwnership.decide hp hc hn ⟨ledger,valid,quiet,.owned old⟩ e =
        .kill k.val := by
      unfold WindowOwnership.decide
      dsimp only
      split
      all_goals first | rfl | (rename_i E; rw [R] at E; cases E <;> rfl)
    simp only [joined,joinedNext,front,D]
    rfl
  | targetBirth a post =>
    have bad := (birth_inv ledger g old.cert none e a post hr).2.2.1
    cases bad

private theorem ledger_word {p c n} (g cert : List (Fin n)) (z : WindowScopedRace.Cursor p c n)
    (w : Word n) :
    (GGTiming.runMarks (cursorNext g cert) z w).1=observe z.1 w := by
  induction w generalizing z with
  | nil => rfl
  | cons e w ih => exact ih (cursorNext g cert z e)

/-- The first scoped clock stop is the joined front's exact reward or its
own named protected entry. No protected padding has yet run. -/
theorem first_stop {p c n} {x : Config p c n} {g cert : List (Fin n)}
    (hp : 2≤p) (hc : 12≤c) (hn : 4≤n) (s : Front x g)
    (h : AtTriple cert s) (w : Word n)
    (first : FirstExit (fun v => WindowScopedRace.Cursor.exit
      (GGTiming.runMarks (cursorNext g cert) (s.ledger,false) v)) w) :
    let q := GGTiming.runMarks (joined hp hc hn) (.inl s) w
    project Front.ledger q=(GGTiming.runMarks (cursorNext g cert) (s.ledger,false) w).1 ∧
    ∃ v e f, w=v++[e] ∧
      GGTiming.runMarks (joined hp hc hn) (.inl s) v=.inl f ∧ AtTriple cert f ∧
      ((∃ a, route g cert none f.ledger e=.reward a ∧ RewardAt a q) ∨
        ∃ (a post : Fin n) (k : Named x g f.ledger e),
          route g cert none f.ledger e=.prefixDeath a post ∧
          k.victim=a ∧ k.post=post ∧ q=.inr (startRunning (k.entry hn))) := by
  induction w generalizing s with
  | nil => exact False.elim (Bool.noConfusion first.2)
  | cons e w ih =>
    let y := cursorNext g cert (s.ledger,false) e
    let q := joined hp hc hn (.inl s) e
    obtain ⟨L,R⟩ := step_agrees hp hc hn s h e
    have agree : project Front.ledger q=y.1 := L
    have finalLedger : project Front.ledger (GGTiming.runMarks (joined hp hc hn) (.inl s) (e::w))=
        (GGTiming.runMarks (cursorNext g cert) (s.ledger,false) (e::w)).1 := by
      rw [ledger_word]
      have same (q : WindowLatch.Cursor (Front x g) x g) (w : Word n) :
          GGTiming.runMarks (joined hp hc hn) q w=
            replay (joinedNext (front hn (WindowOwnership.decide hp hc hn))) q w := by
        induction w generalizing q with
        | nil => rfl
        | cons e es ih => exact ih (joined hp hc hn q e)
      rw [same]
      exact replay_projects hn (WindowOwnership.decide hp hc hn) (.inl s) (e::w)
    refine ⟨finalLedger,?_⟩
    have terminal (out : y.2=true) : w=[] := by
      cases w with
      | nil => rfl
      | cons b t =>
        have no := first.1 1 (by simp)
        exact (no out).elim
    cases E : route g cert none s.ledger e with
    | keep =>
      rw [E] at R
      obtain ⟨U,f,eq,ht⟩ := R
      have eq' : q=.inl f := eq
      have A : y=(f.ledger,false) := Prod.ext (agree.symm.trans (congrArg (project Front.ledger) eq)) U
      have ffirst : FirstExit (fun v => WindowScopedRace.Cursor.exit
          (GGTiming.runMarks (cursorNext g cert) (f.ledger,false) v)) w := by
        refine ⟨?_,?_⟩
        · intro k hk
          have no := first.1 (k+1) (by simp; omega)
          change ¬WindowScopedRace.Cursor.exit (GGTiming.runMarks (cursorNext g cert) y (w.take k)) at no
          simpa only [A] using no
        · have yes := first.2
          change WindowScopedRace.Cursor.exit (GGTiming.runMarks (cursorNext g cert) y w) at yes
          simpa only [A] using yes
      obtain ⟨_,v,b,t,ew,cut,hT,stop⟩ := ih f ht ffirst
      refine ⟨e::v,b,t,by simp [ew],?_,hT,?_⟩
      · change GGTiming.runMarks (joined hp hc hn) q v=.inl t
        rw [eq']; exact cut
      · change _ ∨ _ at stop
        simp only [GGTiming.runMarks,show joined hp hc hn (.inl s) e=q from rfl,eq']
        exact stop
    | reward a =>
      rw [E] at R
      have U := terminal R.1
      subst w
      exact ⟨[],e,s,rfl,rfl,h,.inl ⟨a,E,R.2⟩⟩
    | prefixDeath a post =>
      rw [E] at R
      obtain ⟨U,k,ka,kp,eq⟩ := R
      have W := terminal U
      subst w
      exact ⟨[],e,s,rfl,rfl,h,.inr ⟨a,post,k,E,ka,kp,eq⟩⟩
    | targetBirth a post =>
      rw [E] at R
      exact R.elim

end L4.WindowTripleHandoff
