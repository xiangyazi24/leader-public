import Leader.L4.WindowA0FiniteDAG
import Leader.L4.WindowA0MaskedTrace

/-! A paused physical stock-preparation tape and its finite path clock
read the same raw marks. Pausing the clock does not freeze the ring. -/
namespace L4.WindowA0PausedDAG
open QueueDAG GGTiming

structure GatedRules {α : Type} {n : Nat} (next : α → Fin n → α)
    (good : α → Prop) (enabled : α → Bool) (height : α → Nat → Nat)
    (m P : Nat) (edge : Nat → Fin n) : Prop where
  mono : ∀ x e i, good x → i≤m → height x i≤height (next x e) i
  commit : ∀ x i k, good x → enabled x = true → i≤m → 0<k → k≤P →
    (0<i → k≤height x (i-1)) →
    (i<m → k-1≤height x (i+1)) →
    k≤height (next x (edge i)) i

theorem gated_sound {α : Type} {n : Nat} {next : α → Fin n → α}
    {good : α → Prop} {enabled : α → Bool} {height : α → Nat → Nat}
    {m P : Nat} {edge : Nat → Fin n}
    (rule : GatedRules next good enabled height m P edge) (fuel i k : Nat)
    (hi : i≤m) (hkP : k≤P) (hfuel : 2*k+i≤fuel) :
    GatedSound next good enabled (fifoTree m edge fuel i k) (fun x => k≤height x i) := by
  induction fuel generalizing i k with
  | zero =>
    have hk : k=0 := by omega
    subst k
    exact .done _ (fun _ _ => Nat.zero_le _)
  | succ fuel ih =>
    by_cases hk : k=0
    · subst k
      simp only [fifoTree,if_true]
      exact .done _ (fun _ _ => Nat.zero_le _)
    · simp only [fifoTree,hk,if_false]
      apply GatedSound.fork _ _ _ (fun x => 0<i → k≤height x (i-1))
        (fun x => i<m → k-1≤height x (i+1)) _
      · by_cases he : i=0
        · simp only [he,if_true]
          exact .done _ (by omega)
        · rw [if_neg he]
          have H := ih (i-1) k (by omega) hkP (by omega)
          simpa only [show 0<i by omega,true_implies] using H
      · by_cases he : i<m
        · rw [if_pos he]
          have H := ih (i+1) (k-1) (by omega) (by omega) (by omega)
          simpa only [he,true_implies] using H
        · rw [if_neg he]
          exact .done _ (by omega)
      · exact fun x e hx hp => Nat.le_trans hp (rule.mono x e i hx hi)
      · exact fun x hx he => rule.commit x i k hx he hi (by omega) hkP

theorem gated_outlet {α : Type} {n : Nat} {next : α → Fin n → α}
    {good : α → Prop} {enabled : α → Bool} {height : α → Nat → Nat}
    {m P : Nat} {edge : Nat → Fin n}
    (rule : GatedRules next good enabled height m P edge)
    (keep : ∀ x e, good x → good (next x e)) (x : α) (hx : good x)
    (w : List (Fin n)) (hw : finished (runMarks advance (outletPaths m edge P)
      (servedMarks next enabled x w))) :
    P≤height (runMarks next x w) m :=
  (gated_sound rule (2*P+m) m P (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)).of_paths
    keep x hx w hw

open WindowA0StockDrain in
def canServe {p c n : Nat} (base : Fin n) (z : Cursor p c n) : Bool :=
  !(z.ledger.config (GGStage.incoming base z.heads.j)).stock

open WindowA0StockDrain in
theorem actual_paths_are_gated {p c n : Nat} (g : List (Fin n)) (a b base : Fin n)
    (z : Cursor p c n) (paths : PathList n) (w : List (Fin n)) :
    drainPaths g a b base z paths w =
      runMarks advance paths (servedMarks (next g a b base) (canServe base) z w) := by
  induction w generalizing z paths with
  | nil => rfl
  | cons e w ih =>
    cases h : (z.ledger.config (GGStage.incoming base z.heads.j)).stock <;>
      simp [drainPaths,servedMarks,canServe,h,runMarks,ih]

open WindowA0StockDrain in
/-- On the actual paused observer, the finite budget no longer assumes any
global DAG-completion statement. It suffices to give one closed physical
cut representation and certify monotonicity on all marks and outlet service
only when the old door has no reservation. -/
theorem actual_completion_of_gated {p c n : Nat} (g : List (Fin n)) (a b base : Fin n)
    (z : Cursor p c n) (m P : Nat) (edge : Nat → Fin n)
    (good : Cursor p c n → Prop) (height : Cursor p c n → Nat → Nat)
    (rules : GatedRules (next g a b base) good (canServe base) height m P edge)
    (keep : ∀ x e, good x → good (next g a b base x e)) (hz : good z)
    (discharge : ∀ x, good x → ¬pending base x → P≤height x m → drained base x)
    (w : List (Fin n)) (hp : ¬pending base (tape g a b base z w))
    (hw : finished (drainPaths g a b base z (outletPaths m edge P) w)) :
    drained base (tape g a b base z w) := by
  rw [actual_paths_are_gated] at hw
  have hgood : ∀ x, good x → good (tape g a b base x w) := by
    clear hp hw
    induction w with
    | nil => exact fun _ h => h
    | cons e w ih => intro x hx; exact ih _ (keep x e hx)
  exact discharge _ (hgood _ hz) hp (gated_outlet rules keep z hz w hw)

open WindowA0StockDrain in
/-- Lift commit/monotonicity to a proof observer with auxiliary inventory.
Projection really runs the old physical cursor on every raw mark. -/
theorem actual_completion_with_observer {α : Type} {p c n : Nat}
    (g : List (Fin n)) (a b base : Fin n) (z : Cursor p c n)
    (m P : Nat) (edge : Nat → Fin n) (observer : α → Fin n → α)
    (project : α → Cursor p c n) (seed : α) (hseed : project seed=z)
    (commute : ∀ x e, project (observer x e)=next g a b base (project x) e)
    (good : α → Prop) (height : α → Nat → Nat)
    (rules : GatedRules observer good (fun x => canServe base (project x)) height m P edge)
    (keep : ∀ x e, good x → good (observer x e)) (hz : good seed)
    (discharge : ∀ x, good x → ¬pending base (project x) → P≤height x m →
      drained base (project x))
    (w : List (Fin n)) (hp : ¬pending base (tape g a b base z w))
    (hw : finished (drainPaths g a b base z (outletPaths m edge P) w)) :
    drained base (tape g a b base z w) := by
  have hproj (w : List (Fin n)) (x : α) :
      project (runMarks observer x w)=tape g a b base (project x) w := by
    induction w generalizing x with
    | nil => rfl
    | cons e w ih =>
      change project (runMarks observer (observer x e) w)=
        tape g a b base (next g a b base (project x) e) w
      rw [ih,commute]
  have hmarks (w : List (Fin n)) (x : α) :
      servedMarks observer (fun y => canServe base (project y)) x w =
        servedMarks (next g a b base) (canServe base) (project x) w := by
    induction w generalizing x with
    | nil => rfl
    | cons e w ih =>
      simp only [servedMarks,ih,commute]
  have hkeep (w : List (Fin n)) (x : α) (hx : good x) :
      good (runMarks observer x w) := by
    induction w generalizing x with
    | nil => exact hx
    | cons e w ih => exact ih _ (keep x e hx)
  have hcut : project (runMarks observer seed w)=tape g a b base z w :=
    (hproj w seed).trans (congrArg (fun v => tape g a b base v w) hseed)
  have hw' : finished (runMarks advance (outletPaths m edge P)
      (servedMarks observer (fun y => canServe base (project y)) seed w)) := by
    rw [hmarks,hseed,←actual_paths_are_gated]
    exact hw
  rw [←hcut] at hp ⊢
  exact discharge _ (hkeep w seed hz) hp (gated_outlet rules keep seed hz w hw')

open FIFOCompare WindowA0MaskedTrace WindowA0Masked in
/-- Conservation plus an outlet threshold discharges all actual retained
stock, once the physical reservation at the old head is absent. -/
theorem drained_of_outlet {p c n : Nat} (x : Config p c n) (base : Fin n)
    (m P : Nat) (q : WindowA0MaskedTrace.Cursor)
    (good : Good x base (m+1) q)
    (unpaused : (x (liftedSite base (q.J-1))).stock=false)
    (conserved : cuts (m+1) (stock x base q.I q.J q.extra) q.spent 1=P)
    (outlet : P≤cuts (m+1) (stock x base q.I q.J q.extra) q.spent (m+1)) :
    ∀ d, q.I≤d → d<q.J → (x (liftedSite base d)).stock=false := by
  let s := stock x base q.I q.J q.extra
  have he : q.extra=false := by
    apply Bool.eq_false_iff.mpr
    intro hk
    have ht := good.extraHere hk
    simp [unpaused] at ht
  have hs (d : Nat) (hd : q.I≤d) (hJ : d<q.J) :
      s d=(x (liftedSite base d)).stock := by simp [s,stock,he,hd,hJ]
  have out : P≤q.spent := by
    change P≤cuts (m+1) s q.spent (m+1) at outlet
    rwa [cuts_far (m+1) s q.spent (m+1) (Nat.le_refl _)] at outlet
  have hmono (k : Nat) (hk : 1≤k) :
      cuts (m+1) s q.spent k≤cuts (m+1) s q.spent 1 := by
    induction k with
    | zero => omega
    | succ k ih =>
      by_cases h : k=0
      · subst k
        exact Nat.le_refl _
      · have hstep := cuts_adjacent_all (m+1) s q.spent k
        have H := ih (by omega)
        omega
  intro d hd hJ
  have hpos := good.positive
  have hfits := good.fits
  have hm := hmono d (by omega)
  have hstep := cuts_adjacent (m+1) s q.spent d (by omega)
  have hlow : q.spent≤cuts (m+1) s q.spent (d+1) := by
    unfold cuts
    omega
  apply Bool.eq_false_iff.mpr
  intro hb
  have ha : s d=true := (hs d hd hJ).trans hb
  change cuts (m+1) s q.spent 1=P at conserved
  rw [ha,Bool.toNat_true] at hstep
  omega

open SevenTagCharge WindowSpan WindowA0StockDrain in
/-- Official A0 clock assembled from local gated rows and a closed view
instead of a whole-word fixed-sink comparison hypothesis. -/
theorem entry_drain_of_gated_rows {α : Type} {p c n : Nat} (hn : 4≤n)
    (x : Config p c n) (i : Fin (RankPhysical.rank x))
    (hm0 : MCOV x) (hc : COV x) (short : 2*span x i+2<n)
    (h1 : (x (rootSite x (liftedSite i 1))).leader=false)
    (h2 : (x (rootSite x (liftedSite i 2))).leader=false)
    (m P : Nat) (edge : Nat→Fin n)
    (observer : α → Fin n → α) (project : α → WindowA0StockDrain.Cursor p c n)
    (seed : α) (good : α → Prop) (height : α → Nat → Nat) :
    let g := window7 (WindowRoster.roster x) i
    let tag := fun j : Nat => WindowRoster.roster x (liftedSite i j)
    let z := entryCursor x i
    let b := entryBase x i
    let u := z.heads.k-z.heads.i
    let step := next g (tag 1) (tag 2) b
    P≤u → m≤2*u →
    project seed=z →
    (∀ y e, project (observer y e)=step (project y) e) →
    GatedRules observer good (fun y => canServe b (project y)) height m P edge →
    (∀ y e, good y → good (observer y e)) →
    good seed →
    (∀ y, good y → ¬pending b (project y) → P≤height y m → drained b (project y)) →
    IIDExpectedHittingTimeAtMost RootedAssembly.wordNext
      (fun w => drained b (tape g (tag 1) (tag 2) b z w)) [] (17*n*(span x i+1)) := by
  intro g tag z b u step hP hm hseed commute rule keep hz H
  apply WindowA0FiniteDAG.entry_drain_of_fixed_sink hn x i hm0 hc short h1 h2 m P edge hP hm
  exact actual_completion_with_observer g (tag 1) (tag 2) b z m P edge
    observer project seed hseed commute good height rule keep hz H

#print axioms drained_of_outlet
#print axioms entry_drain_of_gated_rows
#print axioms gated_outlet
#print axioms actual_completion_of_gated
#print axioms actual_completion_with_observer

end L4.WindowA0PausedDAG
