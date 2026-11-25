import Leader.L4.RootedWindows

/-! Exact first-exit suffix transactions for the G6/G7 windows.
Physical stage clocks and their event/geometry invariants are inputs. -/
namespace L4.WindowFiveStages
open TripleRenewal WindowClock RootedAssembly SevenTagCharge
open Classical RankRenewal

abbrev Word (n : Nat) := List (Fin n)

def Clean {n : Nat} (hit : Word n → Prop) (u : Word n) : Prop :=
  ∀ k, k < u.length → ¬ hit (u.take k)

def FirstExit {n : Nat} (hit : Word n → Prop) (u : Word n) : Prop :=
  Clean hit u ∧ hit u

theorem clean_nil {n : Nat} (hit : Word n → Prop) : Clean hit [] := by
  intro k hk
  simp at hk

theorem clean_child {n : Nat} (hit : Word n → Prop) (u : Word n) (e : Fin n) :
    Clean hit (wordNext u e) ↔ Clean hit u ∧ ¬ hit u := by
  constructor
  · intro h
    refine ⟨?_,?_⟩
    · intro k hk
      have H := h k (by simp [wordNext]; omega)
      simpa only [wordNext,List.take_append_of_le_length (Nat.le_of_lt hk)] using H
    · have H := h u.length (by simp [wordNext])
      simpa only [wordNext,List.take_append_length] using H
  · rintro ⟨h,hu⟩ k hk
    have hb : k≤u.length := by simp [wordNext] at hk; omega
    by_cases H : k=u.length
    · subst k
      simpa only [wordNext,List.take_append_length] using hu
    · simpa only [wordNext,List.take_append_of_le_length hb] using h k (by omega)

theorem no_second_exit {n : Nat} (hit : Word n → Prop) (u v : Word n)
    (hu : FirstExit hit u) (hv : v≠[]) : ¬ FirstExit hit (u++v) := by
  intro h
  have hlen : u.length < (u++v).length := by
    simp only [List.length_append]
    cases v <;> simp_all
  have H := h.1 u.length hlen
  exact (by simpa only [List.take_append_length] using H : ¬ hit u) hu.2

theorem cost_firstExit {n : Nat} (hit : Word n → Prop) (t : Nat)
    (u : Word n) (hu : Clean hit u) :
    iidHitCost wordNext (FirstExit hit) t u = iidHitCost wordNext hit t u := by
  induction t generalizing u with
  | zero => rfl
  | succ t ih =>
    by_cases hh : hit u
    · rw [iidHitCost_of_target _ _ _ ⟨hu,hh⟩,iidHitCost_of_target _ _ _ hh]
    · have ht : ¬ FirstExit hit u := fun h => hh h.2
      simp only [iidHitCost,hh,ht,if_false]
      have H : (fun e => iidHitCost wordNext (FirstExit hit) t (wordNext u e)) =
          (fun e => iidHitCost wordNext hit t (wordNext u e)) :=
        funext (fun e => ih _ ((clean_child hit u e).mpr ⟨hu,hh⟩))
      rw [H]

/-- Reachability includes suffixes beyond the exact exit, and their
projection still performs all physical marks. -/
def suffixStage {n : Nat} (w : Word n) (hit : Word n → Prop) : Stage wordNext w where
  State := Word n
  start := []
  next := wordNext
  project u := w++u
  ready := FirstExit hit
  reachable := fun _ => True
  projInit := List.append_nil _
  projStep _ _ := (List.append_assoc ..).symm
  reachStart := trivial
  reachStep _ _ _ := trivial

/-- The span local bound includes nonready suffixes after the exact exit.
The intended implementation freezes its stored span on those suffixes. -/
structure Transaction {n : Nat} (C : Nat) (w : Word n) (h : Nat) where
  hit : Word n → Prop
  span : Word n → Nat
  nom : Word n → Fin n
  startSpan : span []≤h
  localStep : ∀ u e, ¬ FirstExit hit u →
    span (wordNext u e)≤span u+(if e=nom u then 1 else 0)
  mean : IIDExpectedHittingTimeAtMost wordNext hit [] (C*n*(h+1))

theorem Transaction.phase {n C h j : Nat} {w : Word n} {done : Word n → Prop}
    (K : Transaction C w h)
    (after : ∀ u, FirstExit K.hit u → ¬done (w++u) →
      WindowStages wordNext done C j (w++u) (K.span u)) :
    WindowStages wordNext done C (j+1) w h := by
  refine WindowStages.phase (suffixStage w K.hit) K.span K.startSpan K.nom
    (fun u e _ h => K.localStep u e h) ?_ (fun u _ hx hn => after u hx hn)
  intro t
  change iidHitCost wordNext (FirstExit K.hit) t []≤_
  rw [cost_firstExit K.hit t [] (clean_nil _)]
  exact K.mean t

/-- Immediate extension/bypass consumes no marks and preserves span. -/
theorem skip {n C h j : Nat} {w : Word n} {done : Word n → Prop} (i : Fin n)
    (next : WindowStages wordNext done C j w h) :
    WindowStages wordNext done C (j+1) w h := by
  let K : Transaction C w h :=
    ⟨fun _ => True,fun _ => h,fun _ => i,Nat.le_refl _,
      fun _ _ _ => Nat.le_add_right _ _,fun t => by
        rw [iidHitCost_of_target _ _ _ trivial]; exact Nat.zero_le _⟩
  apply K.phase
  intro u hu _
  have he : u=[] := by
    cases u with
    | nil => rfl
    | cons e us => exact (hu.1 0 (by simp) trivial).elim
  subst u
  simpa [K] using next

/-- Indices count remaining slots: 5 entry, 4 first extension, 3
second extension, 2 deletion, 1 protected push. Only the exact exit
must establish the next interface; done words may finish immediately. -/
structure FivePlan {n : Nat} (done : Word n → Prop) (C : Nat) where
  allow : Nat → Word n → Nat → Prop
  terminal : ∀ w h, allow 0 w h → done w
  localStage : ∀ j w h, j<5 → allow (j+1) w h → ¬done w →
    allow j w h ∨ ∃ K : Transaction C w h,
      ∀ u, FirstExit K.hit u → ¬done (w++u) → allow j (w++u) (K.span u)

theorem FivePlan.assemble {n C : Nat} {done : Word n → Prop}
    (P : FivePlan done C) (edge : Fin n) (j : Nat) (hj : j≤5)
    (w : Word n) (h : Nat) (hw : P.allow j w h) :
    WindowStages wordNext done C j w h := by
  induction j generalizing w h with
  | zero => exact WindowStages.already (P.terminal w h hw)
  | succ j ih =>
    by_cases hd : done w
    · exact WindowStages.already hd
    · rcases P.localStage j w h (by omega) hw hd with hs | ⟨K,hK⟩
      · exact skip edge (ih (by omega) w h hs)
      · exact K.phase (fun u hu hn => ih (by omega) _ _ (hK u hu hn))

/-- To supply the full local span field it suffices to prove its
geometric bound on prefixes strictly before exit; past-exit sources
only need a frozen stamp. -/
theorem localStep_of_active_frozen {n : Nat} (hit : Word n → Prop)
    (span : Word n → Nat) (nom : Word n → Fin n)
    (active : ∀ u e, Clean hit u → ¬hit u →
      span (wordNext u e)≤span u+(if e=nom u then 1 else 0))
    (frozen : ∀ u e, ¬Clean hit u → span (wordNext u e)=span u) :
    ∀ u e, ¬FirstExit hit u →
      span (wordNext u e)≤span u+(if e=nom u then 1 else 0) := by
  intro u e hE
  by_cases hC : Clean hit u
  · exact active u e hC (fun H => hE ⟨hC,H⟩)
  · rw [frozen u e hC]
    exact Nat.le_add_right _ _

def LedgerReward {p c n : Nat} (x : Config p c n) (g : List (Fin n))
    (w : Word n) : Prop := hit (observe (initial x) w).losses g = true

theorem ledgerReward_indicator {p c n : Nat} (x : Config p c n)
    (g : List (Fin n)) (w : Word n) :
    indicator (LedgerReward x g) w = reward x g w := by
  unfold LedgerReward indicator reward
  cases h : hit (observe (initial x) w).losses g <;> simp [h]

theorem no_entry_mass {n : Nat} (t : Nat) (w : Word n) :
    endpointSum wordNext (indicator fun _ => False) t w=0 := by
  induction t generalizing w with
  | zero => simp [endpointSum,indicator]
  | succ t ih =>
    have hz (m : Nat) : (List.ofFn (fun _ : Fin m => (0 : Nat))).sum=0 := by
      induction m with
      | zero => rfl
      | succ m hm => simpa [List.ofFn_succ] using hm
    simp [endpointSum,ih,TaggedTail.sumEdge,hz]

/-- The final proof step on the actual reward. The selected loss group
is fixed; the stage clock can use separately scoped event/certified lists. -/
theorem reward_of_plan {p c n C h : Nat} (x : Config p c n) (g : List (Fin n))
    (done freshBad : Word n → Prop)
    (closed : ∀ w e, done w → done (wordNext w e))
    (cover : ∀ w, done w → ¬freshBad w → LedgerReward x g w)
    (P : FivePlan done C) (hn : 0<n) (hC : 0<C) (hw : P.allow 5 [] h)
    (fresh : ∀ t, 1000*endpointSum wordNext (indicator freshBad) t []≤11*n^t) :
    let T := (4*((1+C)^5-1))*n*(h+1)
    12*n^T≤25*endpointSum wordNext (reward x g) T [] := by
  let T := (4*((1+C)^5-1))*n*(h+1)
  have hT : 4*(((1+C)^5-1)*n*(h+1))≤T := by simp [T,Nat.mul_assoc]
  have H := five_stage_reward wordNext done (LedgerReward x g) (fun _ => False)
    freshBad closed (fun w done _ nb => cover w done nb) C h T hn hC hT []
    (P.assemble ⟨0,hn⟩ 5 (by decide) [] h hw)
    (by rw [no_entry_mass,Nat.mul_zero]; exact Nat.zero_le _)
    (fresh T)
  have hr : indicator (LedgerReward x g)=reward x g :=
    funext (ledgerReward_indicator x g)
  rwa [hr] at H

/-! These are the remaining obligations of this adapter, not conclusions:
construct the physical controller, prove its sticky terminal reason and
exact event cover, establish the five local transaction budgets with
physical span handoffs, and bound its protected-birth mass. -/
def PhysicalPlan : Prop :=
  ∀ c : Nat, 12≤c → ∃ C : Nat, 0<C ∧
    ∀ {p n : Nat} (x : Config p c n), 2≤p → 4≤n →
      QuietEntrance x → 7≤RankPhysical.rank x →
      ∀ i : Fin (RankPhysical.rank x), 2*WindowSpan.span x i+2<n →
      let g := window7 (WindowRoster.roster x) i
      ∃ (done freshBad : Word n → Prop) (P : FivePlan done C),
        P.allow 5 [] (WindowSpan.span x i) ∧
        (∀ w e, done w → done (wordNext w e)) ∧
        (∀ w, done w → ¬freshBad w → LedgerReward x g w) ∧
        ∀ t, 1000*endpointSum wordNext (indicator freshBad) t []≤11*n^t

theorem rooted_short_window_of_plan (h : PhysicalPlan) : RootedWindows.RootedShortWindowReward := by
  intro c hc
  obtain ⟨C,hC,plan⟩ := h c hc
  refine ⟨4*((1+C)^5-1),?_ ,?_⟩
  · have hp : 1+C ≤ (1+C)^5 := by
      simpa only [Nat.pow_one] using (Nat.pow_le_pow_right (show 0<1+C by omega)
        (by decide : 1≤5))
    omega
  · intro p n x hp hn hq hk i hshort
    obtain ⟨done,freshBad,P,hw,closed,cover,fresh⟩ := plan x hp hn hq hk i hshort
    exact reward_of_plan x _ done freshBad closed cover P (by omega) hC hw fresh

end L4.WindowFiveStages
