import Leader.L4.SevenTagCharge
import Leader.L4.RankBlockContraction
import Leader.L4.SingletonFinish
import Leader.L4.HitCapCountdown
import Leader.L4.MainAssembly
import Leader.L4.AliasLiteralClock

namespace L4.LastTwoAssembly
open RankPhysical RankRenewal RankBlockContraction SevenTagCharge

def wordNext {n : Nat} (w : List (Fin n)) (e : Fin n) : List (Fin n) := w++[e]

def reward {p c n : Nat} (x : Config p c n) (w0 w : List (Fin n)) : Nat :=
  (hit (observe (initial x) w).losses w0).toNat

/-- A chosen cyclic roster/filter and its marginal trial results.
The literal common schedule and all pointwise retirement incidence
are derived rather than fields. -/
structure WindowMarginals {p c n : Nat} (x : Config p c n) (H T : Nat) where
  k : Nat
  roster : Fin k → Fin n
  inj : ∀ i j, roster i = roster j → i=j
  starts : List (Fin k)
  nodup : starts.Nodup
  many : rank x≤starts.length+H
  trial : ∀ i ∈ starts, 12*n^T≤25*endpointSum wordNext
      (reward x (window7 roster i)) T []

/-- Last-two certificate on the original raw word. The loss is
recorded only when one of this window's original tags disappears,
and all such windows use this same transition. -/
def of_marginals {p c n : Nat} {x : Config p c n} {H T : Nat}
    (hn : 4≤n) (hq : QuietEntrance x) (z : WindowMarginals x H T) :
    GroupRewardCertificate x H T := by
  let groups := z.starts.map (window7 z.roster)
  refine { State := List (Fin n)
           start := []
           next := wordNext
           project := run x
           initial := rfl
           projects := fun w e => run_append x w [e]
           events := groups.map (reward x)
           many := by simpa [groups] using z.many
           success := ?_
           incidence := ?_ }
  · intro f hf
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hf
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
    exact z.trial i hi
  · intro w
    have h7 := windows7_multiplicity z.roster z.inj z.starts z.nodup
    have h := physical_incidence x hn hq.1 hq.2.1 w groups h7
    change 7*rank (run x w) + ((groups.map (reward x)).map (fun f => f w)).sum ≤ _
    simpa only [List.map_map,Function.comp_def, reward,hits] using h

/-- Exact remaining data after the window reward is wired to tags.
There is no abstract fixed-supplier stop on an unrelated exterior
retirement in this residual: the specified endpoint is the actual
loss of an initial window member. -/
def ConcreteWindowMarginals : Prop :=
  ∀ c : Nat, 12≤c → ∃ B C₀ : Nat, 0<B ∧ 0<C₀ ∧
    ∀ (n L : Nat), 4≤n → 1≤L → L≤n →
    ∃ H : Nat, H*L≤C₀*n ∧
      ∀ {p : Nat} (x : Config p c n), 2≤p → (¬p∣n) → QuietEntrance x →
        Nonempty (WindowMarginals x H (B*n*L))

theorem concreteSevenGroups_of_marginals (h : ConcreteWindowMarginals) :
    ConcreteSevenGroups := by
  intro c hc
  obtain ⟨B,C₀,hB,hC,hRest⟩ := h c hc
  refine ⟨B,C₀,hB,hC,?_⟩
  intro n L hn hL hLn
  obtain ⟨H,hH,base⟩ := hRest n L hn hL hLn
  refine ⟨H,hH,?_⟩
  intro p x hp hpnd hq
  obtain ⟨z⟩ := base x hp hpnd hq
  exact ⟨of_marginals hn hq z⟩

open SingletonFinish HitCapCountdown

/-- A cap for the actual aliased episode, not for a projection with
two separately scheduled seam ports. -/
def ConcreteAliasHitCap : Prop :=
  ∀ {c n : Nat} (seam : Fin n) (s : AliasState c n),
    12≤c → 4≤n → s.born=false →
    ∃ nom : List (Fin n) → Fin n,
      ∀ w u, Episode (aliasStep seam) (fun a => a.born=true) s w u →
        paidHits nom w u≤8*(2*c+1)*(n+1)

theorem pureAliasClock_of_hitCap (h : ConcreteAliasHitCap) : PureAliasClock := by
  intro c n seam s hc hn hs
  obtain ⟨nom,bound⟩ := h seam s hc hn hs
  let clock := ofHitCap (aliasStep seam) (fun a => a.born=true) s nom _ bound
  refine ⟨clock, Nat.le_trans (initial_budget_ofHitCap _ _ _ _ _ bound) ?_⟩
  exact Nat.mul_le_mul_right (n+1) (Nat.mul_le_mul_right (2*c+1) (by decide))


/-- Paper downstream at the narrow physical endpoints. The two
new premises are not erased by the certificate assembly. -/
theorem main_of_last_two (restart : RankPhysical.ConcreteRestartTrial)
    (windows : ConcreteWindowMarginals) (alias : ConcreteAliasHitCap) :
    row175Statement :=
  mainTheorem restart (concreteSevenGroups_of_marginals windows)
    (pureAliasClock_of_hitCap alias)


/-- The alias premise is now a literal theorem. Only the two remaining
restart and window-local physical inputs appear in the result. -/
theorem main_after_window_marginals (restart : RankPhysical.ConcreteRestartTrial)
    (windows : ConcreteWindowMarginals) : row175Statement :=
  mainTheorem restart (concreteSevenGroups_of_marginals windows)
    AliasLiteralClock.pureAliasClock

end L4.LastTwoAssembly

#print axioms L4.LastTwoAssembly.of_marginals
#print axioms L4.LastTwoAssembly.concreteSevenGroups_of_marginals
#print axioms L4.LastTwoAssembly.pureAliasClock_of_hitCap

#print axioms L4.LastTwoAssembly.main_of_last_two

#print axioms L4.LastTwoAssembly.main_after_window_marginals
