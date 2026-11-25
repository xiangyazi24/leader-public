import Leader.L4.QueueDAG
import Leader.L4.WindowA0StockDrain
import Leader.L4.WindowA0StockCap

namespace L4.WindowA0FiniteDAG
open QueueDAG GGTiming

/-- Fixed-sink height thresholds only request the k≤P initially
present particles. The left boundary is saturated by initial mass,
not a transition from a living injector. -/
structure BoundedRules {α : Type} {n : Nat} (next : α→Fin n→α)
    (good : α→Prop) (height : α→Nat→Nat) (m P : Nat) (edge : Nat→Fin n) : Prop where
  mono : ∀ x e i, good x → i≤m → height x i≤height (next x e) i
  commit : ∀ x i k, good x → i≤m → 0<k → k≤P →
    (0<i → k≤height x (i-1)) →
    (i<m → k-1≤height x (i+1)) →
    k≤height (next x (edge i)) i

theorem bounded_sound {α : Type} {n : Nat} {next : α→Fin n→α}
    {good : α→Prop} {height : α→Nat→Nat} {m P : Nat} {edge : Nat→Fin n}
    (rule : BoundedRules next good height m P edge) (fuel i k : Nat)
    (hi : i≤m) (hkP : k≤P) (hfuel : 2*k+i≤fuel) :
    Sound next good (fifoTree m edge fuel i k) (fun x => k≤height x i) := by
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
      apply Sound.fork _ _ _ (fun x => 0<i → k≤height x (i-1))
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
      · exact fun x hx => rule.commit x i k hx hi (by omega) hkP

theorem completed_outlet {α : Type} {n : Nat} {next : α→Fin n→α}
    {good : α→Prop} {height : α→Nat→Nat} {m P : Nat} {edge : Nat→Fin n}
    (rule : BoundedRules next good height m P edge)
    (keep : ∀ x e, good x → good (next x e)) (x : α) (hx : good x)
    (w : List (Fin n)) (hw : finished (runMarks advance (outletPaths m edge P) w)) :
    P≤height (runMarks next x w) m :=
  (bounded_sound rule (2*P+m) m P (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)).of_paths
    keep x hx w hw

/-- The scalar depth and cardinality fields of the A0 stock-cut
certificate, with the short parameters kept explicit. -/
theorem bounds {n : Nat} (m P u : Nat) (edge : Nat→Fin n)
    (hP : P≤u) (hm : m≤2*u) :
    let paths := outletPaths m edge P
    (∀ a ∈ paths, a.length≤4*u+2) ∧ paths.length≤2^(4*u+3) := by
  refine ⟨fun a ha => Nat.le_trans (outletPaths_span m edge P a ha) (by omega),?_⟩
  exact Nat.le_trans (outletPaths_count m edge P)
    (Nat.pow_le_pow_right (by decide) (by omega))

open SevenTagCharge WindowSpan WindowA0StockDrain in
/-- The official A0 entry no longer assumes an original-byte cap.
For the drain clock, the one remaining physical premise is the
paused fixed-sink comparison for the explicit dependency paths. -/
theorem entry_drain_of_fixed_sink {p c n : Nat} (hn : 4≤n)
    (x : Config p c n) (i : Fin (RankPhysical.rank x))
    (hm0 : MCOV x) (hc : COV x) (short : 2*span x i+2<n)
    (h1 : (x (rootSite x (liftedSite i 1))).leader=false)
    (h2 : (x (rootSite x (liftedSite i 2))).leader=false)
    (m P : Nat) (edge : Nat→Fin n) :
    let g := window7 (WindowRoster.roster x) i
    let tag := fun j : Nat => WindowRoster.roster x (liftedSite i j)
    let z := entryCursor x i
    let b := entryBase x i
    let u := z.heads.k-z.heads.i
    P≤u → m≤2*u →
    (∀ w, ¬pending b (tape g (tag 1) (tag 2) b z w) →
      finished (drainPaths g (tag 1) (tag 2) b z (outletPaths m edge P) w) →
      drained b (tape g (tag 1) (tag 2) b z w)) →
    IIDExpectedHittingTimeAtMost RootedAssembly.wordNext
      (fun w => drained b (tape g (tag 1) (tag 2) b z w)) [] (17*n*(span x i+1)) := by
  intro g tag z b u hp hm H
  obtain ⟨hEntry,ha,hb,hk,hu⟩ := entry_continuing x i hm0 hc short h1 h2
  have cert : StockCutCertificate g (tag 1) (tag 2) b z u :=
    ⟨outletPaths m edge P,4*u+2,Nat.le_refl _,(bounds m P u edge hp hm).1,
      (bounds m P u edge hp hm).2,WindowA0StockCap.entry_paid_cap hn x i hm0 hc short h1 h2,H⟩
  have hh := mean_of_certificate (initial:=x) hn g (tag 1) (tag 2) (tag 3) b z ha hb hk
    (.inr hEntry) u cert
  intro t
  exact Nat.le_trans (hh t)
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.add_le_add_right hu 1)))

end L4.WindowA0FiniteDAG
