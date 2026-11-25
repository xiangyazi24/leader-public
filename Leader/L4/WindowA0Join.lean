import Leader.L4.WindowOwnership
import Leader.L4.WindowA0FirstExit

namespace L4.WindowA0Join
open SevenTagCharge WindowLocal WindowOwnership WindowA0FirstExit
open WindowFiveStages RootedAssembly TripleRenewal

abbrev tag {p c n : Nat} (x : Config p c n) (i : Fin (RankPhysical.rank x))
    (j : Nat) : Fin n := WindowRoster.roster x (liftedSite i j)

def scope {p c n : Nat} (x : Config p c n)
    (i : Fin (RankPhysical.rank x)) : EntryScope (window7 (WindowRoster.roster x) i) := by
  refine ⟨tag x i 1,tag x i 2,[tag x i 0],
    [tag x i 2,tag x i 3,tag x i 4,tag x i 5,tag x i 6],
    [tag x i 0,tag x i 1],[tag x i 3,tag x i 4,tag x i 5,tag x i 6],?_,?_⟩
  · rfl
  · rfl

theorem initial_ghosts {p c n : Nat} (x : Config p c n)
    (i : Fin (RankPhysical.rank x)) (h : QuietEntrance x)
    (he : (Front.initial x h (scope x i)).mode=.entry (scope x i)) :
    (x (WindowSpan.rootSite x (liftedSite i 1))).leader=false ∧
    (x (WindowSpan.rootSite x (liftedSite i 2))).leader=false := by
  have hn : startMode (z:=SevenTagCharge.initial x) (scope x i)=none := by
    cases H : startMode (z:=SevenTagCharge.initial x) (scope x i) with
    | none => rfl
    | some P => simp [Front.initial,H] at he
  obtain ⟨H1,H2⟩ := (startMode_none (scope x i)).mp hn
  have occ (j : Nat) : (SevenTagCharge.initial x).slots (tag x i j)=some (tag x i j) := by
    have H := (WindowRoster.roster_exact x (tag x i j)).mp ⟨liftedSite i j,rfl⟩
    simp [SevenTagCharge.initial,initSlots,H]
  constructor
  · apply Bool.eq_false_iff.mpr
    intro hl
    exact H1 ⟨tag x i 1,occ 1,hl⟩
  · apply Bool.eq_false_iff.mpr
    intro hl
    exact H2 ⟨tag x i 2,occ 2,hl⟩


abbrev AtEntry {p c n} {x : Config p c n} {g : List (Fin n)}
    (A : EntryScope g) (u : WindowLatch.Cursor (Front x g) x g) : Prop :=
  ∃ s, u=.inl s ∧ s.mode=.entry A

private theorem step_entry_iff {p c n} {x : Config p c n} {g : List (Fin n)}
    (hp : 2≤p) (hc : 12≤c) (hn : 4≤n) (A : EntryScope g)
    (s : Front x g) (hs : s.mode=.entry A) (e : Fin n) :
    AtEntry A (WindowProtectedOuter.joinedNext
      (WindowLatch.front hn (WindowOwnership.decide hp hc hn)) (.inl s) e) ↔
      WindowA0Route.routeTwo g A.first A.second s.ledger e=.keep := by
  rcases s with ⟨z,hv,hq,mode⟩
  change mode=.entry A at hs
  subst mode
  unfold WindowProtectedOuter.joinedNext WindowLatch.front WindowOwnership.decide
  dsimp only
  split
  · rename_i t hEq
    split at hEq
    · rename_i H
      cases hEq
      exact ⟨fun _ => H,fun _ => ⟨_,rfl,rfl⟩⟩
    · rename_i a H
      cases hEq
      constructor
      · rintro ⟨t,ht,hT⟩; cases ht; cases hT
      · intro E; rw [H] at E; cases E
    · rename_i a loc H
      cases hEq
      constructor
      · rintro ⟨t,ht,hT⟩; cases ht; cases hT
      · intro E; rw [H] at E; cases E
    · rename_i a loc H
      exact (no_entry_death z g A.first A.second e a loc H).elim
  · rename_i k hEq
    split at hEq
    · cases hEq
    · cases hEq
    · cases hEq
    · rename_i a loc H
      exact (no_entry_death z g A.first A.second e a loc H).elim

theorem observed_ledger {p c n} (x : Config p c n) (i : Fin (RankPhysical.rank x))
    (w : Word n) : (observed x i w).ledger=observe (SevenTagCharge.initial x) w := by
  have P (z : WindowA0StockDrain.Cursor p c n) :
      (WindowA0StockDrain.tape (window7 (WindowRoster.roster x) i)
        (tag x i 1) (tag x i 2) (WindowA0StockDrain.entryBase x i) z w).ledger=observe z.ledger w := by
    induction w generalizing z with
    | nil => rfl
    | cons e w ih =>
      rw [show WindowA0StockDrain.tape _ _ _ _ z (e::w) =
        WindowA0StockDrain.tape _ _ _ _
          (WindowA0StockDrain.next (window7 (WindowRoster.roster x) i) (tag x i 1) (tag x i 2)
            (WindowA0StockDrain.entryBase x i) z e) w from rfl,ih,WindowA0StockDrain.projection]
      rfl
  exact P _


abbrev InEntry {p c n : Nat} (hp : 2≤p) (hc : 12≤c) (hn : 4≤n)
    (x : Config p c n) (h : QuietEntrance x) (i : Fin (RankPhysical.rank x)) (w : Word n) : Prop :=
  AtEntry (scope x i) (fold hp hc hn h (scope x i) w)

theorem child_iff {p c n : Nat} (hp : 2≤p) (hc : 12≤c) (hn : 4≤n)
    (x : Config p c n) (h : QuietEntrance x) (i : Fin (RankPhysical.rank x))
    (w : Word n) (e : Fin n)
    (hpast : InEntry hp hc hn x h i w) (hd : ¬done x i w) :
    InEntry hp hc hn x h i (wordNext w e) ↔ ¬done x i (wordNext w e) := by
  obtain ⟨s,hs,he⟩ := hpast
  have H := fold_ledger hp hc hn h (scope x i) w
  rw [hs] at H
  change s.ledger=observe (SevenTagCharge.initial x) w at H
  rw [←observed_ledger x i w] at H
  unfold InEntry fold wordNext
  rw [WindowLatch.replay_append]
  change AtEntry (scope x i) (WindowProtectedOuter.joinedNext
    (WindowLatch.front hn (WindowOwnership.decide hp hc hn))
    (fold hp hc hn h (scope x i) w) e) ↔ _
  rw [hs,step_entry_iff hp hc hn _ s he,H]
  let S := WindowA0EntryJoin.entryScope x i
  change WindowA0Route.routeTwo S.group S.iTag S.jTag (observed x i w).ledger e=.keep ↔ _
  have A := WindowA0StockDrain.tape_append S.group S.iTag S.jTag
    (WindowA0StockDrain.entryBase x i) (WindowA0StockDrain.entryCursor x i) w e
  change observed x i (wordNext w e)=WindowA0StockDrain.next S.group S.iTag S.jTag
    (WindowA0StockDrain.entryBase x i) (observed x i w) e at A
  unfold done
  change _ ↔ ¬(observed x i (wordNext w e)).exit.isSome=true
  rw [A]
  have hnone : (observed x i w).exit=none := by
    cases hh : (observed x i w).exit with
    | none => rfl
    | some k => exact (hd (by simp [done,hh])).elim
  by_cases hr : WindowA0Route.routeTwo S.group S.iTag S.jTag (observed x i w).ledger e=.keep <;>
    simp [WindowA0StockDrain.next,hnone,hr]

private theorem snoc_ind {α : Type} (P : List α → Prop) (h0 : P [])
    (hs : ∀ u e, P u → P (u ++ [e])) (w : List α) : P w := by
  have aux : ∀ v : List α, P v.reverse := by
    intro v
    induction v with
    | nil => exact h0
    | cons e u ih => rw [List.reverse_cons]; exact hs _ _ ih
  simpa using aux w.reverse

/-- Through every prefix strictly before the local first stop, the
actual front is still in the same entry mode. At that first stop the
two observables agree, without reading a padded ledger. -/
theorem clean_sync {p c n : Nat} (hp : 2≤p) (hc : 12≤c) (hn : 4≤n)
    (x : Config p c n) (h : QuietEntrance x) (i : Fin (RankPhysical.rank x))
    (he : (Front.initial x h (scope x i)).mode=.entry (scope x i))
    (w : Word n) (hw : Clean (done x i) w) :
    InEntry hp hc hn x h i w ↔ ¬done x i w := by
  induction w using snoc_ind with
  | h0 =>
    have nn : ¬done x i [] := by simp [done,observed,WindowA0StockDrain.tape,GGTiming.runMarks,WindowA0StockDrain.entryCursor]
    exact ⟨fun _ => nn,fun _ => ⟨_,rfl,he⟩⟩
  | hs w e ih =>
    change Clean _ (wordNext w e) at hw
    obtain ⟨H,N⟩ := (clean_child _ w e).mp hw
    exact child_iff hp hc hn x h i w e ((ih H).mpr N) N

theorem front_first_exit {p c n : Nat} (hp : 2≤p) (hc : 12≤c) (hn : 4≤n)
    (x : Config p c n) (h : QuietEntrance x) (i : Fin (RankPhysical.rank x))
    (he : (Front.initial x h (scope x i)).mode=.entry (scope x i))
    (w : Word n) (hw : FirstExit (done x i) w) :
    FirstExit (fun u => ¬InEntry hp hc hn x h i u) w := by
  constructor
  · intro k hk hnIn
    have C : Clean (done x i) (w.take k) := by
      intro j hj
      rw [List.take_take, Nat.min_eq_left (Nat.le_trans (Nat.le_of_lt hj) (List.length_take_le _ _))]
      exact hw.1 j (by have := List.length_take_le k w; omega)
    exact hnIn ((clean_sync hp hc hn x h i he _ C).mpr (hw.1 k hk))
  · intro H
    exact ((clean_sync hp hc hn x h i he w hw.1).mp H) hw.2

#print axioms initial_ghosts
#print axioms front_first_exit

/-- Entry transaction at the original front start. The enclosing
geometry supplies only its span potential and nominated growth row;
the hit predicate and its clock are fully physical. -/
def entryTransaction {p c n : Nat} (hn : 5≤n) (hc : 12≤c)
    (x : Config p c n) (i : Fin (RankPhysical.rank x)) (h : QuietEntrance x)
    (he : (Front.initial x h (scope x i)).mode=.entry (scope x i))
    (short : 2*WindowSpan.span x i+2<n)
    (spanP : Word n → Nat) (nom : Word n → Fin n)
    (start : spanP []≤WindowSpan.span x i)
    (step : ∀ w e, ¬FirstExit (done x i) w →
      spanP (wordNext w e)≤spanP w+(if e=nom w then 1 else 0)) :
    Transaction (n:=n) (WindowA0Restart.entryK c) [] (WindowSpan.span x i) where
  hit := done x i
  span := spanP
  nom := nom
  startSpan := start
  localStep := step
  mean :=
    have ghosts := initial_ghosts x i h he
    entry_clock hn hc x i h.1 h.2.1 short ghosts.1 ghosts.2

#print axioms entryTransaction
end L4.WindowA0Join
