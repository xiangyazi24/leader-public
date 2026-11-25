import Leader.L4.WindowA0Uniform

namespace L4.WindowA0FirstExit
open SevenTagCharge WindowLocal WindowA0Route WindowA0StockDrain
open WindowA0EntryJoin WindowFiveStages RootedAssembly TripleRenewal

def Classified {p c n : Nat} (g : List (Fin n)) (a b : Fin n)
    (z : Ledger p c n) (e : Fin n) (y : Ledger p c n) (r : Event n) : Prop :=
  (∃ k, r=.reward k ∧ k∈g ∧ lostStep z.config z.slots e=some k ∧ y.losses=k::z.losses) ∨
    (∃ k, (k=a ∨ k=b) ∧ r=.targetBirth k (rightNeighbor e) ∧
      z.slots e=some k ∧ (z.config (rightNeighbor e)).leader=false ∧ TaggedLeader y e k)

private theorem recorded_birth {p c n : Nat} (hn : 4≤n)
    (g : List (Fin n)) (a b k : Fin n) (z : Ledger p c n) (e : Fin n)
    (hm : MCOV z.config) (hc : COV z.config) (h : k=a ∨ k=b)
    (hs : z.slots e=some k) (hb : birthAt z.config e=true) :
    Classified g a b z e (advance z e) (.targetBirth k (rightNeighbor e)) := by
  have hb0 : (z.config (rightNeighbor e)).leader=false := by
    have T := (Bool.and_eq_true_iff.mp hb).1
    cases E : (z.config (rightNeighbor e)).leader <;> simp_all
  exact .inr ⟨k,h,rfl,hs,hb0,(target_birth_result hn g [] z e k hm hc hs hb).2⟩

/-- The third event constructor of the generic router (prefix death)
cannot appear here, because A0 uses an empty certified prefix. -/
theorem classify_route {p c n : Nat} (hn : 4≤n)
    (g : List (Fin n)) (a b : Fin n) (z : Ledger p c n) (e : Fin n)
    (hm : MCOV z.config) (hc : COV z.config)
    (h : routeTwo g a b z e≠.keep) :
    Classified g a b z e (advance z e) (routeTwo g a b z e) := by
  cases hL : selectedGroupLoss g z e with
  | some k =>
    obtain ⟨hl,hg⟩ := (selectedGroupLoss_iff g z e k).mp hL
    exact .inl ⟨k,selected_loss_first g a b k z e hL,hg,hl,by simp [advance,hl]⟩
  | none =>
    have ridle (t : Fin n) (hbad : ∀ k, z.slots e=some k → t=k → birthAt z.config e=false) :
        route g [] (some t) z e = .keep := by
      unfold route
      rw [hL]
      cases hs : z.slots e with
      | none => rfl
      | some k =>
        change routeKnown [] (some t) z e k = .keep
        by_cases hk : t=k
        · have HE := hbad k hs hk
          simp [routeKnown,HE]
        · have hB : (some t == some k)=false :=
            Bool.eq_false_iff.mpr (fun H => hk (Option.some.inj (beq_iff_eq.mp H)))
          simp [routeKnown,hB]
    cases hs : z.slots e with
    | none =>
      have E (t : Fin n) : route g [] (some t) z e = .keep :=
        ridle t (by intro k H _; rw [hs] at H; cases H)
      have T : routeTwo g a b z e = .keep := by rw [routeTwo,E a,if_pos rfl,E b]
      exact False.elim (h T)
    | some k =>
      cases hb : birthAt z.config e with
      | false =>
        have E (t : Fin n) : route g [] (some t) z e = .keep := ridle t (fun _ _ _ => hb)
        have T : routeTwo g a b z e = .keep := by rw [routeTwo,E a,if_pos rfl,E b]
        exact False.elim (h T)
      | true =>
        by_cases hka : k=a
        · subst k
          have E := (target_birth_result hn g [] z e a hm hc hs hb).1
          have T : routeTwo g a b z e=.targetBirth a (rightNeighbor e) := by
            unfold routeTwo
            rw [E,if_neg (by intro H; cases H)]
          rw [T]
          exact recorded_birth hn g a b a z e hm hc (.inl rfl) hs hb
        · have eqidle (t : Fin n) (ht : k≠t) :
              route g [] (some t) z e = .keep := by
            apply ridle t
            intro j Hj htj
            rw [hs] at Hj
            exact (ht ((Option.some.inj Hj).trans htj.symm)).elim
          have E := eqidle a hka
          have hk : k=b := by
            apply Classical.byContradiction
            intro hkb
            have T : routeTwo g a b z e = .keep := by rw [routeTwo,E,if_pos rfl,eqidle b hkb]
            exact h T
          subst k
          have E' := (target_birth_result hn g [] z e b hm hc hs hb).1
          have T : routeTwo g a b z e=.targetBirth b (rightNeighbor e) := by
            unfold routeTwo
            rw [E,if_pos rfl,E']
          rw [T]
          exact recorded_birth hn g a b b z e hm hc (.inr rfl) hs hb

private theorem snoc_or_nil {α : Type} (u : List α) :
    u=[] ∨ ∃ v e, u=v++[e] := by
  cases he : u.reverse with
  | nil =>
    left
    have E := congrArg List.reverse he
    simpa using E
  | cons e v =>
    right
    have E := congrArg List.reverse he
    exact ⟨v.reverse,e,by simpa using E⟩

/-- On the original first terminal prefix, the last raw mark has one
authenticated event. A birth supplies its actual living marked head on
the post-mark ledger, not the frozen pre-exit cursor coordinates. -/
theorem first_exit_classified {p c n : Nat} {initial : Config p c n}
    (hn : 4≤n) (g : List (Fin n)) (a b k base : Fin n) (z : Cursor p c n)
    (ha : a∈g) (hb : b∈g) (hk : k∈g)
    (hz : Continuing initial a b k base z) (h0 : z.exit=none)
    (w : Word n) (h : FirstExit (fun u => (tape g a b base z u).exit.isSome=true) w) :
    ∃ u e r, w=u++[e] ∧
      let x := tape g a b base z u
      let y := tape g a b base z w
      x.exit=none ∧ y.exit=some r ∧ y.ledger=advance x.ledger e ∧
        Classified g a b x.ledger e y.ledger r := by
  rcases snoc_or_nil w with rfl | ⟨u,e,rfl⟩
  · have H := h.2
    change z.exit.isSome=true at H
    simp [h0] at H
  let x := tape g a b base z u
  have hpre := ((clean_child _ u e).mp h.1).2
  change ¬x.exit.isSome=true at hpre
  have xnone : x.exit=none := by
    cases E : x.exit with
    | none => rfl
    | some r => exact (hpre (by simp [E])).elim
  have G := (exit_or_continuing_tape hn g a b k base z ha hb hk (.inr hz) u).resolve_left hpre
  have after := tape_append g a b base z u e
  have hafter := h.2
  change (tape g a b base z (wordNext u e)).exit.isSome=true at hafter
  rw [after] at hafter
  have nonkeep : routeTwo g a b x.ledger e≠.keep := by
    intro H
    change (next g a b base x e).exit.isSome=true at hafter
    simp [next,xnone,H] at hafter
  refine ⟨u,e,routeTwo g a b x.ledger e,rfl,xnone,?_,?_,?_⟩
  · change (tape g a b base z (wordNext u e)).exit=_
    rw [after]
    change (next g a b base x e).exit=_
    simp [next,xnone,nonkeep]
  · change (tape g a b base z (wordNext u e)).ledger=_
    rw [after]
    exact projection g a b base x e
  · change Classified g a b x.ledger e (tape g a b base z (wordNext u e)).ledger _
    rw [after,projection]
    exact classify_route hn g a b x.ledger e G.1.markCover G.1.sourceCover nonkeep

/-- Canonical entry trace of the selected seven-window. -/
def observed {p c n : Nat} (x : Config p c n) (i : Fin (RankPhysical.rank x))
    (w : Word n) : Cursor p c n :=
  let S := entryScope x i
  tape S.group S.iTag S.jTag (entryBase x i) (entryCursor x i) w

def done {p c n : Nat} (x : Config p c n) (i : Fin (RankPhysical.rank x)) (w : Word n) : Prop :=
  (observed x i w).exit.isSome=true

theorem entry_classified {p c n : Nat} (hn : 4≤n) (x : Config p c n)
    (i : Fin (RankPhysical.rank x)) (hm : MCOV x) (hv : COV x)
    (short : 2*WindowSpan.span x i+2<n)
    (h1 : (x (WindowSpan.rootSite x (liftedSite i 1))).leader=false)
    (h2 : (x (WindowSpan.rootSite x (liftedSite i 2))).leader=false)
    (w : Word n) (h : FirstExit (done x i) w) :
    ∃ u e r, w=u++[e] ∧
      let x0 := observed x i u
      let y := observed x i w
      let S := entryScope x i
      x0.exit=none ∧ y.exit=some r ∧ y.ledger=advance x0.ledger e ∧
        Classified S.group S.iTag S.jTag x0.ledger e y.ledger r := by
  let S := entryScope x i
  have G : Continuing x S.iTag S.jTag S.kTag (entryBase x i) (entryCursor x i) :=
    (entry_continuing x i hm hv short h1 h2).1
  exact first_exit_classified hn S.group S.iTag S.jTag S.kTag (entryBase x i)
    (entryCursor x i) S.iIn S.jIn S.kIn G rfl w h

/-- The clock concerns precisely the observable with the authenticated
first exit above. Singleton continuation starts on that mark. -/
theorem entry_clock {p c n : Nat} (hn : 5≤n) (hc : 12≤c) (x : Config p c n)
    (i : Fin (RankPhysical.rank x)) (hm : MCOV x) (hv : COV x)
    (short : 2*WindowSpan.span x i+2<n)
    (h1 : (x (WindowSpan.rootSite x (liftedSite i 1))).leader=false)
    (h2 : (x (WindowSpan.rootSite x (liftedSite i 2))).leader=false) :
    IIDExpectedHittingTimeAtMost wordNext (done x i) []
      (WindowA0Restart.entryK c*n*(WindowSpan.span x i+1)) :=
  WindowA0Uniform.physical_entry_exit_mean hn hc x i hm hv short h1 h2

end L4.WindowA0FirstExit
