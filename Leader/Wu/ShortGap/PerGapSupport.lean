import Leader.Wu.ShortGap.PerGapTransferClass


set_option autoImplicit false


namespace PerGapOffPay


/--
An edge touches gap `g` exactly when one of the two scheduled physical sites
lies in the support read by `g`'s component potential.


This is the minimal support-based definition that makes endpoint framing imply
component framing for a genuinely two-site physical step. If `Phi` reads other
mutable physical data, that data must also be represented in `cfg`/`Site` or
the support must be widened accordingly.
-/
def touches
    {State Gap Site : Type} {n : Nat}
    (support : Gap → Site → Prop)
    (scheduledLeft scheduledRight : State → Fin n → Site)
    (g : Gap) (s : State) (e : Fin n) : Prop :=
  support g (scheduledLeft s e) ∨
    support g (scheduledRight s e)


/--
The missing `frameOutside` fact follows from three explicit ingredients:
`Phi` factors through the physical configuration, `phiOf g` depends only on
`support g`, and a scheduler step changes no site except its two endpoints.
-/
theorem frameOutside_of_support
    {State Gap Cell Site : Type} {n : Nat}
    (next : State → Fin n → State)
    (Phi : Gap → State → Nat)
    (cfg : State → Site → Cell)
    (support : Gap → Site → Prop)
    (phiOf : Gap → (Site → Cell) → Nat)
    (scheduledLeft scheduledRight : State → Fin n → Site)
    (phi_eq :
      ∀ (g : Gap) (s : State), Phi g s = phiOf g (cfg s))
    (phi_support :
      ∀ (g : Gap) (C D : Site → Cell),
        (∀ (x : Site), support g x → C x = D x) →
          phiOf g C = phiOf g D)
    (step_outside_eq :
      ∀ (s : State) (e : Fin n) (x : Site),
        x ≠ scheduledLeft s e →
        x ≠ scheduledRight s e →
        cfg (next s e) x = cfg s x) :
    ∀ (g : Gap) (s : State) (e : Fin n),
      ¬ touches support scheduledLeft scheduledRight g s e →
        Phi g (next s e) = Phi g s := by
  intro g s e hnot
  rw [phi_eq g (next s e), phi_eq g s]
  apply phi_support g (cfg (next s e)) (cfg s)
  intro x hx
  apply step_outside_eq s e x
  · intro hxl
    apply hnot
    unfold touches
    exact Or.inl (hxl ▸ hx)
  · intro hxr
    apply hnot
    unfold touches
    exact Or.inr (hxr ▸ hx)


/--
The locality theorem now needs no independent `frameOutside` parameter:
the support bridge above supplies it from physical endpoint framing.
-/
theorem ordinaryLocality_of_support
    {State Gap Cell Site : Type} {n : Nat}
    (next : State → Fin n → State)
    (Phi : Gap → State → Nat)
    (enabled : Gap → State → Prop)
    (cfg : State → Site → Cell)
    (support : Gap → Site → Prop)
    (phiOf : Gap → (Site → Cell) → Nat)
    (scheduledLeft scheduledRight : State → Fin n → Site)
    (phi_eq :
      ∀ (g : Gap) (s : State), Phi g s = phiOf g (cfg s))
    (phi_support :
      ∀ (g : Gap) (C D : Site → Cell),
        (∀ (x : Site), support g x → C x = D x) →
          phiOf g C = phiOf g D)
    (step_outside_eq :
      ∀ (s : State) (e : Fin n) (x : Site),
        x ≠ scheduledLeft s e →
        x ≠ scheduledRight s e →
        cfg (next s e) x = cfg s x) :
    OrdinaryLocality next Phi
      (fun s => ∀ g e, ¬ transferAt next Phi g s e)
      enabled (touches support scheduledLeft scheduledRight) := by
  exact ordinaryLocality_of_derived next Phi enabled
    (touches support scheduledLeft scheduledRight)
    (frameOutside_of_support next Phi cfg support phiOf
      scheduledLeft scheduledRight phi_eq phi_support step_outside_eq)


/--
Per-gap off-pay follows immediately from the derived ordinary locality. Thus
`frameOutside` has disappeared from the caller interface: its replacement is
the checkable support factorization plus the two-endpoint physical frame law.
-/
theorem perGap_offPay_of_support
    {State Gap Cell Site : Type} {n : Nat}
    (next : State → Fin n → State)
    (Phi : Gap → State → Nat)
    (enabled : Gap → State → Prop)
    (cfg : State → Site → Cell)
    (support : Gap → Site → Prop)
    (phiOf : Gap → (Site → Cell) → Nat)
    (scheduledLeft scheduledRight : State → Fin n → Site)
    (phi_eq :
      ∀ (g : Gap) (s : State), Phi g s = phiOf g (cfg s))
    (phi_support :
      ∀ (g : Gap) (C D : Site → Cell),
        (∀ (x : Site), support g x → C x = D x) →
          phiOf g C = phiOf g D)
    (step_outside_eq :
      ∀ (s : State) (e : Fin n) (x : Site),
        x ≠ scheduledLeft s e →
        x ≠ scheduledRight s e →
        cfg (next s e) x = cfg s x) :
    ∀ (g : Gap) (s : State),
      (∀ (g' : Gap) (e : Fin n), ¬ transferAt next Phi g' s e) →
      ¬ enabled g s →
      (List.ofFn (fun e : Fin n => Phi g (next s e))).sum ≤
        n * Phi g s := by
  exact perGap_offPay_of_ordinaryLocality
    next Phi
    (fun s => ∀ g e, ¬ transferAt next Phi g s e)
    enabled
    (touches support scheduledLeft scheduledRight)
    (ordinaryLocality_of_support next Phi enabled cfg support phiOf
      scheduledLeft scheduledRight phi_eq phi_support step_outside_eq)


/-- Distinct gap supports never overlap at one physical site. -/
def SupportDisjoint
    {Gap Site : Type}
    (support : Gap → Site → Prop) : Prop :=
  ∀ (g g' : Gap) (x : Site),
    g ≠ g' → support g x → ¬ support g' x


/--
Inhabitation-free form of “at most two gaps are touched”. No three pairwise
distinct gaps can all touch one two-site scheduler edge.


This form is stronger for downstream contradiction arguments and avoids the
false empty-`Gap` corner case in an unconditional `∃ g1 g2, ...` statement.
-/
theorem at_most_two_touched
    {State Gap Site : Type} {n : Nat}
    (support : Gap → Site → Prop)
    (scheduledLeft scheduledRight : State → Fin n → Site)
    (support_disjoint : SupportDisjoint support) :
    ∀ (s : State) (e : Fin n) (g1 g2 g3 : Gap),
      touches support scheduledLeft scheduledRight g1 s e →
      touches support scheduledLeft scheduledRight g2 s e →
      touches support scheduledLeft scheduledRight g3 s e →
      ¬ (g1 ≠ g2 ∧ g1 ≠ g3 ∧ g2 ≠ g3) := by
  intro s e g1 g2 g3 h1 h2 h3 hdistinct
  unfold SupportDisjoint at support_disjoint
  unfold touches at h1 h2 h3
  cases h1 with
  | inl h1l =>
      cases h2 with
      | inl h2l =>
          exact (support_disjoint g1 g2 (scheduledLeft s e)
            hdistinct.1 h1l) h2l
      | inr h2r =>
          cases h3 with
          | inl h3l =>
              exact (support_disjoint g1 g3 (scheduledLeft s e)
                hdistinct.2.1 h1l) h3l
          | inr h3r =>
              exact (support_disjoint g2 g3 (scheduledRight s e)
                hdistinct.2.2 h2r) h3r
  | inr h1r =>
      cases h2 with
      | inl h2l =>
          cases h3 with
          | inl h3l =>
              exact (support_disjoint g2 g3 (scheduledLeft s e)
                hdistinct.2.2 h2l) h3l
          | inr h3r =>
              exact (support_disjoint g1 g3 (scheduledRight s e)
                hdistinct.2.1 h1r) h3r
      | inr h2r =>
          exact (support_disjoint g1 g2 (scheduledRight s e)
            hdistinct.1 h1r) h2r


/--
If `Gap` is inhabited, the requested covering formulation follows: for each
edge there are two gap names covering every touched gap. The `[Inhabited Gap]`
assumption is necessary only for the case where no gap is touched; without it,
the requested existential statement is false when `Gap` is empty.
-/
theorem at_most_two_touched_exists
    {State Gap Site : Type} {n : Nat} [Inhabited Gap]
    (support : Gap → Site → Prop)
    (scheduledLeft scheduledRight : State → Fin n → Site)
    (support_disjoint : SupportDisjoint support) :
    ∀ (s : State) (e : Fin n),
      ∃ g1 g2 : Gap,
        ∀ g : Gap,
          touches support scheduledLeft scheduledRight g s e →
            g = g1 ∨ g = g2 := by
  intro s e
  cases Classical.em
      (∃ g : Gap, touches support scheduledLeft scheduledRight g s e) with
  | inr hNone =>
      refine ⟨default, default, ?_⟩
      intro g hg
      exact (hNone ⟨g, hg⟩).elim
  | inl hAny =>
      cases hAny with
      | intro g1 hg1 =>
          cases Classical.em
              (∃ g : Gap,
                touches support scheduledLeft scheduledRight g s e ∧
                  g ≠ g1) with
          | inr hSecond =>
              refine ⟨g1, g1, ?_⟩
              intro g hg
              have hEq : g = g1 := Classical.byContradiction (fun hne =>
                hSecond ⟨g, hg, hne⟩)
              exact Or.inl hEq
          | inl hSecond =>
              cases hSecond with
              | intro g2 hg2 =>
                  refine ⟨g1, g2, ?_⟩
                  intro g hg
                  exact Classical.byContradiction (fun hcover => by
                    have h12 : g1 ≠ g2 := by
                      intro hEq
                      exact hg2.2 hEq.symm
                    have h1g : g1 ≠ g := by
                      intro hEq
                      apply hcover
                      exact Or.inl hEq.symm
                    have h2g : g2 ≠ g := by
                      intro hEq
                      apply hcover
                      exact Or.inr hEq.symm
                    exact (at_most_two_touched support
                      scheduledLeft scheduledRight support_disjoint
                      s e g1 g2 g hg1 hg2.1 hg)
                        ⟨h12, h1g, h2g⟩)


/--
If a component actually changes on an edge, that edge must touch its support.
This is the direct “at most two components can change” bridge.
-/
theorem changed_implies_touches_of_support
    {State Gap Cell Site : Type} {n : Nat}
    (next : State → Fin n → State)
    (Phi : Gap → State → Nat)
    (cfg : State → Site → Cell)
    (support : Gap → Site → Prop)
    (phiOf : Gap → (Site → Cell) → Nat)
    (scheduledLeft scheduledRight : State → Fin n → Site)
    (phi_eq :
      ∀ (g : Gap) (s : State), Phi g s = phiOf g (cfg s))
    (phi_support :
      ∀ (g : Gap) (C D : Site → Cell),
        (∀ (x : Site), support g x → C x = D x) →
          phiOf g C = phiOf g D)
    (step_outside_eq :
      ∀ (s : State) (e : Fin n) (x : Site),
        x ≠ scheduledLeft s e →
        x ≠ scheduledRight s e →
        cfg (next s e) x = cfg s x) :
    ∀ (g : Gap) (s : State) (e : Fin n),
      Phi g (next s e) ≠ Phi g s →
        touches support scheduledLeft scheduledRight g s e := by
  intro g s e hchanged
  exact Classical.byContradiction (fun hnot =>
    hchanged
      (frameOutside_of_support next Phi cfg support phiOf
        scheduledLeft scheduledRight phi_eq phi_support
        step_outside_eq g s e hnot))


/-- No three pairwise distinct per-gap components can all change on one edge. -/
theorem at_most_two_changed
    {State Gap Cell Site : Type} {n : Nat}
    (next : State → Fin n → State)
    (Phi : Gap → State → Nat)
    (cfg : State → Site → Cell)
    (support : Gap → Site → Prop)
    (phiOf : Gap → (Site → Cell) → Nat)
    (scheduledLeft scheduledRight : State → Fin n → Site)
    (phi_eq :
      ∀ (g : Gap) (s : State), Phi g s = phiOf g (cfg s))
    (phi_support :
      ∀ (g : Gap) (C D : Site → Cell),
        (∀ (x : Site), support g x → C x = D x) →
          phiOf g C = phiOf g D)
    (step_outside_eq :
      ∀ (s : State) (e : Fin n) (x : Site),
        x ≠ scheduledLeft s e →
        x ≠ scheduledRight s e →
        cfg (next s e) x = cfg s x)
    (support_disjoint : SupportDisjoint support) :
    ∀ (s : State) (e : Fin n) (g1 g2 g3 : Gap),
      Phi g1 (next s e) ≠ Phi g1 s →
      Phi g2 (next s e) ≠ Phi g2 s →
      Phi g3 (next s e) ≠ Phi g3 s →
      ¬ (g1 ≠ g2 ∧ g1 ≠ g3 ∧ g2 ≠ g3) := by
  intro s e g1 g2 g3 h1 h2 h3
  apply at_most_two_touched support scheduledLeft scheduledRight
    support_disjoint s e g1 g2 g3
  · exact changed_implies_touches_of_support next Phi cfg support phiOf
      scheduledLeft scheduledRight phi_eq phi_support step_outside_eq
      g1 s e h1
  · exact changed_implies_touches_of_support next Phi cfg support phiOf
      scheduledLeft scheduledRight phi_eq phi_support step_outside_eq
      g2 s e h2
  · exact changed_implies_touches_of_support next Phi cfg support phiOf
      scheduledLeft scheduledRight phi_eq phi_support step_outside_eq
      g3 s e h3


/-- A derived transfer/rise edge for `g` must touch `g`'s support. -/
theorem transferAt_implies_touches_of_support
    {State Gap Cell Site : Type} {n : Nat}
    (next : State → Fin n → State)
    (Phi : Gap → State → Nat)
    (cfg : State → Site → Cell)
    (support : Gap → Site → Prop)
    (phiOf : Gap → (Site → Cell) → Nat)
    (scheduledLeft scheduledRight : State → Fin n → Site)
    (phi_eq :
      ∀ (g : Gap) (s : State), Phi g s = phiOf g (cfg s))
    (phi_support :
      ∀ (g : Gap) (C D : Site → Cell),
        (∀ (x : Site), support g x → C x = D x) →
          phiOf g C = phiOf g D)
    (step_outside_eq :
      ∀ (s : State) (e : Fin n) (x : Site),
        x ≠ scheduledLeft s e →
        x ≠ scheduledRight s e →
        cfg (next s e) x = cfg s x) :
    ∀ (g : Gap) (s : State) (e : Fin n),
      transferAt next Phi g s e →
        touches support scheduledLeft scheduledRight g s e := by
  intro g s e hRise
  apply changed_implies_touches_of_support next Phi cfg support phiOf
    scheduledLeft scheduledRight phi_eq phi_support step_outside_eq
    g s e
  intro hEq
  unfold transferAt at hRise
  rw [hEq] at hRise
  exact Nat.lt_irrefl _ hRise


/-- No three pairwise distinct gaps can all be derived transfer gaps on one edge. -/
theorem at_most_two_transferAt
    {State Gap Cell Site : Type} {n : Nat}
    (next : State → Fin n → State)
    (Phi : Gap → State → Nat)
    (cfg : State → Site → Cell)
    (support : Gap → Site → Prop)
    (phiOf : Gap → (Site → Cell) → Nat)
    (scheduledLeft scheduledRight : State → Fin n → Site)
    (phi_eq :
      ∀ (g : Gap) (s : State), Phi g s = phiOf g (cfg s))
    (phi_support :
      ∀ (g : Gap) (C D : Site → Cell),
        (∀ (x : Site), support g x → C x = D x) →
          phiOf g C = phiOf g D)
    (step_outside_eq :
      ∀ (s : State) (e : Fin n) (x : Site),
        x ≠ scheduledLeft s e →
        x ≠ scheduledRight s e →
        cfg (next s e) x = cfg s x)
    (support_disjoint : SupportDisjoint support) :
    ∀ (s : State) (e : Fin n) (g1 g2 g3 : Gap),
      transferAt next Phi g1 s e →
      transferAt next Phi g2 s e →
      transferAt next Phi g3 s e →
      ¬ (g1 ≠ g2 ∧ g1 ≠ g3 ∧ g2 ≠ g3) := by
  intro s e g1 g2 g3 h1 h2 h3
  apply at_most_two_touched support scheduledLeft scheduledRight
    support_disjoint s e g1 g2 g3
  · exact transferAt_implies_touches_of_support next Phi cfg support phiOf
      scheduledLeft scheduledRight phi_eq phi_support step_outside_eq
      g1 s e h1
  · exact transferAt_implies_touches_of_support next Phi cfg support phiOf
      scheduledLeft scheduledRight phi_eq phi_support step_outside_eq
      g2 s e h2
  · exact transferAt_implies_touches_of_support next Phi cfg support phiOf
      scheduledLeft scheduledRight phi_eq phi_support step_outside_eq
      g3 s e h3


/--
With an inhabited gap type, every derived transfer set on one scheduler edge is
covered by at most two gap names.
-/
theorem at_most_two_transferAt_exists
    {State Gap Cell Site : Type} {n : Nat} [Inhabited Gap]
    (next : State → Fin n → State)
    (Phi : Gap → State → Nat)
    (cfg : State → Site → Cell)
    (support : Gap → Site → Prop)
    (phiOf : Gap → (Site → Cell) → Nat)
    (scheduledLeft scheduledRight : State → Fin n → Site)
    (phi_eq :
      ∀ (g : Gap) (s : State), Phi g s = phiOf g (cfg s))
    (phi_support :
      ∀ (g : Gap) (C D : Site → Cell),
        (∀ (x : Site), support g x → C x = D x) →
          phiOf g C = phiOf g D)
    (step_outside_eq :
      ∀ (s : State) (e : Fin n) (x : Site),
        x ≠ scheduledLeft s e →
        x ≠ scheduledRight s e →
        cfg (next s e) x = cfg s x)
    (support_disjoint : SupportDisjoint support) :
    ∀ (s : State) (e : Fin n),
      ∃ g1 g2 : Gap,
        ∀ g : Gap,
          transferAt next Phi g s e → g = g1 ∨ g = g2 := by
  intro s e
  cases at_most_two_touched_exists support scheduledLeft scheduledRight
      support_disjoint s e with
  | intro g1 hrest =>
      cases hrest with
      | intro g2 hcover =>
          refine ⟨g1, g2, ?_⟩
          intro g hRise
          apply hcover g
          exact transferAt_implies_touches_of_support next Phi cfg support
            phiOf scheduledLeft scheduledRight phi_eq phi_support
            step_outside_eq g s e hRise


/-!
## Protocol-obligation audit


The proposed `touches` definition is the right one for this bridge: it is
exactly intersection of a two-site mutation footprint with the support of the
component potential. It should be changed only if a protocol step can mutate
additional physical data read by `Phi`; in that case the mutation footprint,
not the proof, must be enlarged.


Substantive protocol obligations:
* `phi_support` is real locality content: `Phi g` must genuinely ignore every
  physical site outside `support g`.
* `SupportDisjoint support` is real ownership-separation content: two distinct
  gaps may not read the same owned physical site. It proves non-overlap, not
  coverage. Calling the supports a literal partition additionally requires a
  coverage theorem such as `∀ x, ∃ g, support g x` if coverage is needed.


Bookkeeping / adapter obligations:
* `phi_eq` identifies the existing state-level `Phi` with its configuration
  presentation `phiOf`; it is often definitional or a short projection lemma.
* `step_outside_eq` is the abstract form of
  `PositiveGapLocalProjectionNoGo.PairStep.outside_eq`. The repository already
  proves the underlying two-endpoint frame property. One adapter still has to
  identify `PairStep.before/after/left/right` with
  `cfg s/cfg (next s e)/scheduledLeft s e/scheduledRight s e`.


So the user's diagnosis is essentially correct, with one refinement:
`phi_support` and support non-overlap are substantive; endpoint framing is
already present physically; but non-overlap alone is not full partitioning.
-/


end PerGapOffPay


#print axioms PerGapOffPay.frameOutside_of_support
#print axioms PerGapOffPay.ordinaryLocality_of_support
#print axioms PerGapOffPay.perGap_offPay_of_support
#print axioms PerGapOffPay.at_most_two_touched
#print axioms PerGapOffPay.at_most_two_touched_exists
#print axioms PerGapOffPay.changed_implies_touches_of_support
#print axioms PerGapOffPay.at_most_two_changed
#print axioms PerGapOffPay.transferAt_implies_touches_of_support
#print axioms PerGapOffPay.at_most_two_transferAt
#print axioms PerGapOffPay.at_most_two_transferAt_exists
