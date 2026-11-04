import Leader.PPL.CompletionRunner.ForcedConstructFreshPersist
import Leader.PPL.SPLEntry.SelectedProvenance
import Leader.PPL.TransitionFacts
import Leader.PPL.Elim.RowE

/-!
# Step-parametric Lemma 4: one-step bridge between P_PL prime and P_PL

Same start state, same selected pair.  If the two preludes agree on the
selected pair,

  `preTokenPair hpsi (C e) (C e⁺) = l18Risk2PreTokenPair hpsi (C e) (C e⁺)`

(`PreludeAgree`; this holds under `CDLAt ring root C`, see
`preludeAgree_of_CDLAt`), then:

* physical bridge (`pprimeStep_agree`): at every site the prime and the
  ordinary post-states agree on `tokenB`, `tokenW`, `dist` and `last`
  (`PhysAgree`).  They may differ on `id`, `leader`, `mode` and the
  Algorithm-5 fields (c = 1 Detect/Construct);
* ghost bridge (`ghostStepPrime_bridge`): `ghostStepPrime` and `ghostStep`
  have the same black map, the same white map and the same completion log,
  and their physical parts are `PhysAgree` site by site.

Transfers proved through the bridge:

* `ghostSound_ghostStepPrime_of_preludeAgree`: one prime ghost step preserves
  `GhostSound` whenever the prelude agrees (in particular under `CDLAt`),
  from the ordinary one-step soundness `coverageLeavesGhostStep_sound`;
* `ghostSound_ghostRunPrime_of_preludeAlong`: the same along a prime run
  whose every visited selected pair satisfies `PreludeAgree`.

The unrestricted `PrimeSelectedPairSound` of `PrimeInstance.lean` is not
obtained: the bridge side condition is not available for an arbitrary
sound `G`.

The private L18 provenance lemmas and the private ordinary one-step
soundness are reached through their mangled names (Lean 4.33 rejects
`open private`; `TransitionFacts.lean` uses the same technique).
-/

namespace PPL
namespace Lemma4Generic

set_option autoImplicit false
set_option Elab.async false

open PPL.Convergence.L18

/-! ## 0. Access to private upstream lemmas -/

open Lean Elab Term Meta in
/-- `l18prov% "name"` elaborates to the private declaration `name` of
`Convergence/L18PrimeSelectedProvenance.lean`. -/
elab "l18prov% " s:str : term => do
  let n : Name :=
    ((((((`_private.Leader.PPL.SPLEntry.SelectedProvenance).num 0).str
      "PPL").str "Convergence").str "L18").str s.getString)
  mkConstWithFreshMVarLevels n

open Lean Elab Term Meta in
/-- `covleaves% "name"` elaborates to the private declaration `name` of
`TokenCorrectnessLemma4CoverageLeaves.lean`. -/
elab "covleaves% " s:str : term => do
  let n : Name :=
    (((`_private.Leader.PPL.TokenCompletion.CoverageLeaves).num 0).str
      "PPL").str s.getString
  mkConstWithFreshMVarLevels n

/-- Re-export of the private `l18PrimeProvPPrimeMoveToken_tokens`. -/
theorem pb_pprimeMoveToken_tokens {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (kind : TokenKind) (l r : State psi kappa) :
    tokenAt kind (pprimeMoveToken hpsi kind l r).1 =
        tokenAt kind (PPL.moveToken hpsi kind l r).1 ∧
      tokenAt kind (pprimeMoveToken hpsi kind l r).2 =
        tokenAt kind (PPL.moveToken hpsi kind l r).2 :=
  (l18prov% "l18PrimeProvPPrimeMoveToken_tokens") hpsi kind l r

/-- Re-export of the private `l18PrimeProvMoveToken_tokens_congr`. -/
theorem pb_moveToken_tokens_congr {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (kind : TokenKind) (l r l' r' : State psi kappa)
    (hldist : l.dist = l'.dist) (hllast : l.last = l'.last)
    (hlid : l.id = l'.id) (hltok : tokenAt kind l = tokenAt kind l')
    (hrdist : r.dist = r'.dist) (hrlast : r.last = r'.last)
    (hrtok : tokenAt kind r = tokenAt kind r') :
    tokenAt kind (PPL.moveToken hpsi kind l r).1 =
        tokenAt kind (PPL.moveToken hpsi kind l' r').1 ∧
      tokenAt kind (PPL.moveToken hpsi kind l r).2 =
        tokenAt kind (PPL.moveToken hpsi kind l' r').2 :=
  (l18prov% "l18PrimeProvMoveToken_tokens_congr") hpsi kind l r l' r'
    hldist hllast hlid hltok hrdist hrlast hrtok

/-- The bridge side condition: both preludes agree on the selected pair. -/
def PreludeAgree {psi kappa : Nat} (hpsi : 2 ≤ psi) (l r : State psi kappa) :
    Prop :=
  PPL.Safety.PeacefulProps.preTokenPair hpsi l r = l18Risk2PreTokenPair hpsi l r

/-- Re-export of the private `l18PrimeProvPreTokenPair_eq`: under `CDLAt`
the two preludes agree on every selected pair. -/
theorem preludeAgree_of_CDLAt {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (root : Fin n) (C : Config n psi kappa) (e : Fin n)
    (hCDL : CDLAt ring root C) :
    PreludeAgree hpsi (C e) (C (ring.rightNeighbor e)) :=
  (l18prov% "l18PrimeProvPreTokenPair_eq") hpsi ring root C e hCDL

/-! ## 1. Field frames of one MoveToken call -/

/-- Two states that agree off the erased token and on that token are equal. -/
theorem eq_of_eraseKindToken {psi kappa : Nat} (kind : TokenKind)
    (a b : State psi kappa)
    (he : PPL.eraseKindToken kind a = PPL.eraseKindToken kind b)
    (ht : tokenAt kind a = tokenAt kind b) : a = b := by
  cases a
  cases b
  cases kind <;> simp_all [PPL.eraseKindToken, tokenAt]

/-- The initiator of a MoveToken call keeps `id`, `dist`, `last` and the
other-kind token. -/
theorem moveToken_left_frame {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (kind : TokenKind) (l r : State psi kappa) :
    (PPL.moveToken hpsi kind l r).1.id = l.id ∧
      (PPL.moveToken hpsi kind l r).1.dist = l.dist ∧
      (PPL.moveToken hpsi kind l r).1.last = l.last ∧
      (kind = .black → (PPL.moveToken hpsi kind l r).1.tokenW = l.tokenW) ∧
      (kind = .white → (PPL.moveToken hpsi kind l r).1.tokenB = l.tokenB) := by
  have h' := congrArg
    (fun q : State psi kappa => (q.id, q.dist, q.last, q.tokenB, q.tokenW))
    (PPL.moveToken_initiator_fields hpsi kind l r)
  cases kind <;> simp_all [PPL.eraseKindToken]

/-- The responder of a MoveToken call keeps `dist`, `last` and the
other-kind token (in both the plain and the birth branch). -/
theorem moveToken_right_frame {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (kind : TokenKind) (l r : State psi kappa) :
    (PPL.moveToken hpsi kind l r).2.dist = r.dist ∧
      (PPL.moveToken hpsi kind l r).2.last = r.last ∧
      (kind = .black → (PPL.moveToken hpsi kind l r).2.tokenW = r.tokenW) ∧
      (kind = .white → (PPL.moveToken hpsi kind l r).2.tokenB = r.tokenB) := by
  rcases PPL.moveToken_responder_fields hpsi kind l r with h | h
  · have h' := congrArg
      (fun q : State psi kappa => (q.dist, q.last, q.tokenB, q.tokenW)) h
    clear h
    cases kind <;> simp_all [PPL.eraseKindTokenId, PPL.eraseKindToken]
  · have h' := congrArg
      (fun q : State psi kappa => (q.dist, q.last, q.tokenB, q.tokenW)) h
    clear h
    cases kind <;>
      simp_all [PPL.eraseKindTokenId, PPL.eraseKindToken, PPL.birthFields]

/-- The prime MoveToken initiator is exactly the ordinary one. -/
theorem pprimeMoveToken_left_eq {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (kind : TokenKind) (l r : State psi kappa) :
    (pprimeMoveToken hpsi kind l r).1 = (PPL.moveToken hpsi kind l r).1 := by
  apply eq_of_eraseKindToken kind
  · have h1 := PPL.moveToken_initiator_fields hpsi kind l { r with mode := false }
    have h2 := PPL.moveToken_initiator_fields hpsi kind l r
    exact h1.trans h2.symm
  · exact (pb_pprimeMoveToken_tokens hpsi kind l r).1

/-- The prime MoveToken responder keeps `dist`, `last` and the other-kind
token. -/
theorem pprimeMoveToken_right_frame {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (kind : TokenKind) (l r : State psi kappa) :
    (pprimeMoveToken hpsi kind l r).2.dist = r.dist ∧
      (pprimeMoveToken hpsi kind l r).2.last = r.last ∧
      (kind = .black → (pprimeMoveToken hpsi kind l r).2.tokenW = r.tokenW) ∧
      (kind = .white → (pprimeMoveToken hpsi kind l r).2.tokenB = r.tokenB) := by
  have h := moveToken_right_frame hpsi kind l { r with mode := false }
  exact h

/-! ## 2. The physical bridge -/

/-- Agreement on the fields every Lemma-4 step Prop reads. -/
def PhysAgree {psi kappa : Nat} (a b : State psi kappa) : Prop :=
  a.tokenB = b.tokenB ∧ a.tokenW = b.tokenW ∧ a.dist = b.dist ∧ a.last = b.last

/-- Algorithm 5 preserves `PhysAgree` on both sides. -/
theorem eliminateLeaders_physAgree {psi kappa : Nat}
    (l r l' r' : State psi kappa)
    (hl : PhysAgree l l') (hr : PhysAgree r r') :
    PhysAgree (PPL.eliminateLeaders l r).1 (PPL.eliminateLeaders l' r').1 ∧
      PhysAgree (PPL.eliminateLeaders l r).2 (PPL.eliminateLeaders l' r').2 := by
  have a := PPL.Elim.otherView_eliminateLeaders_left l r
  have b := PPL.Elim.otherView_eliminateLeaders_left l' r'
  have c := PPL.Elim.otherView_eliminateLeaders_right l r
  have d := PPL.Elim.otherView_eliminateLeaders_right l' r'
  simp only [PPL.Elim.otherView, PPL.Elim.OtherFields.mk.injEq] at a b c d
  unfold PhysAgree at *
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [a.2.2.2.1, b.2.2.2.1, hl.1]
  · rw [a.2.2.2.2.1, b.2.2.2.2.1, hl.2.1]
  · rw [a.2.1, b.2.1, hl.2.2.1]
  · rw [a.2.2.1, b.2.2.1, hl.2.2.2]
  · rw [c.2.2.2.1, d.2.2.2.1, hr.1]
  · rw [c.2.2.2.2.1, d.2.2.2.2.1, hr.2.1]
  · rw [c.2.1, d.2.1, hr.2.2.1]
  · rw [c.2.2.1, d.2.2.1, hr.2.2.2]

/-- The two MoveToken calls, from one and the same prelude pair: prime and
ordinary results are `PhysAgree` on both sides. -/
theorem moves_physAgree {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (a b : State psi kappa) :
    let B := pprimeMoveToken hpsi .black a b
    let A := PPL.moveToken hpsi .black a b
    PhysAgree (pprimeMoveToken hpsi .white B.1 B.2).1
        (PPL.moveToken hpsi .white A.1 A.2).1 ∧
      PhysAgree (pprimeMoveToken hpsi .white B.1 B.2).2
        (PPL.moveToken hpsi .white A.1 A.2).2 := by
  intro B A
  have hB1 : B.1 = A.1 := pprimeMoveToken_left_eq hpsi .black a b
  have hBt := (pb_pprimeMoveToken_tokens hpsi .black a b).2
  have hBf := pprimeMoveToken_right_frame hpsi .black a b
  have hAf := moveToken_right_frame hpsi .black a b
  -- the responders after the black call agree on dist, last, tokenB, tokenW
  have hr_dist : B.2.dist = A.2.dist := hBf.1.trans hAf.1.symm
  have hr_last : B.2.last = A.2.last := hBf.2.1.trans hAf.2.1.symm
  have hr_tokW : B.2.tokenW = A.2.tokenW :=
    (hBf.2.2.1 rfl).trans (hAf.2.2.1 rfl).symm
  have hr_tokB : B.2.tokenB = A.2.tokenB := hBt
  -- white call
  have hW1 : (pprimeMoveToken hpsi .white B.1 B.2).1 =
      (PPL.moveToken hpsi .white B.1 B.2).1 :=
    pprimeMoveToken_left_eq hpsi .white B.1 B.2
  have hWt := pb_pprimeMoveToken_tokens hpsi .white B.1 B.2
  have hC := pb_moveToken_tokens_congr hpsi .white B.1 B.2 A.1 A.2
    (by rw [hB1]) (by rw [hB1]) (by rw [hB1]) (by rw [hB1])
    hr_dist hr_last (by simpa [tokenAt] using hr_tokW)
  have hLB := moveToken_left_frame hpsi .white B.1 B.2
  have hLA := moveToken_left_frame hpsi .white A.1 A.2
  have hRB := pprimeMoveToken_right_frame hpsi .white B.1 B.2
  have hRA := moveToken_right_frame hpsi .white A.1 A.2
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [hW1, hLB.2.2.2.2 rfl, hLA.2.2.2.2 rfl, hB1]
  · have := hWt.1.trans hC.1
    simpa [tokenAt] using this
  · rw [hW1, hLB.2.1, hLA.2.1, hB1]
  · rw [hW1, hLB.2.2.1, hLA.2.2.1, hB1]
  · rw [hRB.2.2.2 rfl, hRA.2.2.2 rfl, hr_tokB]
  · have := hWt.2.trans hC.2
    simpa [tokenAt] using this
  · rw [hRB.1, hRA.1, hr_dist]
  · rw [hRB.2.1, hRA.2.1, hr_last]

/-- Local bridge: under `PreludeAgree`, the prime and the ordinary local
transitions are `PhysAgree` on both sides. -/
theorem pprimePpl_physAgree {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (l r : State psi kappa) (hpre : PreludeAgree hpsi l r) :
    PhysAgree (pprimePpl hpsi l r).1 (PPL.ppl hpsi l r).1 ∧
      PhysAgree (pprimePpl hpsi l r).2 (PPL.ppl hpsi l r).2 := by
  have hP : pprimeCreateLeader hpsi l r =
      (let p := l18Risk2PreTokenPair hpsi l r
       let q := pprimeMoveToken hpsi .black p.1 p.2
       pprimeMoveToken hpsi .white q.1 q.2) := rfl
  have hO : PPL.createLeader hpsi l r =
      (let p := PPL.Safety.PeacefulProps.preTokenPair hpsi l r
       let q := PPL.moveToken hpsi .black p.1 p.2
       PPL.moveToken hpsi .white q.1 q.2) := rfl
  have hm := moves_physAgree hpsi
    (PPL.Safety.PeacefulProps.preTokenPair hpsi l r).1
    (PPL.Safety.PeacefulProps.preTokenPair hpsi l r).2
  unfold PreludeAgree at hpre
  rw [← hpre] at hP
  unfold pprimePpl PPL.ppl
  rw [hP, hO]
  exact eliminateLeaders_physAgree _ _ _ _ hm.1 hm.2

/-- One population-protocol step, site by site. -/
theorem step_apply {n : Nat} (P : PopulationProtocol) (ring : DirectedRing n)
    (C : P.Configuration n) (e i : Fin n) :
    PopulationProtocol.step P ring C e i =
      if i = e then (P.transition (C e) (C (ring.rightNeighbor e))).1
      else if i = ring.rightNeighbor e then
        (P.transition (C e) (C (ring.rightNeighbor e))).2
      else C i := rfl

/-- Physical bridge: under `PreludeAgree` on the selected pair, the prime
and the ordinary steps are `PhysAgree` at every site. -/
theorem pprimeStep_physAgree {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (C : Config n psi kappa) (e : Fin n)
    (hpre : PreludeAgree hpsi (C e) (C (ring.rightNeighbor e))) (i : Fin n) :
    PhysAgree (pprimeStep ring C e i)
      (PopulationProtocol.step (PPL.protocol psi kappa) ring C e i) := by
  have hloc := pprimePpl_physAgree hpsi (C e) (C (ring.rightNeighbor e)) hpre
  have hT : pprimeTransition psi kappa = fun l r => pprimePpl hpsi l r := by
    funext l r
    simp [pprimeTransition, hpsi]
  have hT' : PPL.transition psi kappa = fun l r => PPL.ppl hpsi l r := by
    funext l r
    exact PPL.transition_eq_ppl hpsi l r
  show PhysAgree
    (if i = e then
        ((pprimeProtocol psi kappa).transition (C e) (C (ring.rightNeighbor e))).1
      else if i = ring.rightNeighbor e then
        ((pprimeProtocol psi kappa).transition (C e) (C (ring.rightNeighbor e))).2
      else C i)
    (if i = e then
        ((PPL.protocol psi kappa).transition (C e) (C (ring.rightNeighbor e))).1
      else if i = ring.rightNeighbor e then
        ((PPL.protocol psi kappa).transition (C e) (C (ring.rightNeighbor e))).2
      else C i)
  simp only [pprimeProtocol, PPL.protocol, hT, hT']
  have key : ∀ (a a' b b' c : State psi kappa), PhysAgree a a' → PhysAgree b b' →
      PhysAgree (if i = e then a else if i = ring.rightNeighbor e then b else c)
        (if i = e then a' else if i = ring.rightNeighbor e then b' else c) := by
    intro a a' b b' c ha hb
    by_cases h1 : i = e
    · rw [if_pos h1, if_pos h1]
      exact ha
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : i = ring.rightNeighbor e
      · rw [if_pos h2, if_pos h2]
        exact hb
      · rw [if_neg h2, if_neg h2]
        exact ⟨rfl, rfl, rfl, rfl⟩
  exact key _ _ _ _ _ hloc.1 hloc.2

/-! ## 3. The ghost bridge -/

/-- The prime ghost step, in terms of the public mirror. -/
theorem ghostStepPrime_unfold {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (t : Nat) (G : GhostConfig n psi kappa) (e : Fin n) :
    let rs := ring.rightNeighbor e
    let p := l18Risk2PreTokenPair hpsi (G.phys e) (G.phys rs)
    let gb := pfpGhostMoveToken hpsi .black t e p.1 p.2 (G.black e) (G.black rs)
    let q := pprimeMoveToken hpsi .black p.1 p.2
    let gw := pfpGhostMoveToken hpsi .white t e q.1 q.2 (G.white e) (G.white rs)
    ghostStepPrime hpsi ring t G e =
      { phys := pprimeStep ring G.phys e
        black := pfpGhostSetTwo G.black e rs gb.left gb.right
        white := pfpGhostSetTwo G.white e rs gw.left gw.right
        completed := G.completed ++ gb.done ++ gw.done } := by
  -- A bare `rfl` made the elaborator compare the private L18 ghost operations
  -- with their public mirrors by unfolding both move-token computations
  -- (227 s); rewrite to the mirror first so the comparison is syntactic.
  intro rs p gb q gw
  unfold ghostStepPrime
  rw [pfpSelectedPair_eq, pfpSelectedPair_eq]
  unfold pfpSelectedPair
  dsimp only
  rfl

open Lean Elab Term Meta in
/-- `tokencorr% "name"` elaborates to the private declaration `name` of
`TokenCorrectness.lean`. -/
elab "tokencorr% " s:str : term => do
  let n : Name :=
    (((`_private.Leader.PPL.TokenCorrectness.Ghost).num 0).str "PPL").str s.getString
  mkConstWithFreshMVarLevels n

/-- The public MoveToken mirror is the private ordinary ghost MoveToken
(checked at variables, where unfolding both sides is cheap). -/
private theorem pfpGhostMoveToken_eq_ordinary {n psi kappa : Nat}
    (hpsi : 2 ≤ psi) (kind : TokenKind) (step : Nat) (site : Fin n)
    (l r : State psi kappa) (gl gr : Option (GhostToken n psi)) :
    pfpGhostMoveToken hpsi kind step site l r gl gr =
      (tokencorr% "ghostMoveToken") hpsi kind step site l r gl gr := rfl

private theorem pfpGhostSetTwo_eq_ordinary {n : Nat} {A : Type}
    (f : Fin n → A) (i j : Fin n) (a b : A) :
    pfpGhostSetTwo f i j a b = (tokencorr% "setTwo") f i j a b := rfl

/-- The ordinary ghost step, in terms of the public mirror (the prime ghost
bookkeeping is the ordinary one; only the physical pair differs). -/
theorem ghostStep_unfold {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (t : Nat) (G : GhostConfig n psi kappa) (e : Fin n) :
    let rs := ring.rightNeighbor e
    let p := PPL.Safety.PeacefulProps.preTokenPair hpsi (G.phys e) (G.phys rs)
    let gb := pfpGhostMoveToken hpsi .black t e p.1 p.2 (G.black e) (G.black rs)
    let q := PPL.moveToken hpsi .black p.1 p.2
    let gw := pfpGhostMoveToken hpsi .white t e q.1 q.2 (G.white e) (G.white rs)
    ghostStep hpsi ring t G e =
      { phys := PopulationProtocol.step (PPL.protocol psi kappa) ring G.phys e
        black := pfpGhostSetTwo G.black e rs gb.left gb.right
        white := pfpGhostSetTwo G.white e rs gw.left gw.right
        completed := G.completed ++ gb.done ++ gw.done } := by
  -- A bare `rfl` compared the private ordinary ghost operations with their
  -- differently factored public mirrors on the concrete prelude pair (90 s,
  -- over the default budget); rewrite through the variable-level mirror
  -- equalities so the remaining comparison is syntactic.
  intro rs p gb q gw
  simp only [rs, p, gb, q, gw, pfpGhostMoveToken_eq_ordinary,
    pfpGhostSetTwo_eq_ordinary]
  rfl

/-- Local ghost validity reads the state only through `dist`. -/
theorem pfpGhostLocalValid_congr {psi kappa : Nat} (kind : TokenKind)
    (q q' : State psi kappa) (hd : q.dist = q'.dist) (t : TokenData psi) :
    pfpGhostLocalValid kind q t = pfpGhostLocalValid kind q' t := by
  unfold pfpGhostLocalValid tokenTargetCoordinate
  rw [hd]

theorem pfpGhostLiveValue_congr {psi kappa : Nat} (kind : TokenKind)
    (q q' : State psi kappa) (hd : q.dist = q'.dist)
    (ht : tokenAt kind q = tokenAt kind q') :
    pfpGhostLiveValue kind q = pfpGhostLiveValue kind q' := by
  unfold pfpGhostLiveValue
  rw [ht]
  cases tokenAt kind q' with
  | none => rfl
  | some t => simp only [pfpGhostLocalValid_congr kind q q' hd t]

theorem pfpGhostLiveShadow_congr {n psi kappa : Nat} (kind : TokenKind)
    (q q' : State psi kappa) (hd : q.dist = q'.dist)
    (ht : tokenAt kind q = tokenAt kind q') (g : Option (GhostToken n psi)) :
    pfpGhostLiveShadow kind q g = pfpGhostLiveShadow kind q' g := by
  unfold pfpGhostLiveShadow
  rw [ht]
  cases g with
  | none => rfl
  | some z =>
      cases tokenAt kind q' with
      | none => rfl
      | some t => simp only [pfpGhostLocalValid_congr kind q q' hd t]

theorem pfpGhostBumpTo_congr {n psi kappa : Nat} (kind : TokenKind)
    (q q' : State psi kappa) (hd : q.dist = q'.dist) (v : TokenData psi)
    (g : Option (GhostToken n psi)) :
    pfpGhostBumpTo kind q v g = pfpGhostBumpTo kind q' v g := by
  unfold pfpGhostBumpTo
  cases g with
  | none => rfl
  | some z => simp only [pfpGhostLocalValid_congr kind q q' hd v]

theorem pfpGhostFinishMove_congr_right {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (kind : TokenKind) (l r r' : State psi kappa) (hd : r.dist = r'.dist)
    (lv2 rv0 : Option (TokenData psi)) (gl2 gr0 : Option (GhostToken n psi)) :
    pfpGhostFinishMove hpsi kind l r lv2 rv0 gl2 gr0 =
      pfpGhostFinishMove hpsi kind l r' lv2 rv0 gl2 gr0 := by
  unfold pfpGhostFinishMove
  simp only [pfpGhostBumpTo_congr kind r r' hd]

/-- The ghost MoveToken reads the responder only through `dist`, `last` and
the moved token. -/
theorem pfpGhostMoveToken_congr_right {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (kind : TokenKind) (step : Nat) (site : Fin n) (l r r' : State psi kappa)
    (hd : r.dist = r'.dist) (hl : r.last = r'.last)
    (ht : tokenAt kind r = tokenAt kind r')
    (gl gr : Option (GhostToken n psi)) :
    pfpGhostMoveToken hpsi kind step site l r gl gr =
      pfpGhostMoveToken hpsi kind step site l r' gl gr := by
  unfold pfpGhostMoveToken
  simp only [hl, pfpGhostLiveValue_congr kind r r' hd ht,
    pfpGhostLiveShadow_congr kind r r' hd ht,
    pfpGhostFinishMove_congr_right hpsi kind l r r' hd]

/-- Ghost bridge.  Under `PreludeAgree` on the selected pair, the prime and
the ordinary ghost steps have equal black maps, white maps and completion
logs, and `PhysAgree` physical parts at every site. -/
theorem ghostStepPrime_bridge {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (t : Nat) (G : GhostConfig n psi kappa) (e : Fin n)
    (hpre : PreludeAgree hpsi (G.phys e) (G.phys (ring.rightNeighbor e))) :
    (ghostStepPrime hpsi ring t G e).black = (ghostStep hpsi ring t G e).black ∧
      (ghostStepPrime hpsi ring t G e).white = (ghostStep hpsi ring t G e).white ∧
      (ghostStepPrime hpsi ring t G e).completed =
        (ghostStep hpsi ring t G e).completed ∧
      ∀ i, PhysAgree ((ghostStepPrime hpsi ring t G e).phys i)
        ((ghostStep hpsi ring t G e).phys i) := by
  have hphys := fun i => pprimeStep_physAgree hpsi ring G.phys e hpre i
  have h1 := ghostStepPrime_unfold hpsi ring t G e
  have h2 := ghostStep_unfold hpsi ring t G e
  simp only at h1 h2
  rw [h1, h2]
  dsimp only
  unfold PreludeAgree at hpre
  rw [← hpre]
  generalize PPL.Safety.PeacefulProps.preTokenPair hpsi (G.phys e)
    (G.phys (ring.rightNeighbor e)) = p
  have hB1 := pprimeMoveToken_left_eq hpsi .black p.1 p.2
  have hBf := pprimeMoveToken_right_frame hpsi .black p.1 p.2
  have hAf := moveToken_right_frame hpsi .black p.1 p.2
  have hW : ∀ (gl gr : Option (GhostToken n psi)),
      pfpGhostMoveToken hpsi .white t e (pprimeMoveToken hpsi .black p.1 p.2).1
          (pprimeMoveToken hpsi .black p.1 p.2).2 gl gr =
        pfpGhostMoveToken hpsi .white t e (PPL.moveToken hpsi .black p.1 p.2).1
          (PPL.moveToken hpsi .black p.1 p.2).2 gl gr := by
    intro gl gr
    rw [hB1]
    apply pfpGhostMoveToken_congr_right
    · exact hBf.1.trans hAf.1.symm
    · exact hBf.2.1.trans hAf.2.1.symm
    · simpa [tokenAt] using (hBf.2.2.1 rfl).trans (hAf.2.2.1 rfl).symm
  refine ⟨rfl, ?_, ?_, ?_⟩
  · rw [hW]
  · rw [hW]
  · exact hphys

/-! ## 4. Transfers -/

/-- `ValidToken` reads the site only through the token and `dist`. -/
theorem validToken_congr {n psi kappa : Nat} (kind : TokenKind)
    (C C' : Config n psi kappa) (i : Fin n)
    (ht : tokenAt kind (C i) = tokenAt kind (C' i))
    (hd : (C i).dist = (C' i).dist) :
    ValidToken kind C i ↔ ValidToken kind C' i := by
  unfold ValidToken tokenTargetCoordinate
  rw [ht, hd]

/-- `SiteSound` reads the ghost map, the token and `dist` of the site. -/
theorem siteSound_congr {n psi kappa : Nat} (G G' : GhostConfig n psi kappa)
    (kind : TokenKind) (i : Fin n)
    (hg : ghostTokenAt kind G i = ghostTokenAt kind G' i)
    (ht : tokenAt kind (G.phys i) = tokenAt kind (G'.phys i))
    (hd : (G.phys i).dist = (G'.phys i).dist) :
    SiteSound G kind i ↔ SiteSound G' kind i := by
  unfold SiteSound
  rw [hg, ht, validToken_congr kind G.phys G'.phys i ht hd]

/-- Private ordinary one-step soundness (`CoverageLeaves:2224`). -/
theorem pb_ghostStep_sound {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (t : Nat) (G : GhostConfig n psi kappa) (e : Fin n)
    (hG : GhostSound G) : GhostSound (ghostStep hpsi ring t G e) :=
  (covleaves% "coverageLeavesGhostStep_sound") hpsi ring t G e hG

/-- Transfer: under `PreludeAgree`, one prime ghost step preserves
`GhostSound`, from the ordinary one-step soundness. -/
theorem ghostSound_ghostStepPrime_of_preludeAgree {n psi kappa : Nat}
    (hpsi : 2 ≤ psi) (ring : DirectedRing n) (t : Nat)
    (G : GhostConfig n psi kappa) (e : Fin n) (hG : GhostSound G)
    (hpre : PreludeAgree hpsi (G.phys e) (G.phys (ring.rightNeighbor e))) :
    GhostSound (ghostStepPrime hpsi ring t G e) := by
  have hO := pb_ghostStep_sound hpsi ring t G e hG
  obtain ⟨hb, hw, _, hph⟩ := ghostStepPrime_bridge hpsi ring t G e hpre
  apply ghostSound_of_siteSound
  intro kind i
  have hs := siteSound_of_ghostSound hO kind i
  refine (siteSound_congr _ _ kind i ?_ ?_ ?_).2 hs
  · cases kind
    · show (ghostStepPrime hpsi ring t G e).black i = (ghostStep hpsi ring t G e).black i
      rw [hb]
    · show (ghostStepPrime hpsi ring t G e).white i = (ghostStep hpsi ring t G e).white i
      rw [hw]
  · cases kind
    · exact (hph i).1
    · exact (hph i).2.1
  · exact (hph i).2.2.1

/-- Transfer under `CDLAt` of the pre-state. -/
theorem ghostSound_ghostStepPrime_of_CDLAt {n psi kappa : Nat}
    (hpsi : 2 ≤ psi) (ring : DirectedRing n) (root : Fin n) (t : Nat)
    (G : GhostConfig n psi kappa) (e : Fin n) (hG : GhostSound G)
    (hCDL : CDLAt ring root G.phys) :
    GhostSound (ghostStepPrime hpsi ring t G e) :=
  ghostSound_ghostStepPrime_of_preludeAgree hpsi ring t G e hG
    (preludeAgree_of_CDLAt hpsi ring root G.phys e hCDL)

/-- `PreludeAgree` at every selected pair visited along a prime run. -/
def PreludeAlong {n psi kappa : Nat} (hpsi : 2 ≤ psi) (ring : DirectedRing n) :
    Config n psi kappa → DetSchedule n → Prop
  | _, [] => True
  | C, e :: es =>
      PreludeAgree hpsi (C e) (C (ring.rightNeighbor e)) ∧
        PreludeAlong hpsi ring (pprimeStep ring C e) es

/-- Transfer along a run: a prime ghost run keeps `GhostSound` as long as
every visited selected pair satisfies `PreludeAgree`. -/
theorem ghostSound_ghostRunPrime_of_preludeAlong {n psi kappa : Nat}
    (hpsi : 2 ≤ psi) (ring : DirectedRing n) (t : Nat)
    (G : GhostConfig n psi kappa) (s : DetSchedule n) (hG : GhostSound G)
    (hal : PreludeAlong hpsi ring G.phys s) :
    GhostSound (ghostRunPrime hpsi ring t G s) := by
  induction s generalizing t G with
  | nil => exact hG
  | cons e es ih =>
      exact ih (t + 1) (ghostStepPrime hpsi ring t G e)
        (ghostSound_ghostStepPrime_of_preludeAgree hpsi ring t G e hG hal.1)
        hal.2

end Lemma4Generic
end PPL

#print axioms PPL.Lemma4Generic.pprimeStep_physAgree
#print axioms PPL.Lemma4Generic.ghostStepPrime_bridge
#print axioms PPL.Lemma4Generic.ghostSound_ghostStepPrime_of_CDLAt
#print axioms PPL.Lemma4Generic.ghostSound_ghostRunPrime_of_preludeAlong
