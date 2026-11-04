import Leader.PPL.Modes.SignalLineageProof
import Leader.PPL.TransitionFacts

namespace PPL.Modes.SignalLineage

set_option autoImplicit false
set_option Elab.async false

/-! The local physical pair facts used by signal ownership. -/

/-- Algorithm 2 through line 9, immediately before its two token passes. -/
private def preTokenPair {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa) :
    PPL.State psi kappa × PPL.State psi kappa :=
  let s := PPL.createLeaderThroughLine6 hpsi l r
  let l0 := s.left
  let r0 := s.right
  let tmp := s.tmp
  let r1 := if r0.mode = false then { r0 with dist := tmp } else r0
  let l1 :=
    if r1.leader = true then { l0 with last := true }
    else if r1.dist.val = 0 ∨ r1.dist.val = psi then
      { l0 with last := false }
    else { l0 with last := r1.last }
  (l1, r1)

private theorem line6_signal_hits {psi kappa : Nat}
    (hpsi : 2 ≤ psi) (l r : PPL.State psi kappa) :
    let d := PPL.determineMode l r
    let s := PPL.createLeaderThroughLine6 hpsi l r
    s.left.signalR = d.1.signalR ∧ s.left.hits = d.1.hits ∧
      s.right.signalR = d.2.signalR ∧ s.right.hits = d.2.hits := by
  dsimp only [PPL.createLeaderThroughLine6]
  split
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩

private theorem preTokenPair_signal_hits {psi kappa : Nat}
    (hpsi : 2 ≤ psi) (l r : PPL.State psi kappa) :
    let d := PPL.determineMode l r
    let q := preTokenPair hpsi l r
    q.1.signalR = d.1.signalR ∧ q.1.hits = d.1.hits ∧
      q.2.signalR = d.2.signalR ∧ q.2.hits = d.2.hits := by
  let s := PPL.createLeaderThroughLine6 hpsi l r
  have hs := line6_signal_hits hpsi l r
  have hp :
      let q := preTokenPair hpsi l r
      q.1.signalR = s.left.signalR ∧ q.1.hits = s.left.hits ∧
        q.2.signalR = s.right.signalR ∧ q.2.hits = s.right.hits := by
    dsimp only [preTokenPair]
    all_goals try (split <;> try dsimp only)
    all_goals try (split <;> try dsimp only)
    all_goals try (split <;> try dsimp only)
    all_goals exact ⟨rfl, rfl, rfl, rfl⟩
  dsimp only at hs hp ⊢
  exact ⟨hp.1.trans hs.1, hp.2.1.trans hs.2.1,
    hp.2.2.1.trans hs.2.2.1, hp.2.2.2.trans hs.2.2.2⟩

private theorem createLeader_signal_hits {psi kappa : Nat}
    (hpsi : 2 ≤ psi) (l r : PPL.State psi kappa) :
    let d := PPL.determineMode l r
    let q := PPL.createLeader hpsi l r
    q.1.signalR = d.1.signalR ∧ q.1.hits = d.1.hits ∧
      q.2.signalR = d.2.signalR ∧ q.2.hits = d.2.hits := by
  let p := preTokenPair hpsi l r
  let b := PPL.moveToken hpsi .black p.1 p.2
  let w := PPL.moveToken hpsi .white b.1 b.2
  have hdef : PPL.createLeader hpsi l r = w := by rfl
  have hp := preTokenPair_signal_hits hpsi l r
  have hb := PPL.moveToken_signal_hits hpsi PPL.TokenKind.black p.1 p.2
  have hw := PPL.moveToken_signal_hits hpsi PPL.TokenKind.white b.1 b.2
  dsimp only at hp hb hw
  rw [hdef]
  exact ⟨hw.1.trans (hb.1.trans hp.1),
    hw.2.1.trans (hb.2.1.trans hp.2.1),
    hw.2.2.1.trans (hb.2.2.1.trans hp.2.2.1),
    hw.2.2.2.trans (hb.2.2.2.trans hp.2.2.2)⟩

private theorem eliminateLeaders_signal_hits {psi kappa : Nat}
    (l r : PPL.State psi kappa) :
    let q := PPL.eliminateLeaders l r
    q.1.signalR = l.signalR ∧ q.1.hits = l.hits ∧
      q.2.signalR = r.signalR ∧ q.2.hits = r.hits := by
  dsimp only
  have hl := PPL.Elim.otherView_eliminateLeaders_left l r
  have hr := PPL.Elim.otherView_eliminateLeaders_right l r
  exact ⟨congrArg (fun z : PPL.Elim.OtherFields psi kappa => z.signalR) hl,
    congrArg (fun z : PPL.Elim.OtherFields psi kappa => z.hits) hl,
    congrArg (fun z : PPL.Elim.OtherFields psi kappa => z.signalR) hr,
    congrArg (fun z : PPL.Elim.OtherFields psi kappa => z.hits) hr⟩

/-- The suffix of the literal pair interaction preserves both signal and hit
fields after DetermineMode has written them. -/
theorem postDetermineModeSignalStable : PostDetermineModeSignalStable := by
  intro psi kappa hpsi l r
  let c := PPL.createLeader hpsi l r
  let q := PPL.eliminateLeaders c.1 c.2
  have hc := createLeader_signal_hits hpsi l r
  have he := eliminateLeaders_signal_hits c.1 c.2
  have hdef : PPL.ppl hpsi l r = q := by rfl
  dsimp only at hc he
  dsimp only
  rw [hdef]
  exact ⟨he.1.trans hc.1,
    he.2.1.trans hc.2.1,
    he.2.2.1.trans hc.2.2.1,
    he.2.2.2.trans hc.2.2.2⟩

/-- DetermineMode's initiator reset and responder trichotomy, at the literal
Algorithm 4 pair boundary. -/
private theorem left_signalR_zero {psi kappa : Nat}
    (l r : PPL.State psi kappa) :
    (PPL.determineMode l r).1.signalR.val = 0 := by
  simp only [PPL.determineMode]
  repeat (first | rfl | split <;> try dsimp only)
  all_goals simp_all
  all_goals try (change (0 : Fin (kappa + 1)) = 0; rfl)
  all_goals repeat (first | rfl | split <;> simp_all)
  all_goals try (change (0 : Fin (kappa + 1)) = 0; rfl)
  all_goals
    by_cases hs : 0 < l.signalR.val ∨ 0 < r.signalR.val
    · simp [hs]
      split <;> change (0 : Fin (kappa + 1)) = 0 <;> rfl
    · have hzl : l.signalR.val = 0 := by omega
      have hzr : r.signalR.val = 0 := by omega
      have hz : l.signalR = 0 := Fin.ext (by simpa using hzl)
      have hrz : r.signalR = 0 := Fin.ext (by simpa using hzr)
      simp [hz, hrz]
      change (0 : Fin (kappa + 1)) = 0
      rfl

private theorem left_hits_zero {psi kappa : Nat}
    (l r : PPL.State psi kappa) :
    (PPL.determineMode l r).1.hits.val = 0 := by
  simp only [PPL.determineMode]
  repeat (first | rfl | split <;> try dsimp only)
  all_goals simp_all
  all_goals change (0 : Fin (psi + 1)) = 0 <;> rfl

elab "unfoldSignalPrivate" : tactic => do
  let names := ["finishModes", "zeroFin", "cappedSucc", "topFin", "predFinOfPos"]
  for stem in names do
    let nm := Lean.mkIdent
      ((((`_private.Leader.PPL.Transition).num 0).str "PPL").str stem)
    let tac ← `(tactic| try (unfold $nm:ident at *))
    Lean.Elab.Tactic.evalTactic tac

theorem determineModeSignalProjection :
    DetermineModeSignalProjectionObligation := by
  intro psi kappa hpsi l r
  have hlr := left_signalR_zero l r
  have hlh := left_hits_zero l r
  refine ⟨hlr, hlh, ?_⟩
  unfold DetermineModeResponderCases armedSignalVal bumpedHitsVal
  simp only [PPL.determineMode]
  repeat (first | rfl | split <;> try dsimp only)
  all_goals simp_all
  all_goals unfoldSignalPrivate
  all_goals dsimp only at *
  all_goals repeat (first | rfl | split <;> try dsimp only)
  all_goals simp_all [apply_ite]
  all_goals try (change ¬ r.signalR.val ≤ kappa at *; omega)
  all_goals omega

/-- A positive DetermineMode responder signal is backed by the owner of the
winning input signal, or by a fresh arm from a leader. -/
private theorem winnerOwner_ne_none_of_det_pos
    {n psi kappa : Nat} (g : GhostConfig n psi kappa)
    (e j : Fin n) (hwf : LineageWellFormed g)
    (hcases : DetermineModeResponderCases (g.physical e) (g.physical j))
    (hp : 0 < (PPL.determineMode (g.physical e) (g.physical j)).2.signalR.val) :
    winnerOwner g e j ≠ none := by
  rcases hcases with hz | hl | hr
  · omega
  · have hcmp : (g.physical j).signalR.val ≤ armedTTL g e := by
      simpa [armedTTL, armedSignalVal] using hl.2.1
    rw [winnerOwner, if_pos hcmp]
    by_cases hlead : (g.physical e).leader = true
    · simp [armedOwner, hlead]
    · have hpos : 0 < (g.physical e).signalR.val := by
        simpa [armedSignalVal, hlead] using hl.1
      have howner : g.owner e ≠ none := by
        intro he
        have hz := (hwf.1 e).1 he
        omega
      simpa [armedOwner, hlead] using howner
  · have hcmp : ¬ (g.physical j).signalR.val ≤ armedTTL g e := by
      have hlt : armedTTL g e < (g.physical j).signalR.val := by
        simpa [armedTTL, armedSignalVal] using hr.1
      omega
    rw [winnerOwner, if_neg hcmp]
    have hpos : 0 < (g.physical j).signalR.val := by
      have hlt : armedTTL g e < (g.physical j).signalR.val := by
        simpa [armedTTL, armedSignalVal] using hr.1
      omega
    intro he
    have hz := (hwf.1 j).1 he
    omega

/-- Ghost ownership continues to match exactly the physical positive
right-signal sites after one literal interaction. -/
theorem ownerMatchesPreserved {n psi kappa : Nat}
    (ring : DirectedRing n) :
    OwnerMatchesPreserved (psi := psi) (kappa := kappa) ring := by
  intro g e hpsi hself hwf
  intro k
  let j := ring.rightNeighbor e
  have hd := determineModeSignalProjection hpsi (g.physical e) (g.physical j)
  have hs := step_signal_projection_of_stable
    postDetermineModeSignalStable hpsi ring g.physical e hself
  dsimp only at hd hs
  change (ghostStep ring g e).owner k = none ↔
    (step ring g.physical e k).signalR.val = 0
  by_cases hke : k = e
  · subst k
    have hz : (step ring g.physical e e).signalR.val = 0 := by
      rw [hs.1]
      exact hd.1
    simp [ghostStep_initiator_owner_none, hz]
  by_cases hkj : k = j
  · subst k
    rw [ghostStep_responder_owner ring g e hself]
    constructor
    · intro hown
      by_cases hp : 0 < (step ring g.physical e j).signalR.val
      · have hdetpos :
            0 < (PPL.determineMode (g.physical e) (g.physical j)).2.signalR.val := by
          rw [← hs.2.2.1]
          exact hp
        have hn := winnerOwner_ne_none_of_det_pos g e j hwf hd.2.2 hdetpos
        change 0 < (step ring g.physical e (ring.rightNeighbor e)).signalR.val at hp
        simp [hp] at hown
        exact (hn hown).elim
      · omega
    · intro hz
      have hp : ¬ 0 < (step ring g.physical e j).signalR.val := by omega
      change ¬ 0 < (step ring g.physical e (ring.rightNeighbor e)).signalR.val at hp
      simp [hp]
  · have haway := step_signal_hits_away ring g.physical e k hke hkj
    have hown := ghostStep_owner_other ring g e k hke hkj
    rw [hown, haway.1]
    exact hwf.1 k

end PPL.Modes.SignalLineage

#print axioms PPL.Modes.SignalLineage.postDetermineModeSignalStable
#print axioms PPL.Modes.SignalLineage.determineModeSignalProjection
#print axioms PPL.Modes.SignalLineage.ownerMatchesPreserved
