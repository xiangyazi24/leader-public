import Leader.PPL.SPLEntry.TrajectoryKey

/-!
# L18: refined provenance of one prime ghost move

Refinements of `q3_left_cases` / `q3_right_cases` needed by the no-overtaking
invariant and the service-write argument:

* `q7_LR`: if both outputs of one selected move are live, the right output is
  the unchanged right pre-owner (at most one output is new);
* `q7_right_cases`: a moved right output additionally records the open
  `last` gate, the empty live responder slot, and (for a moved initiator
  occurrence) the live initiator value;
* `q7_done_cases`: every logged completion is the bump of a pre-owner by one
  Algorithm-3 move, reaching exactly `tokenTrajectoryMoves psi` moves.
-/

namespace PPL.Convergence.L18

set_option autoImplicit false
set_option Elab.async false

open PPL

theorem q7_finish_LR {n psi kappa : Nat} (hpsi : 2 ≤ psi) (kind : TokenKind)
    (l r : State psi kappa) (lv2 rv0 : Option (TokenData psi))
    (gl2 gr0 : Option (GhostToken n psi)) (zl zr : GhostToken n psi)
    (hl : (q3GFinishMove hpsi kind l r lv2 rv0 gl2 gr0).left = some zl)
    (hr : (q3GFinishMove hpsi kind l r lv2 rv0 gl2 gr0).right = some zr) :
    gr0 = some zr := by
  unfold q3GFinishMove at hl hr
  rcases lv2 with _ | t
  · dsimp only at hl hr
    rcases rv0 with _ | t'
    · exact hr
    · dsimp only at hl hr
      split at hr
      · simp at hr
      · split at hr
        · simp at hr
        · exact hr
  · dsimp only at hl hr
    split at hr
    · rename_i h1
      rw [dif_pos h1] at hl
      simp at hl
    · rename_i h1
      split at hr
      · rename_i h2
        rw [dif_neg h1, dif_pos h2] at hl
        simp at hl
      · rcases rv0 with _ | t'
        · exact hr
        · dsimp only at hr
          split at hr
          · simp at hr
          · split at hr
            · simp at hr
            · exact hr

/-- At most one output of a selected move is new: if both are live, the
right one is the unchanged right pre-owner. -/
theorem q7_LR {n psi kappa : Nat} (hpsi : 2 ≤ psi) (kind : TokenKind)
    (step : Nat) (site : Fin n) (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) (zl zr : GhostToken n psi)
    (hl : (q3GMoveToken hpsi kind step site l r gl gr).left = some zl)
    (hr : (q3GMoveToken hpsi kind step site l r gl gr).right = some zr) :
    gr = some zr := by
  unfold q3GMoveToken at hl hr
  dsimp only at hl hr
  split at hr
  · rename_i hlast
    rw [dif_pos hlast] at hl
    exact (q3_shadow kind r gr zr (q7_finish_LR hpsi kind _ _ _ _ _ _ zl zr hl hr)).1
  · exact (q3_shadow kind r gr zr hr).1

/-- Refined provenance of the right output. -/
theorem q7_right_cases {n psi kappa : Nat} (hpsi : 2 ≤ psi) (kind : TokenKind)
    (step : Nat) (site : Fin n) (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) (z : GhostToken n psi)
    (h : (q3GMoveToken hpsi kind step site l r gl gr).right = some z) :
    gr = some z ∨
      ∃ z0 v,
        ((gl = some z0 ∧ q3GLiveValue kind l = some z0.value) ∨
          (z0 = q3GBirth hpsi kind step site l.id ∧
            l.dist.val = tokenD' psi kind ∧ q3GLiveValue kind l = none)) ∧
        q3MoveR hpsi z0.value v ∧ z = q3Bump z0 v ∧ q3GLocalValid kind r v ∧
        (l.last = false ∧ r.last = false) ∧ q3GLiveValue kind r = none := by
  unfold q3GMoveToken at h
  dsimp only at h
  split at h
  · rename_i hlast
    rcases q3_finish_right hpsi kind _ _ _ _ _ _ z h with hgr | ⟨t, v, hlv, hmv, hb⟩
    · exact Or.inl (q3_shadow kind r gr z hgr).1
    · obtain ⟨z0, hg2, hz, hLV⟩ := q3_bump_live kind r v _ z hb
      right
      by_cases hbc : (l.dist.val = tokenD' psi kind ∧ q3GLiveValue kind l = none)
      · simp only [if_pos hbc] at hg2 hlv
        by_cases hcol : ((some (q3GBirth hpsi kind step site l.id).value : Option (TokenData psi)) ≠ none ∧
            q3GLiveValue kind r ≠ none)
        · rw [if_pos hcol] at hg2
          cases hg2
        · rw [if_neg hcol] at hg2 hlv
          have e1 := Option.some.inj hg2
          have e2 := Option.some.inj hlv
          subst e1
          have hrn : q3GLiveValue kind r = none := by
            cases hq : q3GLiveValue kind r with
            | none => rfl
            | some _ => exact absurd ⟨by simp, by rw [hq]; simp⟩ hcol
          refine ⟨_, v, Or.inr ⟨rfl, hbc.1, hbc.2⟩, ?_, hz, hLV, hlast, hrn⟩
          rw [e2]; exact hmv
      · simp only [if_neg hbc] at hg2 hlv
        by_cases hcol : (q3GLiveValue kind l ≠ none ∧ q3GLiveValue kind r ≠ none)
        · rw [if_pos hcol] at hg2
          cases hg2
        · rw [if_neg hcol] at hg2 hlv
          have hsh := q3_shadow kind l gl z0 hg2
          have hlv' := q3_liveValue kind l t hlv
          have ht : z0.value = t := by
            rw [hsh.2] at hlv'; exact Option.some.inj hlv'
          have hrn : q3GLiveValue kind r = none := by
            cases hq : q3GLiveValue kind r with
            | none => rfl
            | some _ => exact absurd ⟨by rw [hlv]; simp, by rw [hq]; simp⟩ hcol
          refine ⟨z0, v, Or.inl ⟨hsh.1, by rw [ht]; exact hlv⟩, ?_, hz, hLV, hlast, hrn⟩
          rw [ht]; exact hmv
  · exact Or.inl (q3_shadow kind r gr z h).1

theorem q7_bump_done {n psi kappa : Nat} (kind : TokenKind) (q : State psi kappa)
    (v : TokenData psi) (g : Option (GhostToken n psi)) (m : LineageMeta n)
    (h : m ∈ (q3GBumpTo kind q v g).done) :
    ∃ z0, g = some z0 ∧ m = { z0.lmeta with moves := z0.lmeta.moves + 1 } ∧
      z0.lmeta.moves + 1 = tokenTrajectoryMoves psi := by
  unfold q3GBumpTo at h
  rcases g with _ | z0
  · simp at h
  · dsimp only at h
    split at h
    · rename_i hT
      simp only [List.mem_singleton] at h
      exact ⟨z0, rfl, h, hT⟩
    · simp at h

theorem q7_finish_done {n psi kappa : Nat} (hpsi : 2 ≤ psi) (kind : TokenKind)
    (l r : State psi kappa) (lv2 rv0 : Option (TokenData psi))
    (gl2 gr0 : Option (GhostToken n psi)) (m : LineageMeta n)
    (h : m ∈ (q3GFinishMove hpsi kind l r lv2 rv0 gl2 gr0).done) :
    (∃ t v, lv2 = some t ∧ q3MoveR hpsi t v ∧ m ∈ (q3GBumpTo kind r v gl2).done) ∨
      (∃ t v, rv0 = some t ∧ q3MoveL hpsi l t v ∧ m ∈ (q3GBumpTo kind l v gr0).done) := by
  unfold q3GFinishMove at h
  rcases lv2 with _ | t
  · dsimp only at h
    rcases rv0 with _ | t'
    · simp at h
    · dsimp only at h
      split at h
      · rename_i hm1
        exact Or.inr ⟨t', _, rfl, Or.inl ⟨hm1, rfl⟩, h⟩
      · split at h
        · rename_i hm1 hm2
          dsimp only at h
          refine Or.inr ⟨t', _, rfl, ?_, h⟩
          refine Or.inr ⟨hm2, ?_, rfl, rfl⟩
          simp only [tokenCode, q3GMkToken]
          rw [decode_encode]
        · simp at h
  · dsimp only at h
    split at h
    · rename_i h1
      exact Or.inl ⟨t, _, rfl, Or.inl ⟨h1, rfl⟩, h⟩
    · split at h
      · rename_i h1 h2
        dsimp only at h
        refine Or.inl ⟨t, _, rfl, ?_, h⟩
        refine Or.inr ⟨h2, ?_, rfl, rfl⟩
        simp only [tokenCode, q3GMkToken]
        rw [decode_encode]
      · rcases rv0 with _ | t'
        · simp at h
        · dsimp only at h
          split at h
          · rename_i hm1
            exact Or.inr ⟨t', _, rfl, Or.inl ⟨hm1, rfl⟩, h⟩
          · split at h
            · rename_i hm1 hm2
              dsimp only at h
              refine Or.inr ⟨t', _, rfl, ?_, h⟩
              refine Or.inr ⟨hm2, ?_, rfl, rfl⟩
              simp only [tokenCode, q3GMkToken]
              rw [decode_encode]
            · simp at h

/-- Provenance of a logged completion. -/
theorem q7_done_cases {n psi kappa : Nat} (hpsi : 2 ≤ psi) (kind : TokenKind)
    (step : Nat) (site : Fin n) (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) (m : LineageMeta n)
    (h : m ∈ (q3GMoveToken hpsi kind step site l r gl gr).done) :
    ∃ z0 v,
      ((((gl = some z0 ∧ q3GLiveValue kind l = some z0.value) ∨
          (z0 = q3GBirth hpsi kind step site l.id ∧
            l.dist.val = tokenD' psi kind ∧ q3GLiveValue kind l = none)) ∧
        q3MoveR hpsi z0.value v ∧ (l.last = false ∧ r.last = false) ∧
        q3GLiveValue kind r = none) ∨
      (gr = some z0 ∧ q3MoveL hpsi l z0.value v)) ∧
      m = { z0.lmeta with moves := z0.lmeta.moves + 1 } ∧
      z0.lmeta.moves + 1 = tokenTrajectoryMoves psi := by
  unfold q3GMoveToken at h
  dsimp only at h
  split at h
  · rename_i hlast
    rcases q7_finish_done hpsi kind _ _ _ _ _ _ m h with
      ⟨t, v, hlv, hmv, hb⟩ | ⟨t, v, hrv, hmv, hb⟩
    · obtain ⟨z0, hg2, hm, hT⟩ := q7_bump_done kind r v _ m hb
      refine ⟨z0, v, ?_⟩
      by_cases hbc : (l.dist.val = tokenD' psi kind ∧ q3GLiveValue kind l = none)
      · simp only [if_pos hbc] at hg2 hlv
        by_cases hcol : ((some (q3GBirth hpsi kind step site l.id).value : Option (TokenData psi)) ≠ none ∧
            q3GLiveValue kind r ≠ none)
        · rw [if_pos hcol] at hg2
          cases hg2
        · rw [if_neg hcol] at hg2 hlv
          have e1 := Option.some.inj hg2
          have e2 := Option.some.inj hlv
          subst e1
          have hrn : q3GLiveValue kind r = none := by
            cases hq : q3GLiveValue kind r with
            | none => rfl
            | some _ => exact absurd ⟨by simp, by rw [hq]; simp⟩ hcol
          refine ⟨Or.inl ⟨Or.inr ⟨rfl, hbc.1, hbc.2⟩, ?_, hlast, hrn⟩, hm, hT⟩
          rw [e2]; exact hmv
      · simp only [if_neg hbc] at hg2 hlv
        by_cases hcol : (q3GLiveValue kind l ≠ none ∧ q3GLiveValue kind r ≠ none)
        · rw [if_pos hcol] at hg2
          cases hg2
        · rw [if_neg hcol] at hg2 hlv
          have hsh := q3_shadow kind l gl z0 hg2
          have hlv' := q3_liveValue kind l t hlv
          have ht : z0.value = t := by
            rw [hsh.2] at hlv'; exact Option.some.inj hlv'
          have hrn : q3GLiveValue kind r = none := by
            cases hq : q3GLiveValue kind r with
            | none => rfl
            | some _ => exact absurd ⟨by rw [hlv]; simp, by rw [hq]; simp⟩ hcol
          refine ⟨Or.inl ⟨Or.inl ⟨hsh.1, by rw [ht]; exact hlv⟩, ?_, hlast, hrn⟩, hm, hT⟩
          rw [ht]; exact hmv
    · obtain ⟨z0, hg0, hm, hT⟩ := q7_bump_done kind l v _ m hb
      have hsh := q3_shadow kind r gr z0 hg0
      have hrv' := q3_liveValue kind r t hrv
      have ht : z0.value = t := by
        rw [hsh.2] at hrv'; exact Option.some.inj hrv'
      refine ⟨z0, v, Or.inr ⟨hsh.1, ?_⟩, hm, hT⟩
      rw [ht]; exact hmv
  · simp at h

/-- The completion log of one prime ghost step. -/
theorem q7_completed_step {n psi kappa : Nat} (hpsi : 2 ≤ psi) (ring : DirectedRing n)
    (step : Nat) (G : GhostConfig n psi kappa) (e : Fin n) :
    (ghostStepPrime hpsi ring step G e).completed =
      G.completed ++ (ghostStepSelectedPair_prime hpsi ring step G e .black).done ++
        (ghostStepSelectedPair_prime hpsi ring step G e .white).done := rfl

end PPL.Convergence.L18

#print axioms PPL.Convergence.L18.q7_LR
#print axioms PPL.Convergence.L18.q7_right_cases
#print axioms PPL.Convergence.L18.q7_done_cases
