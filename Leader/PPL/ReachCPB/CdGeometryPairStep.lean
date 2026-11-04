import Leader.PPL.ReachCPB.MismatchCapped
import Leader.PPL.TransitionFacts

namespace PPL.Convergence.ReachCPB

set_option autoImplicit false
set_option Elab.async false

/-!
Lemma16CdGeometryPairStepSpec is true as written.  The proof is the literal
one-interaction row:

* DetermineMode preserves leader/dist/last;
* on a leaderless successor-distance edge, Algorithm-2 line 4 computes the
  existing responder distance, so line 6 cannot birth and line 8 is
  idempotent;
* line 9 writes the same false initiator last bit;
* both Algorithm-3 MoveToken calls preserve dist/last by TransitionFacts;
* Algorithm 5 preserves dist/last by Elim.otherView.
-/

private structure CdStatic (psi : Nat) where
  leader : Bool
  dist : Fin (2 * psi)
  last : Bool

private def cdStatic {psi kappa : Nat}
    (q : PPL.State psi kappa) : CdStatic psi where
  leader := q.leader
  dist := q.dist
  last := q.last

/-- Publicly named copy of the private Algorithm-2 line-4 expression. -/
private def cdLine4Tmp {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : PPL.State psi kappa) : Fin (2 * psi) :=
  let d := PPL.determineMode l r
  if d.2.leader = true then
    ⟨0, by omega⟩
  else
    ⟨(d.1.dist.val + 1) % (2 * psi),
      Nat.mod_lt _ (by omega)⟩

/-- Algorithm-2 lines 8--9, parameterized by the state retained after line 6. -/
private def cdAfterLine9 {psi kappa : Nat}
    (s : PPL.CreateLeaderAfterLine6 psi kappa) :
    PPL.State psi kappa × PPL.State psi kappa :=
  let r1 :=
    if s.right.mode = false then
      { s.right with dist := s.tmp }
    else
      s.right
  let l1 :=
    if r1.leader = true then
      { s.left with last := true }
    else if Or (r1.dist.val = 0) (r1.dist.val = psi) then
      { s.left with last := false }
    else
      { s.left with last := r1.last }
  (l1, r1)

/-- Exact CreateLeader prefix through Algorithm-2 line 9. -/
private def cdPreTokenPair {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : PPL.State psi kappa) :
    PPL.State psi kappa × PPL.State psi kappa :=
  cdAfterLine9 (PPL.createLeaderThroughLine6 hpsi l r)

theorem lemma16CdGeometryPairStepSpec_proved :
    Lemma16CdGeometryPairStepSpec := by
  intro psi kappa hpsi l r _hl hr hdist hllast hrlast
  dsimp only
  rw [PPL.transition_eq_ppl hpsi]

  /- DetermineMode changes none of leader/dist/last. -/
  have hdet :
      let d := PPL.determineMode l r
      And
        (cdStatic d.1 = cdStatic l)
        (cdStatic d.2 = cdStatic r) := by
    simp only [PPL.determineMode]
    all_goals try (split <;> try dsimp only)
    all_goals try (split <;> try dsimp only)
    all_goals try (split <;> try dsimp only)
    all_goals try (split <;> try dsimp only)
    all_goals try (split <;> try dsimp only)
    all_goals exact And.intro rfl rfl
  dsimp only at hdet

  have hdetLdist :
      (PPL.determineMode l r).1.dist = l.dist := by
    have h :=
      congrArg (fun z : CdStatic psi => z.dist) hdet.1
    simpa [cdStatic] using h
  have hdetLlast :
      (PPL.determineMode l r).1.last = l.last := by
    have h :=
      congrArg (fun z : CdStatic psi => z.last) hdet.1
    simpa [cdStatic] using h
  have hdetRleader :
      (PPL.determineMode l r).2.leader = r.leader := by
    have h :=
      congrArg (fun z : CdStatic psi => z.leader) hdet.2
    simpa [cdStatic] using h
  have hdetRdist :
      (PPL.determineMode l r).2.dist = r.dist := by
    have h :=
      congrArg (fun z : CdStatic psi => z.dist) hdet.2
    simpa [cdStatic] using h
  have hdetRlast :
      (PPL.determineMode l r).2.last = r.last := by
    have h :=
      congrArg (fun z : CdStatic psi => z.last) hdet.2
    simpa [cdStatic] using h

  /- The local line-4 mirror is definitionally the retained line-4 tmp. -/
  have htmpBridge :
      cdLine4Tmp hpsi l r =
        (PPL.createLeaderThroughLine6 hpsi l r).tmp := by
    dsimp only [cdLine4Tmp, PPL.createLeaderThroughLine6]
    rfl

  /- On the successor-distance row, tmp is exactly the current r.dist. -/
  have htmpRight :
      cdLine4Tmp hpsi l r = r.dist := by
    apply Fin.ext
    simp [cdLine4Tmp, hdetRleader, hr, hdetLdist, hdist]

  /- Hence the Detect inconsistency guard at Algorithm-2 line 6 is false. -/
  have hguard :
      ¬ PPL.createLeaderLine6Guard hpsi l r := by
    intro hfire
    unfold PPL.createLeaderLine6Guard at hfire
    dsimp only at hfire
    apply hfire.2
    change
      (PPL.createLeaderThroughLine6 hpsi l r).tmp =
        (PPL.determineMode l r).2.dist
    calc
      (PPL.createLeaderThroughLine6 hpsi l r).tmp =
          cdLine4Tmp hpsi l r := htmpBridge.symm
      _ = r.dist := htmpRight
      _ = (PPL.determineMode l r).2.dist := hdetRdist.symm

  let s := PPL.createLeaderThroughLine6 hpsi l r

  /- With the line-6 branch excluded, the retained states are DetermineMode's. -/
  have hs :
      And
        (s.left = (PPL.determineMode l r).1)
        (s.right = (PPL.determineMode l r).2) := by
    dsimp only [s, PPL.createLeaderThroughLine6]
    split
    · rename_i hfire
      exact False.elim (hguard hfire)
    · exact And.intro rfl rfl

  have hsTmp : s.tmp = r.dist := by
    change
      (PPL.createLeaderThroughLine6 hpsi l r).tmp = r.dist
    exact (htmpBridge.symm).trans htmpRight

  have hsLdist : s.left.dist = l.dist := by
    rw [hs.1, hdetLdist]
  have hsLlast : s.left.last = l.last := by
    rw [hs.1, hdetLlast]
  have hsRleader : s.right.leader = false := by
    rw [hs.2, hdetRleader, hr]
  have hsRdist : s.right.dist = r.dist := by
    rw [hs.2, hdetRdist]
  have hsRlast : s.right.last = r.last := by
    rw [hs.2, hdetRlast]

  /- Lines 8--9 are idempotent on dist and zero-last geometry. -/
  let p := cdPreTokenPair hpsi l r
  have hp :
      And
        (p.1.dist = l.dist)
        (And
          (p.1.last = l.last)
          (And
            (p.2.dist = r.dist)
            (p.2.last = r.last))) := by
    change
      (let r1 : PPL.State psi kappa :=
        if s.right.mode = false then
          { s.right with dist := s.tmp }
        else
          s.right
       let l1 : PPL.State psi kappa :=
        if r1.leader = true then
          { s.left with last := true }
        else if Or (r1.dist.val = 0) (r1.dist.val = psi) then
          { s.left with last := false }
        else
          { s.left with last := r1.last }
       And
         (l1.dist = l.dist)
         (And
           (l1.last = l.last)
           (And
             (r1.dist = r.dist)
             (r1.last = r.last))))
    by_cases hm : s.right.mode = false
    · by_cases hb :
          Or (r.dist.val = 0) (r.dist.val = psi)
      · simp [hm, hb, hsLdist, hsLlast, hsRleader,
          hsRdist, hsRlast, hsTmp, hllast, hrlast]
      · simp [hm, hb, hsLdist, hsLlast, hsRleader,
          hsRdist, hsRlast, hsTmp, hllast, hrlast]
    · by_cases hb :
          Or (r.dist.val = 0) (r.dist.val = psi)
      · simp [hm, hb, hsLdist, hsLlast, hsRleader,
          hsRdist, hsRlast, hsTmp, hllast, hrlast]
      · simp [hm, hb, hsLdist, hsLlast, hsRleader,
          hsRdist, hsRlast, hsTmp, hllast, hrlast]

  /- TransitionFacts: Algorithm 3 preserves dist/last on both endpoints. -/
  have hmove :
      forall (kind : PPL.TokenKind)
        (a b : PPL.State psi kappa),
        let q := PPL.moveToken hpsi kind a b
        And
          (q.1.dist = a.dist)
          (And
            (q.1.last = a.last)
            (And
              (q.2.dist = b.dist)
              (q.2.last = b.last))) := by
    intro kind a b
    dsimp only
    have hi :=
      PPL.moveToken_initiator_fields hpsi kind a b
    rcases PPL.moveToken_responder_fields hpsi kind a b with
      hres | hres
    · cases kind <;>
        simp_all [PPL.eraseKindToken, PPL.eraseKindTokenId]
    · cases kind <;>
        simp_all [PPL.eraseKindToken, PPL.eraseKindTokenId,
          PPL.birthFields]

  let b := PPL.moveToken hpsi .black p.1 p.2
  let w := PPL.moveToken hpsi .white b.1 b.2

  have hb := hmove PPL.TokenKind.black p.1 p.2
  have hw := hmove PPL.TokenKind.white b.1 b.2
  dsimp only at hb hw

  have hcreate :
      And
        ((PPL.createLeader hpsi l r).1.dist = l.dist)
        (And
          ((PPL.createLeader hpsi l r).1.last = l.last)
          (And
            ((PPL.createLeader hpsi l r).2.dist = r.dist)
            ((PPL.createLeader hpsi l r).2.last = r.last))) := by
    have hdef :
        PPL.createLeader hpsi l r = w := by
      rfl
    rw [hdef]
    exact
      And.intro
        (hw.1.trans (hb.1.trans hp.1))
        (And.intro
          (hw.2.1.trans (hb.2.1.trans hp.2.1))
          (And.intro
            (hw.2.2.1.trans (hb.2.2.1.trans hp.2.2.1))
            (hw.2.2.2.trans (hb.2.2.2.trans hp.2.2.2))))

  /- Algorithm 5 frames dist and last through OtherFields. -/
  have helim :
      forall (a b : PPL.State psi kappa),
        let q := PPL.eliminateLeaders a b
        And
          (q.1.dist = a.dist)
          (And
            (q.1.last = a.last)
            (And
              (q.2.dist = b.dist)
              (q.2.last = b.last))) := by
    intro a b
    dsimp only
    have hleft :=
      PPL.Elim.otherView_eliminateLeaders_left a b
    have hright :=
      PPL.Elim.otherView_eliminateLeaders_right a b
    exact
      And.intro
        (congrArg
          (fun z : PPL.Elim.OtherFields psi kappa => z.dist)
          hleft)
        (And.intro
          (congrArg
            (fun z : PPL.Elim.OtherFields psi kappa => z.last)
            hleft)
          (And.intro
            (congrArg
              (fun z : PPL.Elim.OtherFields psi kappa => z.dist)
              hright)
            (congrArg
              (fun z : PPL.Elim.OtherFields psi kappa => z.last)
              hright)))

  let c := PPL.createLeader hpsi l r
  let q := PPL.eliminateLeaders c.1 c.2

  have hc :
      And
        (c.1.dist = l.dist)
        (And
          (c.1.last = l.last)
          (And
            (c.2.dist = r.dist)
            (c.2.last = r.last))) := by
    simpa only [c] using hcreate

  have he := helim c.1 c.2
  dsimp only at he

  have hq :
      And
        (q.1.dist = c.1.dist)
        (And
          (q.1.last = c.1.last)
          (And
            (q.2.dist = c.2.dist)
            (q.2.last = c.2.last))) := by
    simpa only [q] using he

  have hppl :
      PPL.ppl hpsi l r = q := by
    rfl

  rw [hppl]
  exact
    And.intro
      (hq.1.trans hc.1)
      (And.intro
        (hq.2.1.trans hc.2.1)
        (And.intro
          (hq.2.2.1.trans hc.2.2.1)
          (hq.2.2.2.trans hc.2.2.2)))

/-- The existing configuration-level consumer is now unconditional. -/
theorem lemma16CdGeometryStep_closed :
    Lemma16CdGeometryStepSpec :=
  lemma16CdGeometryStep lemma16CdGeometryPairStepSpec_proved

/-- The existing schedule-induction consumer is now unconditional as well. -/
theorem lemma16CdTraceUntilSuccess_closed :
    Lemma16CdTraceUntilSuccessSpec :=
  lemma16CdTraceUntilSuccess_proved
    lemma16CdGeometryPairStepSpec_proved

end PPL.Convergence.ReachCPB

#print axioms PPL.Convergence.ReachCPB.lemma16CdGeometryPairStepSpec_proved
#print axioms PPL.Convergence.ReachCPB.lemma16CdGeometryStep_closed
#print axioms PPL.Convergence.ReachCPB.lemma16CdTraceUntilSuccess_closed
