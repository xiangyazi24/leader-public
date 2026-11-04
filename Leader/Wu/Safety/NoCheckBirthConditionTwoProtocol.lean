import Leader.Wu.Safety.NoCheckBirthConditionTwoPhysical

/-!
# Exact finite preservation of corrected condition 2

This module completes the finite physical lift of Wu's peaceful-bullet
condition for the separately named no-CHECK-birth protocol.  The proof first
quotients local states by the five fields that Algorithm 15 can observe, then
shows that every normal physical interaction has the same quotient as the
isolated no-collision Algorithm-15 kernel.  Deletion-priority branches are
identity on that quotient.  Exact bounded erasure and timer expiration preserve
the quotient, so the global ring theorem for the isolated kernel transfers to
the packaged finite protocol.

The theorem requires `1 < n`.  The omitted one-agent case is genuinely false
for this condition and is treated separately as a regression, not hidden in the
physical refinement.
-/

namespace PPLLNoCheckBirthConditionTwoProtocol

open PPLL PPLLRepair PPLLNoCheckBirthConditionTwoPhysical

/-! ## A five-field quotient for Algorithm 15 -/

/-- A canonical audit state containing exactly a `PeaceView`.  Every field not
read by Algorithm 15 is reset.  This representative turns observational
congruence into ordinary equality between canonical states. -/
def PeaceView.toState (v : PeaceView ψ) : AgentState ψ where
  leader := v.leader
  probe := false
  phase := false
  bit := false
  wait := false
  state := .none
  path := .bot
  reset := false
  carry := false
  count := 0
  label := v.label
  h_field := false
  path2 := none
  path3 := none
  path4 := none
  path5 := none
  p := false
  p_carry := false
  reset_cmd := false
  echo := false
  signal_B := v.signal_B
  bullet := v.bullet
  shield := v.shield
  write_state := .none
  write := .none
  last := false
  last_set := false
  last_unset := false
  b_carry := false
  gen_ws := false
  ws_echo := false
  signal_ws := false

/-- Canonicalize an audit state modulo leader, label, shield, bullet, and
`signal_B`; all other fields are intentionally forgotten. -/
private def canon (u : AgentState ψ) : AgentState ψ :=
  PeaceView.toState (PeaceView.ofState u)

/-- Algorithm 15's firing stage has the same five-field output on a state and
on its canonical representative. -/
private theorem fire_canon (hψ:ψ>0)(l r:AgentState ψ) :
 peaceViewPair (eliminateLeadersNoCollisionFire hψ (canon l) (canon r))=
 peaceViewPair (eliminateLeadersNoCollisionFire hψ l r) := by
  by_cases hl : l.leader = true ∧ l.signal_B = ⟨1, by omega⟩
  · have hlc : (canon l).leader = true ∧
        (canon l).signal_B = ⟨1, by omega⟩ := hl
    by_cases hr : r.leader = true ∧ r.signal_B = ⟨1, by omega⟩
    · have hrc : (canon r).leader = true ∧
          (canon r).signal_B = ⟨1, by omega⟩ := hr
      unfold eliminateLeadersNoCollisionFire
      rw [if_pos hlc, if_pos hrc, if_pos hl, if_pos hr]
      rfl
    · have hrc : ¬((canon r).leader = true ∧
          (canon r).signal_B = ⟨1, by omega⟩) := hr
      unfold eliminateLeadersNoCollisionFire
      rw [if_pos hlc, if_neg hrc, if_pos hl, if_neg hr]
      rfl
  · have hlc : ¬((canon l).leader = true ∧
        (canon l).signal_B = ⟨1, by omega⟩) := hl
    by_cases hr : r.leader = true ∧ r.signal_B = ⟨1, by omega⟩
    · have hrc : (canon r).leader = true ∧
          (canon r).signal_B = ⟨1, by omega⟩ := hr
      unfold eliminateLeadersNoCollisionFire
      rw [if_neg hlc, if_pos hrc, if_neg hl, if_pos hr]
      rfl
    · have hrc : ¬((canon r).leader = true ∧
          (canon r).signal_B = ⟨1, by omega⟩) := hr
      unfold eliminateLeadersNoCollisionFire
      rw [if_neg hlc, if_neg hrc, if_neg hl, if_neg hr]
      rfl

/-- Bullet collision and movement depend only on the quotient fields. -/
private theorem move_canon (next:Fin ψ)(l r:AgentState ψ) :
 peaceViewPair (eliminateLeadersNoCollisionMove next (canon l) (canon r))=
 peaceViewPair (eliminateLeadersNoCollisionMove next l r) := by
  by_cases h1 : r.bullet.val > 0 ∧ l.leader = true
  · by_cases hkill : r.bullet = ⟨2, by omega⟩ ∧ l.shield = false
    · simp [eliminateLeadersNoCollisionMove, canon, PeaceView.toState,
        PeaceView.ofState, peaceViewPair, h1, hkill]
    · simp [eliminateLeadersNoCollisionMove, canon, PeaceView.toState,
        PeaceView.ofState, peaceViewPair, h1]
  · by_cases h2 : r.bullet.val > 0 ∧ l.leader = false
    · by_cases hlabel : r.label = next
      · simp [eliminateLeadersNoCollisionMove, canon, PeaceView.toState,
          PeaceView.ofState, peaceViewPair, h2, hlabel]
      · simp [eliminateLeadersNoCollisionMove, canon, PeaceView.toState,
          PeaceView.ofState, peaceViewPair, h2, hlabel]
    · simp [eliminateLeadersNoCollisionMove, canon, PeaceView.toState,
        PeaceView.ofState, peaceViewPair, h1, h2]

/-- The absence-signal stage depends only on the quotient fields. -/
private theorem signal_canon (next:Fin ψ)(l r:AgentState ψ) :
 peaceViewPair (eliminateLeadersNoCollisionSignal next (canon l) (canon r))=
 peaceViewPair (eliminateLeadersNoCollisionSignal next l r) := by
  by_cases hcond : r.label = next ∨ l.leader = true
  · by_cases hb : r.bullet = ⟨2, by omega⟩
    · simp [eliminateLeadersNoCollisionSignal, canon, PeaceView.toState,
        PeaceView.ofState, peaceViewPair, hcond, hb]
    · by_cases hl : l.leader = true
      · simp [eliminateLeadersNoCollisionSignal, canon, PeaceView.toState,
          PeaceView.ofState, peaceViewPair, hl]
      · simp [eliminateLeadersNoCollisionSignal, canon, PeaceView.toState,
          PeaceView.ofState, peaceViewPair, hl]
  · simp [eliminateLeadersNoCollisionSignal, canon, PeaceView.toState,
      PeaceView.ofState, peaceViewPair, hcond]

private theorem fire_congr (hψ:ψ>0)(l r l' r':AgentState ψ)
 (hl:PeaceView.ofState l=PeaceView.ofState l')
 (hr:PeaceView.ofState r=PeaceView.ofState r') :
 peaceViewPair (eliminateLeadersNoCollisionFire hψ l r)=
 peaceViewPair (eliminateLeadersNoCollisionFire hψ l' r') := by
  have hcl : canon l = canon l' := congrArg PeaceView.toState hl
  have hcr : canon r = canon r' := congrArg PeaceView.toState hr
  have hc : peaceViewPair
      (eliminateLeadersNoCollisionFire hψ (canon l) (canon r)) =
      peaceViewPair
        (eliminateLeadersNoCollisionFire hψ (canon l') (canon r')) := by
    rw [hcl, hcr]
  exact (fire_canon hψ l r).symm.trans
    (hc.trans (fire_canon hψ l' r'))

private theorem move_congr (next next':Fin ψ)(l r l' r':AgentState ψ)
 (hn:next=next')
 (hl:PeaceView.ofState l=PeaceView.ofState l')
 (hr:PeaceView.ofState r=PeaceView.ofState r') :
 peaceViewPair (eliminateLeadersNoCollisionMove next l r)=
 peaceViewPair (eliminateLeadersNoCollisionMove next' l' r') := by
  have hcl : canon l = canon l' := congrArg PeaceView.toState hl
  have hcr : canon r = canon r' := congrArg PeaceView.toState hr
  have hc : peaceViewPair
      (eliminateLeadersNoCollisionMove next (canon l) (canon r)) =
      peaceViewPair
        (eliminateLeadersNoCollisionMove next' (canon l') (canon r')) := by
    rw [hn, hcl, hcr]
  exact (move_canon next l r).symm.trans
    (hc.trans (move_canon next' l' r'))

private theorem signal_congr (next next':Fin ψ)(l r l' r':AgentState ψ)
 (hn:next=next')
 (hl:PeaceView.ofState l=PeaceView.ofState l')
 (hr:PeaceView.ofState r=PeaceView.ofState r') :
 peaceViewPair (eliminateLeadersNoCollisionSignal next l r)=
 peaceViewPair (eliminateLeadersNoCollisionSignal next' l' r') := by
  have hcl : canon l = canon l' := congrArg PeaceView.toState hl
  have hcr : canon r = canon r' := congrArg PeaceView.toState hr
  have hc : peaceViewPair
      (eliminateLeadersNoCollisionSignal next (canon l) (canon r)) =
      peaceViewPair
        (eliminateLeadersNoCollisionSignal next' (canon l') (canon r')) := by
    rw [hn, hcl, hcr]
  exact (signal_canon next l r).symm.trans
    (hc.trans (signal_canon next' l' r'))

/-- The complete repaired Algorithm 15 descends to `PeaceView`: pairs with
identical views produce identical output views. -/
theorem noCollision_congr (hψ:ψ>0)(l r l' r':AgentState ψ)
 (hl:PeaceView.ofState l=PeaceView.ofState l')
 (hr:PeaceView.ofState r=PeaceView.ofState r') :
 peaceViewPair (eliminateLeadersNoCollision hψ l r)=
 peaceViewPair (eliminateLeadersNoCollision hψ l' r') := by
  let next : Fin ψ := ⟨(l.label.val+1)%ψ, Nat.mod_lt _ hψ⟩
  let next' : Fin ψ := ⟨(l'.label.val+1)%ψ, Nat.mod_lt _ hψ⟩
  let q0 := eliminateLeadersNoCollisionFire hψ l r
  let q0' := eliminateLeadersNoCollisionFire hψ l' r'
  let q1 := eliminateLeadersNoCollisionMove next q0.1 q0.2
  let q1' := eliminateLeadersNoCollisionMove next' q0'.1 q0'.2
  have hlabel := congrArg PeaceView.label hl
  unfold PeaceView.ofState at hlabel
  dsimp only at hlabel
  have hn : next = next' := by
    apply Fin.ext
    simp [next, next', hlabel]
  have h0 := fire_congr hψ l r l' r' hl hr
  have h1 := move_congr next next' q0.1 q0.2 q0'.1 q0'.2 hn
    (congrArg Prod.fst h0) (congrArg Prod.snd h0)
  have h2 := signal_congr next next' q1.1 q1.2 q1'.1 q1'.2 hn
    (congrArg Prod.fst h1) (congrArg Prod.snd h1)
  rw [eliminateLeadersNoCollision_eq_staged,
    eliminateLeadersNoCollision_eq_staged]
  exact h2

/-! ## Physical prefix and suffix classification

Every repaired stage outside Algorithm 15 is a frame on `PeaceView`.  In the
normal branch the complete output is therefore observationally identical to
running only the no-collision kernel on the original output-safe endpoints.
-/

open PPLLVerify PPLLNoCheckBirthRepair PPLLWriteIncrementGate
  PPLLNoCheckBirthLeaderFrames PPLLNoCheckBirthConditionTwoKernel
  PPLLNoCheckBirthPhysicalConditionOne PPLLNoCheckBirthConditionTwoFrames
  PPLLNoCheckBirthConditionTwoGlobal PPLLNoCheckBirthConditionTwoWriteFrames
  PPLLAuthorizedComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLTerminalEqualSupportRepair

private theorem normalize_peace (u:AuthorizedAgentState ψ) :
 PeaceView.ofState (normalizeDeletion u).core = PeaceView.ofState u.core := by
  apply PeaceView.ext
  all_goals
    unfold normalizeDeletion PeaceView.ofState
    try dsimp only []
    repeat (first | rfl | split)

/-- Priority deletion changes comparison controls but not any peaceful-bullet
field. -/
private theorem eliminateSig_peace (hψ:ψ>0)(l r:AgentState ψ) :
 peaceViewPair (eliminateSig hψ l r)=peaceViewPair (l,r) := by
  have hleaders := eliminateSig_leaders_eq hψ l r
  have hlabels := eliminateSig_labels_eq hψ l r
  have hbullets := eliminateSig_bulletFieldPair hψ l r
  apply Prod.ext <;> apply PeaceView.ext
  · exact hleaders.1
  · exact hlabels.1
  · exact congrArg (fun v=>v.1.shield) hbullets
  · exact congrArg (fun v=>v.1.bullet) hbullets
  · exact congrArg (fun v=>v.1.signal_B) hbullets
  · exact hleaders.2
  · exact hlabels.2
  · exact congrArg (fun v=>v.2.shield) hbullets
  · exact congrArg (fun v=>v.2.bullet) hbullets
  · exact congrArg (fun v=>v.2.signal_B) hbullets

/-- Birth marking only marks comparison carriers for later deletion; it does
not alter the five-field quotient. -/
private theorem mark_peace (born:Bool)
 (q:AuthorizedAgentState ψ×AuthorizedAgentState ψ) :
 authorizedPeaceViewPair (markLeaderBirth born q)=authorizedPeaceViewPair q := by
  apply Prod.ext <;> apply PeaceView.ext
  all_goals
    unfold authorizedPeaceViewPair peaceViewPair PeaceView.ofState
      markLeaderBirth markComparisonForDeletion
    try dsimp only []
    repeat (first | rfl | split)

attribute [local irreducible]
  writeSeqIncrementGate noCheckBirthAuthorizedBeforeEliminate
  noCheckBirthAuthorizedAfterBeforeEliminate noCheckBirthAuthorizedNormal

/-- Gated WRITE preserves the quotient provided a responder leader is at label
zero.  Output safety supplies exactly this fact in the normal branch. -/
private theorem write_peace (hψ:ψ>0)(l r:AgentState ψ)
 (hz:r.leader=true→r.label=⟨0,hψ⟩) :
 peaceViewPair (writeSeqIncrementGate hψ l r)=peaceViewPair (l,r) := by
  have hl := writeSeqIncrementGate_leaders_of_responder_zero hψ l r hz
  have ha := writeSeqIncrementGate_labels hψ l r
  have hb := writeSeqIncrementGate_bulletFieldPair hψ l r
  have hbLS := congrArg (fun v=>v.1.shield) hb
  have hbLB := congrArg (fun v=>v.1.bullet) hb
  have hbLG := congrArg (fun v=>v.1.signal_B) hb
  have hbRS := congrArg (fun v=>v.2.shield) hb
  have hbRB := congrArg (fun v=>v.2.bullet) hb
  have hbRG := congrArg (fun v=>v.2.signal_B) hb
  unfold bulletFieldPair BulletFields.ofState at hbLS hbLB hbLG hbRS hbRB hbRG
  dsimp only at hbLS hbLB hbLG hbRS hbRB hbRG
  apply Prod.ext <;> apply PeaceView.ext
  · exact hl.1
  · exact ha.1
  · exact hbLS
  · exact hbLB
  · exact hbLG
  · exact hl.2
  · exact ha.2
  · exact hbRS
  · exact hbRB
  · exact hbRG

/-- The post-boundary suffix has the same view as Algorithm 15 alone: gated
WRITE is a frame after the kernel. -/
private theorem after_peace (hψ:ψ>0)
 (b:AuthorizedAgentState ψ×AuthorizedAgentState ψ)
 (hz : let k:=eliminateLeadersNoCollision hψ b.1.core b.2.core
       k.2.leader=true→k.2.label=⟨0,hψ⟩) :
 authorizedPeaceViewPair (noCheckBirthAuthorizedAfterBeforeEliminate hψ b)=
 peaceViewPair (eliminateLeadersNoCollision hψ b.1.core b.2.core) := by
  let k:=eliminateLeadersNoCollision hψ b.1.core b.2.core
  unfold noCheckBirthAuthorizedAfterBeforeEliminate
  dsimp only
  exact write_peace hψ k.1 k.2 hz

/-- Edge-local P'_ψ and leader-label facts sufficient for the complete
`PeaceView` refinement.  No global unique-leader premise is stored. -/
structure PeaceEdgeFrame (hψ : ψ > 0) (l r : AgentState ψ) : Prop where
  pPsi_frame :
    (pPsi hψ l r).1.leader = l.leader ∧
    (pPsi hψ l r).1.label = l.label ∧
    (pPsi hψ l r).2.leader = r.leader ∧
    (pPsi hψ l r).2.label = r.label
  responder_zero : r.leader = true → r.label = ⟨0, hψ⟩

/-- Output safety supplies the edge-local frame. -/
theorem PeaceEdgeFrame.of_outputSafe
    (hψ : ψ > 0) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hSafe : OutputSafeConfig hψ ring C)
    (e : Fin n) :
    PeaceEdgeFrame hψ (C e) (C (ring.rightNeighbor e)) where
  pPsi_frame := pPsi_leader_label_of_paperSafe hψ ring C hSafe e
  responder_zero := by
    intro hleader
    exact paperSafe_unique_leader_label_zero hψ ring C hSafe
      (ring.rightNeighbor e)
      (by simpa [AgentState.isLeader] using hleader)

/-- Given an edge-local frame, the exact normalized authorized normal branch is
observationally equal to the isolated no-collision kernel on the original
endpoints, independently of authorization bits. -/
private theorem normal_peace (hψ:ψ>0)(κ:Nat)
 (l r:AuthorizedAgentState ψ)
 (hframe : PeaceEdgeFrame hψ l.core r.core) :
 let l0:=normalizeDeletion l
 let r0:=normalizeDeletion r
 authorizedPeaceViewPair (noCheckBirthAuthorizedNormal hψ κ l0 r0)=
 peaceViewPair (eliminateLeadersNoCollision hψ l.core r.core) := by
  let l0:=normalizeDeletion l
  let r0:=normalizeDeletion r
  change authorizedPeaceViewPair
    (noCheckBirthAuthorizedNormal hψ κ l0 r0) =
      peaceViewPair (eliminateLeadersNoCollision hψ l.core r.core)
  let b:=noCheckBirthAuthorizedBeforeEliminate hψ κ l0 r0
  let k:=eliminateLeadersNoCollision hψ b.1.core b.2.core
  have hb:=PPLLNoCheckBirthConditionTwoPhysical.authorizedBoundary_peaceView_of_pPsi_frame
    hψ κ l r hframe.pPsi_frame
  have hz : k.2.leader=true→k.2.label=⟨0,hψ⟩ := by
    intro hk
    have hbr : b.2.core.leader=true := by
      rw [eliminateLeadersNoCollision_responder_leader_eq hψ
        b.1.core b.2.core] at hk
      exact hk
    have horig : r.core.leader=true := by
      exact (congrArg (fun v=>v.2.leader) hb).symm.trans hbr
    have hzero := hframe.responder_zero horig
    exact (noCollision_labels hψ b.1.core b.2.core).2.trans
      ((congrArg (fun v=>v.2.label) hb).trans hzero)
  have hafter:=after_peace hψ b hz
  have hkernel:=noCollision_congr hψ b.1.core b.2.core l.core r.core
    (congrArg Prod.fst hb) (congrArg Prod.snd hb)
  rw [noCheckBirthAuthorizedNormal_eq_boundarySuffix]
  dsimp only
  have hbEq : b = noCheckBirthAuthorizedBeforeEliminate hψ κ l0 r0 := rfl
  rw [← hbEq]
  exact (mark_peace _ (noCheckBirthAuthorizedAfterBeforeEliminate hψ b)).trans
    (hafter.trans hkernel)

private theorem authorizedEliminateSig_peace (hψ:ψ>0)
 (l r:AuthorizedAgentState ψ) :
 authorizedPeaceViewPair (authorizedEliminateSig hψ l r)=
 authorizedPeaceViewPair (l,r) :=
  eliminateSig_peace hψ l.core r.core

private theorem normalizePair_peace (l r:AuthorizedAgentState ψ) :
 authorizedPeaceViewPair (normalizeDeletion l,normalizeDeletion r)=
 authorizedPeaceViewPair (l,r) :=
  Prod.ext (normalize_peace l) (normalize_peace r)

/-- Both deletion branches frame the input view, while the normal branch has
the isolated-kernel view.  These are all branches of the actual authorized
transition. -/
private theorem authorized_classification (hψ:ψ>0)(κ:Nat)
 (l r:AuthorizedAgentState ψ)
 (hframe : PeaceEdgeFrame hψ l.core r.core) :
 let q:=noCheckBirthAuthorizedTransition hψ κ l r
 authorizedPeaceViewPair q=authorizedPeaceViewPair (l,r) ∨
 authorizedPeaceViewPair q=
   peaceViewPair (eliminateLeadersNoCollision hψ l.core r.core) := by
  let l0:=normalizeDeletion l
  let r0:=normalizeDeletion r
  change authorizedPeaceViewPair
      (noCheckBirthAuthorizedTransition hψ κ l r) =
        authorizedPeaceViewPair (l,r) ∨
    authorizedPeaceViewPair
      (noCheckBirthAuthorizedTransition hψ κ l r) =
        peaceViewPair (eliminateLeadersNoCollision hψ l.core r.core)
  by_cases hr:deletionActive r0
  · rw [noCheckBirthAuthorizedTransition_of_responderDeletion hψ κ l r hr]
    left
    exact (authorizedEliminateSig_peace hψ l0 r0).trans
      (normalizePair_peace l r)
  · by_cases hl:deletionActive l0
    · rw [noCheckBirthAuthorizedTransition_of_initiatorDeletion hψ κ l r hr hl]
      left
      exact normalizePair_peace l r
    · rw [noCheckBirthAuthorizedTransition_of_normal hψ κ l r hr hl]
      right
      exact normal_peace hψ κ l r hframe

/-! ## Exact bounded and timer lift -/

open PPLLExpiringComparisonRepair PPLLPathStallComparisonRepair

/-- Erase both finite endpoint wrappers to the audit states observed by
`PeaceView`. -/
def erasedExpiringPair
 (q:ExpiringAgentState ψ κ τ×ExpiringAgentState ψ κ τ) :
 AgentState ψ×AgentState ψ :=
 (eraseExpiringState q.1,eraseExpiringState q.2)

/-- Carrier expiration and deletion-priority refreshing change no field used
by corrected condition 2. -/
private theorem expire_peace (τ:Nat)
 (old out:ExpiringAgentState ψ κ τ) :
 PeaceView.ofState (eraseExpiringState (deletionPriorityExpireOne τ old out))=
 PeaceView.ofState (eraseExpiringState out) := by
  apply PeaceView.ext
  all_goals
    unfold deletionPriorityExpireOne pathExpireOne clearComparisonCarrier
      eraseExpiringState PeaceView.ofState
    try dsimp only []
    repeat (first | rfl | split)

/-- Exact bounded reification followed by path-stall expiration has the same
endpoint view as the authorized audit transition. -/
private theorem pathStall_peace (hψ:ψ>0)(κ τ:Nat)
 (l r:ExpiringAgentState ψ κ τ) :
 peaceViewPair (erasedExpiringPair
   (noCheckBirthPathStallTransition hψ κ τ l r))=
 authorizedPeaceViewPair (noCheckBirthAuthorizedTransition hψ κ
   l.core.erase r.core.erase) := by
  let q:=noCheckBirthBoundedTransition hψ κ l.core r.core
  let lOut : ExpiringAgentState ψ κ τ:=⟨q.1,l.stall⟩
  let rOut : ExpiringAgentState ψ κ τ:=⟨q.2,r.stall⟩
  have hl:=expire_peace τ l lOut
  have hr:=expire_peace τ r rOut
  have he:=erase_noCheckBirthBoundedTransition hψ κ l.core r.core
  have hexp : peaceViewPair (erasedExpiringPair
      (noCheckBirthPathStallTransition hψ κ τ l r))=
      authorizedPeaceViewPair (q.1.erase,q.2.erase) := by
    unfold noCheckBirthPathStallTransition erasedExpiringPair peaceViewPair
    dsimp only
    exact Prod.ext hl hr
  exact hexp.trans (congrArg authorizedPeaceViewPair he)

/-- In the physical normal branch, exact bounded reification and timer handling
leave the endpoint view equal to the isolated no-collision kernel.  The theorem
is valid even on a self-edge; nontriviality is needed only by the later global
peacefulness proof. -/
theorem noCheckBirthPathStallTransition_peaceView_eq_noCollision_of_normal
    (hψ : ψ > 0) (κ τ : Nat) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ)
    (hSafe : OutputSafeConfig hψ ring (eraseExpiringConfig C)) (e : Fin n)
    (hR : ¬deletionActive
      (normalizeDeletion (C (ring.rightNeighbor e)).core.erase))
    (hL : ¬deletionActive (normalizeDeletion (C e).core.erase)) :
    peaceViewPair (erasedExpiringPair
      (noCheckBirthPathStallTransition hψ κ τ
        (C e) (C (ring.rightNeighbor e)))) =
      peaceViewPair (eliminateLeadersNoCollision hψ
        (eraseExpiringState (C e))
        (eraseExpiringState (C (ring.rightNeighbor e)))) := by
  let raw := eraseExpiringConfig C
  let l := C e
  let r := C (ring.rightNeighbor e)
  let al := l.core.erase
  let ar := r.core.erase
  have hf := pathStall_peace hψ κ τ l r
  have ha : authorizedPeaceViewPair
      (noCheckBirthAuthorizedTransition hψ κ al ar) =
      peaceViewPair (eliminateLeadersNoCollision hψ al.core ar.core) := by
    rw [noCheckBirthAuthorizedTransition_of_normal hψ κ al ar hR hL]
    exact normal_peace hψ κ al ar
      (PeaceEdgeFrame.of_outputSafe hψ ring raw hSafe e)
  exact hf.trans ha

/-- The actual finite physical endpoint pair is observationally either an
identity update (deletion priority) or the no-collision kernel update (normal
branch). -/
private theorem physicalPair_classification_of_frame (hψ:ψ>0)(κ τ:Nat)
 (ring:DirectedRing n)(C:Fin n→ExpiringAgentState ψ κ τ)(e:Fin n)
 (hframe : PeaceEdgeFrame hψ
   (eraseExpiringConfig C e)
   (eraseExpiringConfig C (ring.rightNeighbor e))) :
 let l:=C e
 let r:=C (ring.rightNeighbor e)
 let q:=noCheckBirthPathStallTransition hψ κ τ l r
 peaceViewPair (erasedExpiringPair q)=
   peaceViewPair (eraseExpiringState l,eraseExpiringState r) ∨
 peaceViewPair (erasedExpiringPair q)=
   peaceViewPair (eliminateLeadersNoCollision hψ
     (eraseExpiringState l) (eraseExpiringState r)) := by
  let raw:=eraseExpiringConfig C
  let l:=C e
  let r:=C (ring.rightNeighbor e)
  let q:=noCheckBirthPathStallTransition hψ κ τ l r
  change peaceViewPair (erasedExpiringPair q)=
      peaceViewPair (eraseExpiringState l,eraseExpiringState r) ∨
    peaceViewPair (erasedExpiringPair q)=
      peaceViewPair (eliminateLeadersNoCollision hψ
        (eraseExpiringState l) (eraseExpiringState r))
  have hf:=pathStall_peace hψ κ τ l r
  have hc:=authorized_classification hψ κ l.core.erase r.core.erase hframe
  rcases hc with hc|hc
  · left
    exact hf.trans hc
  · right
    exact hf.trans hc

private theorem physicalPair_classification (hψ:ψ>0)(κ τ:Nat)
 (ring:DirectedRing n)(C:Fin n→ExpiringAgentState ψ κ τ)
 (hSafe:OutputSafeConfig hψ ring (eraseExpiringConfig C))(e:Fin n) :
 let l:=C e
 let r:=C (ring.rightNeighbor e)
 let q:=noCheckBirthPathStallTransition hψ κ τ l r
 peaceViewPair (erasedExpiringPair q)=
   peaceViewPair (eraseExpiringState l,eraseExpiringState r) ∨
 peaceViewPair (erasedExpiringPair q)=
   peaceViewPair (eliminateLeadersNoCollision hψ
     (eraseExpiringState l) (eraseExpiringState r)) := by
  exact physicalPair_classification_of_frame hψ κ τ ring C e
    (PeaceEdgeFrame.of_outputSafe hψ ring (eraseExpiringConfig C) hSafe e)

private theorem leader_eq_of_view_eq {a b:AgentState ψ}
 (h:PeaceView.ofState a=PeaceView.ofState b) : a.leader=b.leader := by
  exact congrArg PeaceView.leader h

private theorem label_eq_of_view_eq {a b:AgentState ψ}
 (h:PeaceView.ofState a=PeaceView.ofState b) : a.label=b.label := by
  exact congrArg PeaceView.label h

private theorem shield_eq_of_view_eq {a b:AgentState ψ}
 (h:PeaceView.ofState a=PeaceView.ofState b) : a.shield=b.shield := by
  exact congrArg PeaceView.shield h

private theorem bullet_eq_of_view_eq {a b:AgentState ψ}
 (h:PeaceView.ofState a=PeaceView.ofState b) : a.bullet=b.bullet := by
  exact congrArg PeaceView.bullet h

private theorem signal_eq_of_view_eq {a b:AgentState ψ}
 (h:PeaceView.ofState a=PeaceView.ofState b) : a.signal_B=b.signal_B := by
  exact congrArg PeaceView.signal_B h

/-! ## Global transport and capstone -/

/-- Peacefulness is invariant under pointwise equality of the five fields it
mentions.  The witness distance and interval are transported unchanged. -/
private theorem noNonPeacefulBullet_of_view_eq
 (hψ:ψ>0)(ring:DirectedRing n)(C D:Fin n→AgentState ψ)
 (hview:∀i,PeaceView.ofState (D i)=PeaceView.ofState (C i))
 (hpeace:noNonPeacefulBullet hψ ring C) :
 noNonPeacefulBullet hψ ring D := by
  intro start hLiveD
  have hLiveC : (C start).bullet=⟨2,by omega⟩ :=
    (bullet_eq_of_view_eq (hview start)).symm.trans hLiveD
  obtain ⟨_,d,hd,htarget,hshield,hsignal,hlabel⟩:=hpeace start hLiveC
  refine ⟨hLiveD,d,hd,?_,?_,?_,?_⟩
  · change (D ⟨(start.val+d)%n,Nat.mod_lt _ ring.hn⟩).leader=true
    exact (leader_eq_of_view_eq
      (hview ⟨(start.val+d)%n,Nat.mod_lt _ ring.hn⟩)).trans htarget
  · exact (shield_eq_of_view_eq
      (hview ⟨(start.val+d)%n,Nat.mod_lt _ ring.hn⟩)).trans hshield
  · intro k hk
    exact (signal_eq_of_view_eq
      (hview ⟨(start.val+k)%n,Nat.mod_lt _ ring.hn⟩)).trans (hsignal k hk)
  · intro k hk
    exact (label_eq_of_view_eq
      (hview ⟨(start.val+(k+1))%n,Nat.mod_lt _ ring.hn⟩)).trans
      ((hlabel k hk).trans (by
        apply Fin.ext
        exact congrArg (fun a : Fin ψ => (a.val + 1) % ψ)
          (label_eq_of_view_eq
            (hview ⟨(start.val+k)%n,Nat.mod_lt _ ring.hn⟩)).symm))

private theorem updatePair_view_eq_of_pair
 (C:Fin n→AgentState ψ)(i j:Fin n)(q q':AgentState ψ×AgentState ψ)
 (hq:peaceViewPair q=peaceViewPair q') :
 ∀k,PeaceView.ofState (updatePair C i j q k)=
   PeaceView.ofState (updatePair C i j q' k) := by
  intro k
  by_cases hki:k=i
  · subst k
    rw [updatePair_initiator,updatePair_initiator]
    exact congrArg Prod.fst hq
  · by_cases hkj:k=j
    · have hji : j ≠ i := by
        intro h
        exact hki (hkj.trans h)
      subst k
      rw [updatePair_responder C i j q hji,
        updatePair_responder C i j q' hji]
      exact congrArg Prod.snd hq
    · rw [updatePair_other C i j k q hki hkj,
        updatePair_other C i j k q' hki hkj]

private theorem updatePair_input_view
 (C:Fin n→AgentState ψ)(i j:Fin n) :
 ∀k,PeaceView.ofState (updatePair C i j (C i,C j) k)=
   PeaceView.ofState (C k) := by
  intro k
  by_cases hki:k=i
  · subst k
    rw [updatePair_initiator]
  · by_cases hkj:k=j
    · have hji : j ≠ i := by
        intro h
        exact hki (hkj.trans h)
      subst k
      rw [updatePair_responder C i j (C i,C j) hji]
    · rw [updatePair_other C i j k (C i,C j) hki hkj]

/-- Erasing one packaged finite protocol step gives the corresponding audit
configuration update on the erased physical pair. -/
private theorem erased_protocol_step
 (hψ:ψ>0)(κ τ:Nat)(ring:DirectedRing n)
 (C:Fin n→ExpiringAgentState ψ κ τ)(e:Fin n) :
 eraseExpiringConfig ((noCheckBirthProtocol hψ κ τ).step ring C e)=
 updatePair (eraseExpiringConfig C) e (ring.rightNeighbor e)
   (erasedExpiringPair (noCheckBirthPathStallTransition hψ κ τ
     (C e) (C (ring.rightNeighbor e)))) := by
  funext k
  by_cases hke:k=e
  · simp [PopulationProtocol.step,noCheckBirthProtocol,updatePair,
      eraseExpiringConfig,erasedExpiringPair,hke]
  · by_cases hkr:k=ring.rightNeighbor e
    · have hre:ring.rightNeighbor e≠e:=by
        intro hre
        exact hke (hkr.trans hre)
      simp [PopulationProtocol.step,noCheckBirthProtocol,updatePair,
        eraseExpiringConfig,erasedExpiringPair,hkr,hre]
    · simp [PopulationProtocol.step,noCheckBirthProtocol,updatePair,
        eraseExpiringConfig,hke,hkr]

/-- If deletion priority is inactive, the erased packaged protocol step is
pointwise `PeaceView`-equal to the isolated no-collision configuration step.
Unlike the preservation capstone, this exact refinement also covers self-edges
and is used to certify the necessary `n = 1` regression. -/
theorem noCheckBirthProtocol_step_peaceView_eq_noCollisionStep_of_normal
    (hψ : ψ > 0) (κ τ : Nat) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ)
    (hSafe : OutputSafeConfig hψ ring (eraseExpiringConfig C)) (e : Fin n)
    (hR : ¬deletionActive
      (normalizeDeletion (C (ring.rightNeighbor e)).core.erase))
    (hL : ¬deletionActive (normalizeDeletion (C e).core.erase)) :
    ∀ k, PeaceView.ofState
        (eraseExpiringConfig
          ((noCheckBirthProtocol hψ κ τ).step ring C e) k) =
      PeaceView.ofState (noCollisionStep hψ ring
        (eraseExpiringConfig C) e k) := by
  let raw := eraseExpiringConfig C
  let physical := noCheckBirthPathStallTransition hψ κ τ
    (C e) (C (ring.rightNeighbor e))
  have hstep := erased_protocol_step hψ κ τ ring C e
  have hpair :=
    noCheckBirthPathStallTransition_peaceView_eq_noCollision_of_normal
      hψ κ τ ring C hSafe e hR hL
  intro k
  rw [hstep]
  exact updatePair_view_eq_of_pair raw e (ring.rightNeighbor e)
    (erasedExpiringPair physical)
    (eliminateLeadersNoCollision hψ (raw e)
      (raw (ring.rightNeighbor e))) hpair k

/-- Every exact finite repaired step is pointwise `PeaceView`-equal either to
its input or to the isolated no-collision Algorithm-15 update.  The first case
collects both deletion-priority branches; the second is the complete normal
branch.  This public disjunction is the reusable physical refinement boundary
for later corrected safety conditions. -/
theorem noCheckBirthProtocol_step_peaceView_classification_of_frame
    (hψ : ψ > 0) (κ τ : Nat) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (e : Fin n)
    (hframe : PeaceEdgeFrame hψ
      (eraseExpiringConfig C e)
      (eraseExpiringConfig C (ring.rightNeighbor e))) :
    (∀ k, PeaceView.ofState
        (eraseExpiringConfig
          ((noCheckBirthProtocol hψ κ τ).step ring C e) k) =
      PeaceView.ofState (eraseExpiringConfig C k)) ∨
    (∀ k, PeaceView.ofState
        (eraseExpiringConfig
          ((noCheckBirthProtocol hψ κ τ).step ring C e) k) =
      PeaceView.ofState (noCollisionStep hψ ring
        (eraseExpiringConfig C) e k)) := by
  let raw := eraseExpiringConfig C
  let physical := noCheckBirthPathStallTransition hψ κ τ
    (C e) (C (ring.rightNeighbor e))
  let D := eraseExpiringConfig
    ((noCheckBirthProtocol hψ κ τ).step ring C e)
  change (∀ k, PeaceView.ofState (D k) = PeaceView.ofState (raw k)) ∨
    (∀ k, PeaceView.ofState (D k) =
      PeaceView.ofState (noCollisionStep hψ ring raw e k))
  have hstep : D = updatePair raw e (ring.rightNeighbor e)
      (erasedExpiringPair physical) :=
    erased_protocol_step hψ κ τ ring C e
  have hclass := physicalPair_classification_of_frame
    hψ κ τ ring C e hframe
  rcases hclass with hin | hkernel
  · left
    intro k
    rw [hstep]
    exact (updatePair_view_eq_of_pair raw e (ring.rightNeighbor e)
      (erasedExpiringPair physical) (raw e, raw (ring.rightNeighbor e))
      hin k).trans (updatePair_input_view raw e (ring.rightNeighbor e) k)
  · right
    intro k
    rw [hstep]
    exact updatePair_view_eq_of_pair raw e (ring.rightNeighbor e)
      (erasedExpiringPair physical)
      (eliminateLeadersNoCollision hψ (raw e)
        (raw (ring.rightNeighbor e))) hkernel k

/-- Output safety supplies the edge-local frame required by the public
classification. -/
theorem noCheckBirthProtocol_step_peaceView_classification
    (hψ : ψ > 0) (κ τ : Nat) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ)
    (hSafe : OutputSafeConfig hψ ring (eraseExpiringConfig C)) (e : Fin n) :
    (∀ k, PeaceView.ofState
        (eraseExpiringConfig
          ((noCheckBirthProtocol hψ κ τ).step ring C e) k) =
      PeaceView.ofState (eraseExpiringConfig C k)) ∨
    (∀ k, PeaceView.ofState
        (eraseExpiringConfig
          ((noCheckBirthProtocol hψ κ τ).step ring C e) k) =
      PeaceView.ofState (noCollisionStep hψ ring
        (eraseExpiringConfig C) e k)) := by
  exact noCheckBirthProtocol_step_peaceView_classification_of_frame
    hψ κ τ ring C e
    (PeaceEdgeFrame.of_outputSafe hψ ring (eraseExpiringConfig C) hSafe e)

/-- **Finite physical corrected condition 2.**  On every nontrivial ring, one
exact step of the bounded no-CHECK-birth protocol preserves Wu's literal
peaceful-bullet predicate from an output-safe erased configuration.  The theorem
covers arbitrary authorization bits and stall timers, both deletion-priority
branches, the complete normal branch, bounded reification, carrier clearing,
and expiration. -/
theorem noNonPeacefulBullet_preserved_noCheckBirthProtocol (hψ:ψ>0)(κ τ:Nat)(hn2:1<n)
 (ring:DirectedRing n)(C:Fin n→ExpiringAgentState ψ κ τ)
 (hSafe:OutputSafeConfig hψ ring (eraseExpiringConfig C))(e:Fin n) :
 noNonPeacefulBullet hψ ring
   (eraseExpiringConfig ((noCheckBirthProtocol hψ κ τ).step ring C e)) := by
  let raw:=eraseExpiringConfig C
  let l:=C e
  let r:=C (ring.rightNeighbor e)
  let physical:=noCheckBirthPathStallTransition hψ κ τ l r
  let D:=eraseExpiringConfig ((noCheckBirthProtocol hψ κ τ).step ring C e)
  have hstep:=erased_protocol_step hψ κ τ ring C e
  have hstep' : D = updatePair raw e (ring.rightNeighbor e)
      (erasedExpiringPair physical) := hstep
  have hclass:=physicalPair_classification hψ κ τ ring C hSafe e
  rcases hclass with hin|hkernel
  · apply noNonPeacefulBullet_of_view_eq hψ ring raw D
    · intro k
      rw [hstep']
      exact (updatePair_view_eq_of_pair raw e (ring.rightNeighbor e)
        (erasedExpiringPair physical) (raw e,raw (ring.rightNeighbor e))
        hin k).trans (updatePair_input_view raw e
          (ring.rightNeighbor e) k)
    · exact hSafe.no_nonpeaceful_bullet
  · apply noNonPeacefulBullet_of_view_eq hψ ring
      (noCollisionStep hψ ring raw e) D
    · intro k
      rw [hstep']
      exact updatePair_view_eq_of_pair raw e (ring.rightNeighbor e)
        (erasedExpiringPair physical)
        (eliminateLeadersNoCollision hψ (raw e)
          (raw (ring.rightNeighbor e))) hkernel k
    · exact noNonPeacefulBullet_preserved_noCollisionStep
        hψ hn2 ring raw hSafe e

end PPLLNoCheckBirthConditionTwoProtocol
