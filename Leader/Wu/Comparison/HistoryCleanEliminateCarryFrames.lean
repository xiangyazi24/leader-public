import Leader.Wu.Splice.CheckWholeStepCuts


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace B9CheckWholeStep


open PPLL PPLLRepair
open PPLLAuthorizedComparisonRepair
open PPLLComparisonHistory


variable {n psi : Nat}


private theorem fullPair_of_audit_pCarry_frame
    (l r : MarkedAgentState n psi)
    (q : MarkedAgentState n psi × MarkedAgentState n psi)
    (hin :
      FullLocalHistoryTrusted l.concrete l.history ∧
      FullLocalHistoryTrusted r.concrete r.history)
    (haudit :
      AuditLocalHistoryTrusted q.1.concrete q.1.history ∧
      AuditLocalHistoryTrusted q.2.concrete q.2.history)
    (hp :
      q.1.concrete.p_carry = l.concrete.p_carry ∧
      q.2.concrete.p_carry = r.concrete.p_carry)
    (hh :
      q.1.history.pCarry = l.history.pCarry ∧
      q.2.history.pCarry = r.history.pCarry) :
    FullLocalHistoryTrusted q.1.concrete q.1.history ∧
      FullLocalHistoryTrusted q.2.concrete q.2.history := by
  constructor
  · constructor
    · exact haudit.1
    · unfold PCarryHistoryTrusted
      rw [hp.1, hh.1]
      exact hin.1.2
  · constructor
    · exact haudit.2
    · unfold PCarryHistoryTrusted
      rw [hp.2, hh.2]
      exact hin.2.2


/-! CLEAN_SIG: local physical pCarry frames. -/


private theorem cleanSigGenConnect_pCarry (u : AgentState psi) :
    (cleanSigGenConnect u).p_carry = u.p_carry := by
  have path4_pCarry (v : AgentState psi) (x : Option (Int × Nat)) :
      ({ v with path4 := x }).p_carry = v.p_carry := by
    cases v
    rfl
  have path5_pCarry (v : AgentState psi) (x : Option (Int × Nat)) :
      ({ v with path5 := x }).p_carry = v.p_carry := by
    cases v
    rfl
  cases hpath : u.path with
  | bot =>
      simp only [cleanSigGenConnect, hpath]
  | some pathLabel pathBit =>
      by_cases h0 : pathLabel ≠ 0
      · by_cases hlast : pathLabel ≠ psi - 1
        · simpa only [cleanSigGenConnect, hpath, if_pos h0, if_pos hlast] using
            (path5_pCarry
              ({ u with path4 := some (Int.ofNat pathLabel, 1) })
              (some (Int.ofNat pathLabel, 1))).trans
              (path4_pCarry u (some (Int.ofNat pathLabel, 1)))
        · simpa only [cleanSigGenConnect, hpath, if_pos h0, if_neg hlast] using
            path4_pCarry u (some (Int.ofNat pathLabel, 1))
      · by_cases hlast : pathLabel ≠ psi - 1
        · simpa only [cleanSigGenConnect, hpath, if_neg h0, if_pos hlast] using
            path5_pCarry u (some (Int.ofNat pathLabel, 1))
        · simp only [cleanSigGenConnect, hpath, if_neg h0, if_neg hlast]


private theorem cleanSigCleanApply_eq_update (u : AgentState psi) :
    ∃ (a : PathInfo) (b c : Option (Int × Nat)),
      cleanSigCleanApply u =
        { u with path := a, path4 := b, path5 := c } := by
  cases u
  unfold cleanSigCleanApply
  repeat
    first
    | exact ⟨_, _, _, rfl⟩
    | split
    | dsimp only

private theorem cleanSigCleanApply_pCarry (u : AgentState psi) :
    (cleanSigCleanApply u).p_carry = u.p_carry := by
  obtain ⟨a, b, c, h⟩ := cleanSigCleanApply_eq_update u
  rw [h]


private theorem cleanSigStep3_pCarry (l r : AgentState psi) :
    let q := cleanSigStep3 l r
    q.1.p_carry = l.p_carry ∧ q.2.p_carry = r.p_carry := by
  unfold cleanSigStep3
  repeat (first | exact ⟨rfl, rfl⟩ | split)


private theorem cleanSigStep4_pCarry (l r : AgentState psi) :
    let q := cleanSigStep4 l r
    q.1.p_carry = l.p_carry ∧ q.2.p_carry = r.p_carry := by
  unfold cleanSigStep4
  repeat (first | exact ⟨rfl, rfl⟩ | split)


private theorem cleanSigStep5_pCarry (hpsi : 0 < psi)
    (l r : AgentState psi) :
    let q := cleanSigStep5 hpsi l r
    q.1.p_carry = l.p_carry ∧ q.2.p_carry = r.p_carry := by
  unfold cleanSigStep5
  repeat (first | exact ⟨rfl, rfl⟩ | split)


private theorem cleanSigStep6_pCarry (hpsi : 0 < psi)
    (l r : AgentState psi) :
    let q := cleanSigStep6 hpsi l r
    q.1.p_carry = l.p_carry ∧ q.2.p_carry = r.p_carry := by
  unfold cleanSigStep6
  repeat (first | exact ⟨rfl, rfl⟩ | split)


/-- Chain the literal CLEAN_SIG subrows; do not unfold the whole row. -/
private theorem cleanSig_pCarry_frame (hpsi : 0 < psi)
    (l r : AgentState psi) :
    let q := cleanSig hpsi l r
    q.1.p_carry = l.p_carry ∧ q.2.p_carry = r.p_carry := by
  let l0 := cleanSigGenConnect l
  let r0 := cleanSigGenConnect r
  let q1 := cleanSigStep3 l0 r0
  let q2 := cleanSigStep4 q1.1 q1.2
  let q3 := cleanSigStep5 hpsi q2.1 q2.2
  let q4 := cleanSigStep6 hpsi q3.1 q3.2
  have hl0 := cleanSigGenConnect_pCarry l
  have hr0 := cleanSigGenConnect_pCarry r
  have h1 := cleanSigStep3_pCarry l0 r0
  have h2 := cleanSigStep4_pCarry q1.1 q1.2
  have h3 := cleanSigStep5_pCarry hpsi q2.1 q2.2
  have h4 := cleanSigStep6_pCarry hpsi q3.1 q3.2
  change l0.p_carry = l.p_carry at hl0
  change r0.p_carry = r.p_carry at hr0
  change q1.1.p_carry = l0.p_carry ∧
    q1.2.p_carry = r0.p_carry at h1
  change q2.1.p_carry = q1.1.p_carry ∧
    q2.2.p_carry = q1.2.p_carry at h2
  change q3.1.p_carry = q2.1.p_carry ∧
    q3.2.p_carry = q2.2.p_carry at h3
  change q4.1.p_carry = q3.1.p_carry ∧
    q4.2.p_carry = q3.2.p_carry at h4
  change
    (cleanSigCleanApply q4.1).p_carry = l.p_carry ∧
      (cleanSigCleanApply q4.2).p_carry = r.p_carry
  exact ⟨
    (cleanSigCleanApply_pCarry q4.1).trans
      (h4.1.trans (h3.1.trans (h2.1.trans (h1.1.trans hl0)))),
    (cleanSigCleanApply_pCarry q4.2).trans
      (h4.2.trans (h3.2.trans (h2.2.trans (h1.2.trans hr0))))⟩


private theorem markedCleanSig_pCarry_history_frame
    (hpsi : 0 < psi) (l r : MarkedAgentState n psi) :
    let q := markedCleanSig hpsi l r
    q.1.history.pCarry = l.history.pCarry ∧
      q.2.history.pCarry = r.history.pCarry := by
  unfold markedCleanSig
  exact ⟨rfl, rfl⟩


private theorem markedCleanSig_preserves_fullLocalHistoryTrusted_local
    (hpsi : 0 < psi) (l r : MarkedAgentState n psi)
    (hl : FullLocalHistoryTrusted l.concrete l.history)
    (hr : FullLocalHistoryTrusted r.concrete r.history) :
    let q := markedCleanSig hpsi l r
    FullLocalHistoryTrusted q.1.concrete q.1.history ∧
      FullLocalHistoryTrusted q.2.concrete q.2.history := by
  let q := markedCleanSig hpsi l r
  have ha := markedCleanSig_preserves_auditLocalHistoryTrusted
    hpsi l r hl.1 hr.1
  change AuditLocalHistoryTrusted q.1.concrete q.1.history ∧
    AuditLocalHistoryTrusted q.2.concrete q.2.history at ha
  have he := erase_markedCleanSig hpsi l r
  change (q.1.concrete, q.2.concrete) =
    cleanSig hpsi l.concrete r.concrete at he
  have hp0 := cleanSig_pCarry_frame hpsi l.concrete r.concrete
  change
    (cleanSig hpsi l.concrete r.concrete).1.p_carry = l.concrete.p_carry ∧
      (cleanSig hpsi l.concrete r.concrete).2.p_carry = r.concrete.p_carry at hp0
  have hp :
      q.1.concrete.p_carry = l.concrete.p_carry ∧
        q.2.concrete.p_carry = r.concrete.p_carry := by
    exact ⟨
      (congrArg (fun p : AgentState psi × AgentState psi => p.1.p_carry) he).trans hp0.1,
      (congrArg (fun p : AgentState psi × AgentState psi => p.2.p_carry) he).trans hp0.2⟩
  have hh := markedCleanSig_pCarry_history_frame hpsi l r
  change q.1.history.pCarry = l.history.pCarry ∧
    q.2.history.pCarry = r.history.pCarry at hh
  exact fullPair_of_audit_pCarry_frame l r q ⟨hl, hr⟩ ha hp hh


/-! ELIMINATE_SIG is one atomic stage; both fields are framed directly. -/


private theorem eliminateSig_pCarry_frame (hpsi : 0 < psi)
    (l r : AgentState psi) :
    let q := eliminateSig hpsi l r
    q.1.p_carry = l.p_carry ∧ q.2.p_carry = r.p_carry := by
  unfold eliminateSig
  repeat (first | exact ⟨rfl, rfl⟩ | split)


private theorem markedEliminateSig_pCarry_history_frame
    (hpsi : 0 < psi) (l r : MarkedAgentState n psi) :
    let q := markedEliminateSig hpsi l r
    q.1.history.pCarry = l.history.pCarry ∧
      q.2.history.pCarry = r.history.pCarry := by
  unfold markedEliminateSig
  repeat (first | exact ⟨rfl, rfl⟩ | split)


private theorem markedEliminateSig_preserves_fullLocalHistoryTrusted_local
    (hpsi : 0 < psi) (l r : MarkedAgentState n psi)
    (hl : FullLocalHistoryTrusted l.concrete l.history)
    (hr : FullLocalHistoryTrusted r.concrete r.history) :
    let q := markedEliminateSig hpsi l r
    FullLocalHistoryTrusted q.1.concrete q.1.history ∧
      FullLocalHistoryTrusted q.2.concrete q.2.history := by
  let q := markedEliminateSig hpsi l r
  have ha := markedEliminateSig_preserves_auditLocalHistoryTrusted
    hpsi l r hl.1 hr.1
  change AuditLocalHistoryTrusted q.1.concrete q.1.history ∧
    AuditLocalHistoryTrusted q.2.concrete q.2.history at ha
  have he := erase_markedEliminateSig hpsi l r
  change (q.1.concrete, q.2.concrete) =
    eliminateSig hpsi l.concrete r.concrete at he
  have hp0 := eliminateSig_pCarry_frame hpsi l.concrete r.concrete
  change
    (eliminateSig hpsi l.concrete r.concrete).1.p_carry = l.concrete.p_carry ∧
      (eliminateSig hpsi l.concrete r.concrete).2.p_carry = r.concrete.p_carry at hp0
  have hp :
      q.1.concrete.p_carry = l.concrete.p_carry ∧
        q.2.concrete.p_carry = r.concrete.p_carry := by
    exact ⟨
      (congrArg (fun p : AgentState psi × AgentState psi => p.1.p_carry) he).trans hp0.1,
      (congrArg (fun p : AgentState psi × AgentState psi => p.2.p_carry) he).trans hp0.2⟩
  have hh := markedEliminateSig_pCarry_history_frame hpsi l r
  change q.1.history.pCarry = l.history.pCarry ∧
    q.2.history.pCarry = r.history.pCarry at hh
  exact fullPair_of_audit_pCarry_frame l r q ⟨hl, hr⟩ ha hp hh


/-- The missing B9 CHECK cut hypothesis needs no compatibility premise. -/
theorem currentCleanEliminateFullPreservation
    {n psi : Nat} (hpsi : 0 < psi) :
    CurrentCleanEliminateFullPreservation (n := n) hpsi := by
  unfold CurrentCleanEliminateFullPreservation
  intro l r hin
  change FullLocalHistoryTrusted l.concrete.core l.history ∧
    FullLocalHistoryTrusted r.concrete.core r.history at hin


  let lm : MarkedAgentState n psi := ⟨l.concrete.core, l.history⟩
  let rm : MarkedAgentState n psi := ⟨r.concrete.core, r.history⟩
  let c := markedCleanSig hpsi lm rm
  let e := markedEliminateSig hpsi c.1 c.2
  let pc := authorizedCleanSig hpsi l.concrete r.concrete
  let pe := authorizedEliminateSig hpsi pc.1 pc.2


  have hc := markedCleanSig_preserves_fullLocalHistoryTrusted_local
    hpsi lm rm hin.1 hin.2
  change FullLocalHistoryTrusted c.1.concrete c.1.history ∧
    FullLocalHistoryTrusted c.2.concrete c.2.history at hc
  have he := markedEliminateSig_preserves_fullLocalHistoryTrusted_local
    hpsi c.1 c.2 hc.1 hc.2
  change FullLocalHistoryTrusted e.1.concrete e.1.history ∧
    FullLocalHistoryTrusted e.2.concrete e.2.history at he


  have hce := erase_markedCleanSig hpsi lm rm
  change (c.1.concrete, c.2.concrete) =
    cleanSig hpsi l.concrete.core r.concrete.core at hce
  have hpc :
      (pc.1.core, pc.2.core) =
        cleanSig hpsi l.concrete.core r.concrete.core := by
    rfl
  have hcleanCore :
      (pc.1.core, pc.2.core) =
        (c.1.concrete, c.2.concrete) := hpc.trans hce.symm
  obtain ⟨hcleanL, hcleanR⟩ := Prod.mk.inj hcleanCore


  have hee := erase_markedEliminateSig hpsi c.1 c.2
  change (e.1.concrete, e.2.concrete) =
    eliminateSig hpsi c.1.concrete c.2.concrete at hee
  have hpe :
      (pe.1.core, pe.2.core) =
        eliminateSig hpsi c.1.concrete c.2.concrete := by
    calc
      (pe.1.core, pe.2.core) =
          eliminateSig hpsi pc.1.core pc.2.core := by rfl
      _ = eliminateSig hpsi c.1.concrete c.2.concrete := by
        rw [hcleanL, hcleanR]
  have hcore :
      (pe.1.core, pe.2.core) =
        (e.1.concrete, e.2.concrete) := hpe.trans hee.symm
  obtain ⟨hcoreL, hcoreR⟩ := Prod.mk.inj hcore


  change FullLocalHistoryTrusted pe.1.core e.1.history ∧
    FullLocalHistoryTrusted pe.2.core e.2.history
  constructor
  · rw [hcoreL]
    exact he.1
  · rw [hcoreR]
    exact he.2


end B9CheckWholeStep


#print axioms B9CheckWholeStep.currentCleanEliminateFullPreservation
