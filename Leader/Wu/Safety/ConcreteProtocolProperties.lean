import Leader.Wu.Safety.ConditionalClosedness
import Leader.Wu.Protocol.Algorithm

/-!
# Verification of ProtocolProperties for the Concrete P_PLL

Only P'_ψ (Algorithm 2) modifies labels. All other sub-algorithms preserve
labels unconditionally. Barrier status depends only on labels, so it is
determined entirely by P'_ψ.
-/

namespace PPLLVerify

open PPLL

variable {ψ : Nat} (hψ : ψ > 0)

/-! ## Simp infrastructure for pushing projections through ite -/

section IteSimp

variable {c : Prop} [Decidable c]

@[simp] private theorem Prod_fst_ite (a b : α × β) :
    (if c then a else b).1 = if c then a.1 else b.1 := by
  by_cases h : c <;> simp [h]

@[simp] private theorem Prod_snd_ite (a b : α × β) :
    (if c then a else b).2 = if c then a.2 else b.2 := by
  by_cases h : c <;> simp [h]

@[simp] private theorem AgentState_label_ite (a b : AgentState ψ) :
    (if c then a else b).label = if c then a.label else b.label := by
  by_cases h : c <;> simp [h]

@[simp] private theorem AgentState_leader_ite (a b : AgentState ψ) :
    (if c then a else b).leader = if c then a.leader else b.leader := by
  by_cases h : c <;> simp [h]

@[simp] private theorem AgentState_reset_cmd_ite (a b : AgentState ψ) :
    (if c then a else b).reset_cmd = if c then a.reset_cmd else b.reset_cmd := by
  by_cases h : c <;> simp [h]

@[simp] private theorem AgentState_echo_ite (a b : AgentState ψ) :
    (if c then a else b).echo = if c then a.echo else b.echo := by
  by_cases h : c <;> simp [h]

@[simp] private theorem AgentState_signal_B_ite (a b : AgentState ψ) :
    (if c then a else b).signal_B = if c then a.signal_B else b.signal_B := by
  by_cases h : c <;> simp [h]

@[simp] private theorem AgentState_bullet_ite (a b : AgentState ψ) :
    (if c then a else b).bullet = if c then a.bullet else b.bullet := by
  by_cases h : c <;> simp [h]

@[simp] private theorem AgentState_shield_ite (a b : AgentState ψ) :
    (if c then a else b).shield = if c then a.shield else b.shield := by
  by_cases h : c <;> simp [h]

@[simp] private theorem AgentState_probe_ite (a b : AgentState ψ) :
    (if c then a else b).probe = if c then a.probe else b.probe := by
  by_cases h : c <;> simp [h]

@[simp] private theorem AgentState_phase_ite (a b : AgentState ψ) :
    (if c then a else b).phase = if c then a.phase else b.phase := by
  by_cases h : c <;> simp [h]

@[simp] private theorem AgentState_state_ite (a b : AgentState ψ) :
    (if c then a else b).state = if c then a.state else b.state := by
  by_cases h : c <;> simp [h]

@[simp] private theorem AgentState_bit_ite (a b : AgentState ψ) :
    (if c then a else b).bit = if c then a.bit else b.bit := by
  by_cases h : c <;> simp [h]

@[simp] private theorem AgentState_wait_ite (a b : AgentState ψ) :
    (if c then a else b).wait = if c then a.wait else b.wait := by
  by_cases h : c <;> simp [h]

@[simp] private theorem AgentState_path_ite (a b : AgentState ψ) :
    (if c then a else b).path = if c then a.path else b.path := by
  by_cases h : c <;> simp [h]

@[simp] private theorem AgentState_path3_ite (a b : AgentState ψ) :
    (if c then a else b).path3 = if c then a.path3 else b.path3 := by
  by_cases h : c <;> simp [h]

@[simp] private theorem AgentState_write_state_ite (a b : AgentState ψ) :
    (if c then a else b).write_state = if c then a.write_state else b.write_state := by
  by_cases h : c <;> simp [h]

@[simp] private theorem AgentState_write_ite (a b : AgentState ψ) :
    (if c then a else b).write = if c then a.write else b.write := by
  by_cases h : c <;> simp [h]

@[simp] private theorem AgentState_last_ite (a b : AgentState ψ) :
    (if c then a else b).last = if c then a.last else b.last := by
  by_cases h : c <;> simp [h]

@[simp] private theorem AgentState_last_set_ite (a b : AgentState ψ) :
    (if c then a else b).last_set = if c then a.last_set else b.last_set := by
  by_cases h : c <;> simp [h]

@[simp] private theorem AgentState_last_unset_ite (a b : AgentState ψ) :
    (if c then a else b).last_unset = if c then a.last_unset else b.last_unset := by
  by_cases h : c <;> simp [h]

@[simp] private theorem AgentState_gen_ws_ite (a b : AgentState ψ) :
    (if c then a else b).gen_ws = if c then a.gen_ws else b.gen_ws := by
  by_cases h : c <;> simp [h]

@[simp] private theorem AgentState_ws_echo_ite (a b : AgentState ψ) :
    (if c then a else b).ws_echo = if c then a.ws_echo else b.ws_echo := by
  by_cases h : c <;> simp [h]

@[simp] private theorem AgentState_signal_ws_ite (a b : AgentState ψ) :
    (if c then a else b).signal_ws = if c then a.signal_ws else b.signal_ws := by
  by_cases h : c <;> simp [h]

@[simp] private theorem AgentState_reset_ite (a b : AgentState ψ) :
    (if c then a else b).reset = if c then a.reset else b.reset := by
  by_cases h : c <;> simp [h]

@[simp] private theorem AgentState_carry_ite (a b : AgentState ψ) :
    (if c then a else b).carry = if c then a.carry else b.carry := by
  by_cases h : c <;> simp [h]

@[simp] private theorem AgentState_count_ite (a b : AgentState ψ) :
    (if c then a else b).count = if c then a.count else b.count := by
  by_cases h : c <;> simp [h]

@[simp] private theorem AgentState_h_field_ite (a b : AgentState ψ) :
    (if c then a else b).h_field = if c then a.h_field else b.h_field := by
  by_cases h : c <;> simp [h]

@[simp] private theorem AgentState_b_carry_ite (a b : AgentState ψ) :
    (if c then a else b).b_carry = if c then a.b_carry else b.b_carry := by
  by_cases h : c <;> simp [h]

@[simp] private theorem AgentState_path2_ite (a b : AgentState ψ) :
    (if c then a else b).path2 = if c then a.path2 else b.path2 := by
  by_cases h : c <;> simp [h]

@[simp] private theorem AgentState_path4_ite (a b : AgentState ψ) :
    (if c then a else b).path4 = if c then a.path4 else b.path4 := by
  by_cases h : c <;> simp [h]

@[simp] private theorem AgentState_path5_ite (a b : AgentState ψ) :
    (if c then a else b).path5 = if c then a.path5 else b.path5 := by
  by_cases h : c <;> simp [h]

@[simp] private theorem AgentState_p_ite (a b : AgentState ψ) :
    (if c then a else b).p = if c then a.p else b.p := by
  by_cases h : c <;> simp [h]

@[simp] private theorem AgentState_p_carry_ite (a b : AgentState ψ) :
    (if c then a else b).p_carry = if c then a.p_carry else b.p_carry := by
  by_cases h : c <;> simp [h]

@[simp] private theorem ite_same (a : α) :
    (if c then a else a) = a := by by_cases h : c <;> simp [h]

end IteSimp

/-! ## Match-pushing lemmas (not @[simp] — used only where needed) -/

section MatchSimp

variable {ψ : Nat}

private theorem Prod_fst_match_pathInfo (p : PathInfo)
    (f : Nat → Nat → α × β) (g : α × β) :
    (match p with | .some l b => f l b | .bot => g).1 =
    match p with | .some l b => (f l b).1 | .bot => g.1 := by
  cases p <;> rfl

private theorem Prod_snd_match_pathInfo (p : PathInfo)
    (f : Nat → Nat → α × β) (g : α × β) :
    (match p with | .some l b => f l b | .bot => g).2 =
    match p with | .some l b => (f l b).2 | .bot => g.2 := by
  cases p <;> rfl

private theorem AgentState_label_match_pathInfo (p : PathInfo)
    (f : Nat → Nat → AgentState ψ) (g : AgentState ψ) :
    (match p with | .some l b => f l b | .bot => g).label =
    match p with | .some l b => (f l b).label | .bot => g.label := by
  cases p <;> rfl

private theorem Prod_fst_match_option {α : Type} (x : Option α)
    (f : α → β × γ) (g : β × γ) :
    (match x with | some a => f a | none => g).1 =
    match x with | some a => (f a).1 | none => g.1 := by
  cases x <;> rfl

private theorem Prod_snd_match_option {α : Type} (x : Option α)
    (f : α → β × γ) (g : β × γ) :
    (match x with | some a => f a | none => g).2 =
    match x with | some a => (f a).2 | none => g.2 := by
  cases x <;> rfl

private theorem AgentState_label_match_option {α : Type} (x : Option α)
    (f : α → AgentState ψ) (g : AgentState ψ) :
    (match x with | some a => f a | none => g).label =
    match x with | some a => (f a).label | none => g.label := by
  cases x <;> rfl

private theorem match_pathInfo_same (p : PathInfo) (a : α) :
    (match p with | .some _ _ => a | .bot => a) = a := by
  cases p <;> rfl

private theorem match_option_same {α : Type} (x : Option α) (a : β) :
    (match x with | some _ => a | none => a) = a := by
  cases x <;> rfl

/-! Field-pushing through match — needed for cleanSig where path4/path5 are
    modified by genConnect and then re-matched in later steps. -/

private theorem AgentState_path4_match_pathInfo (p : PathInfo)
    (f : Nat → Nat → AgentState ψ) (g : AgentState ψ) :
    (match p with | .some l b => f l b | .bot => g).path4 =
    match p with | .some l b => (f l b).path4 | .bot => g.path4 := by
  cases p <;> rfl

private theorem AgentState_path5_match_pathInfo (p : PathInfo)
    (f : Nat → Nat → AgentState ψ) (g : AgentState ψ) :
    (match p with | .some l b => f l b | .bot => g).path5 =
    match p with | .some l b => (f l b).path5 | .bot => g.path5 := by
  cases p <;> rfl

private theorem AgentState_path_match_pathInfo (p : PathInfo)
    (f : Nat → Nat → AgentState ψ) (g : AgentState ψ) :
    (match p with | .some l b => f l b | .bot => g).path =
    match p with | .some l b => (f l b).path | .bot => g.path := by
  cases p <;> rfl

private theorem AgentState_state_match_pathInfo (p : PathInfo)
    (f : Nat → Nat → AgentState ψ) (g : AgentState ψ) :
    (match p with | .some l b => f l b | .bot => g).state =
    match p with | .some l b => (f l b).state | .bot => g.state := by
  cases p <;> rfl

private theorem AgentState_path4_match_option {α : Type} (x : Option α)
    (f : α → AgentState ψ) (g : AgentState ψ) :
    (match x with | some a => f a | none => g).path4 =
    match x with | some a => (f a).path4 | none => g.path4 := by
  cases x <;> rfl

private theorem AgentState_path5_match_option {α : Type} (x : Option α)
    (f : α → AgentState ψ) (g : AgentState ψ) :
    (match x with | some a => f a | none => g).path5 =
    match x with | some a => (f a).path5 | none => g.path5 := by
  cases x <;> rfl

private theorem AgentState_path_match_option {α : Type} (x : Option α)
    (f : α → AgentState ψ) (g : AgentState ψ) :
    (match x with | some a => f a | none => g).path =
    match x with | some a => (f a).path | none => g.path := by
  cases x <;> rfl

private theorem AgentState_state_match_option {α : Type} (x : Option α)
    (f : α → AgentState ψ) (g : AgentState ψ) :
    (match x with | some a => f a | none => g).state =
    match x with | some a => (f a).state | none => g.state := by
  cases x <;> rfl

private theorem AgentState_path3_match_option {α : Type} (x : Option α)
    (f : α → AgentState ψ) (g : AgentState ψ) :
    (match x with | some a => f a | none => g).path3 =
    match x with | some a => (f a).path3 | none => g.path3 := by
  cases x <;> rfl

private theorem AgentState_write_state_match_option {α : Type} (x : Option α)
    (f : α → AgentState ψ) (g : AgentState ψ) :
    (match x with | some a => f a | none => g).write_state =
    match x with | some a => (f a).write_state | none => g.write_state := by
  cases x <;> rfl

private theorem AgentState_path2_match_option {α : Type} (x : Option α)
    (f : α → AgentState ψ) (g : AgentState ψ) :
    (match x with | some a => f a | none => g).path2 =
    match x with | some a => (f a).path2 | none => g.path2 := by
  cases x <;> rfl

private theorem AgentState_path3_match_pathInfo (p : PathInfo)
    (f : Nat → Nat → AgentState ψ) (g : AgentState ψ) :
    (match p with | .some l b => f l b | .bot => g).path3 =
    match p with | .some l b => (f l b).path3 | .bot => g.path3 := by
  cases p <;> rfl

private theorem AgentState_write_state_match_pathInfo (p : PathInfo)
    (f : Nat → Nat → AgentState ψ) (g : AgentState ψ) :
    (match p with | .some l b => f l b | .bot => g).write_state =
    match p with | .some l b => (f l b).write_state | .bot => g.write_state := by
  cases p <;> rfl

private theorem AgentState_path2_match_pathInfo (p : PathInfo)
    (f : Nat → Nat → AgentState ψ) (g : AgentState ψ) :
    (match p with | .some l b => f l b | .bot => g).path2 =
    match p with | .some l b => (f l b).path2 | .bot => g.path2 := by
  cases p <;> rfl

end MatchSimp

/-! ## P'_ψ label stability -/

private theorem pPsi_l_label (l r : AgentState ψ) :
    (pPsi hψ l r).1.label = l.label := by
  unfold pPsi
  by_cases hb : r.label ≠ ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  · simp only [if_pos hb]
    split
    · split <;> rfl
    · rfl
  · simp only [if_neg hb]
    split <;> rfl

private theorem pPsi_r_label_of_non_barrier (l r : AgentState ψ)
    (h : ¬isBarrier hψ l r) :
    (pPsi hψ l r).2.label = r.label := by
  unfold pPsi
  have hb : ¬(r.label ≠ ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩) := by
    unfold isBarrier at h; exact h
  simp only [if_neg hb]
  split <;> rfl

private theorem pPsi_r_label_of_leader_zero_early (l r : AgentState ψ)
    (hleader : r.leader = true) (hlabel : r.label = ⟨0, hψ⟩) :
    (pPsi hψ l r).2.label = ⟨0, hψ⟩ := by
  unfold pPsi
  split <;> simp [hleader, hlabel]

private theorem pPsi_r_label_of_leader_no_probe (l r : AgentState ψ)
    (hl : r.leader = true) (hp : r.probe = false) :
    (pPsi hψ l r).2.label = r.label := by
  unfold pPsi
  have hnl : ¬(r.leader = false) := by rw [hl]; decide
  have hnp : ¬(r.probe = true) := by rw [hp]; decide
  simp only [if_neg hnp, if_neg hnl, Prod_fst_ite, Prod_snd_ite,
    AgentState_label_ite, AgentState_phase_ite, AgentState_probe_ite,
    AgentState_leader_ite, ite_same]

/-! ## Label stability for remaining sub-algorithms -/

/-! ### wait -/

private theorem wait_l_label (κ : Nat) (l r : AgentState ψ) :
    (wait hψ κ l r).1.label = l.label := by
  simp only [wait, Prod_fst_ite, Prod_snd_ite,
    AgentState_label_ite, AgentState_reset_ite, AgentState_h_field_ite,
    AgentState_carry_ite, AgentState_count_ite, AgentState_wait_ite, ite_same]

private theorem wait_r_label (κ : Nat) (l r : AgentState ψ) :
    (wait hψ κ l r).2.label = r.label := by
  simp only [wait, Prod_fst_ite, Prod_snd_ite,
    AgentState_label_ite, AgentState_reset_ite, AgentState_h_field_ite,
    AgentState_carry_ite, AgentState_count_ite, AgentState_wait_ite, ite_same]

/-! ### genSig (includes wait) -/

private theorem genSig_l_label (κ : Nat) (l r : AgentState ψ) :
    (genSig hψ κ l r).1.label = l.label := by
  simp only [genSig, wait, Prod_fst_ite, Prod_snd_ite, AgentState_label_ite, ite_same]

private theorem genSig_r_label (κ : Nat) (l r : AgentState ψ) :
    (genSig hψ κ l r).2.label = r.label := by
  simp only [genSig, wait, Prod_fst_ite, Prod_snd_ite, AgentState_label_ite, ite_same]

/-! ### suppressSig -/

private theorem suppressSig_l_label (l r : AgentState ψ) :
    (suppressSig hψ l r).1.label = l.label := by
  simp only [suppressSig, Prod_fst_ite, Prod_snd_ite,
    AgentState_label_ite, AgentState_leader_ite, AgentState_reset_cmd_ite,
    AgentState_echo_ite, ite_same]

private theorem suppressSig_r_label (l r : AgentState ψ) :
    (suppressSig hψ l r).2.label = r.label := by
  simp only [suppressSig, Prod_fst_ite, Prod_snd_ite,
    AgentState_label_ite, AgentState_leader_ite, AgentState_reset_cmd_ite,
    AgentState_echo_ite, AgentState_count_ite, ite_same]

/-! ### eliminateLeaders -/

private theorem eliminateLeaders_l_label (l r : AgentState ψ) :
    (eliminateLeaders hψ l r).1.label = l.label := by
  simp only [eliminateLeaders, Prod_fst_ite, Prod_snd_ite,
    AgentState_label_ite, AgentState_leader_ite, AgentState_signal_B_ite,
    AgentState_bullet_ite, AgentState_shield_ite, ite_same]

private theorem eliminateLeaders_r_label (l r : AgentState ψ) :
    (eliminateLeaders hψ l r).2.label = r.label := by
  simp only [eliminateLeaders, Prod_fst_ite, Prod_snd_ite,
    AgentState_label_ite, AgentState_leader_ite, AgentState_signal_B_ite,
    AgentState_bullet_ite, AgentState_shield_ite, ite_same]

/-! ### groupInfo -/

private theorem groupInfo_l_label (l r : AgentState ψ) :
    (groupInfo hψ l r).1.label = l.label := by
  simp only [groupInfo, Prod_fst_ite, Prod_snd_ite,
    AgentState_label_ite, AgentState_leader_ite, AgentState_last_set_ite,
    AgentState_last_ite, AgentState_last_set_ite, AgentState_last_unset_ite, ite_same]

private theorem groupInfo_r_label (l r : AgentState ψ) :
    (groupInfo hψ l r).2.label = r.label := by
  simp only [groupInfo, Prod_fst_ite, Prod_snd_ite,
    AgentState_label_ite, AgentState_leader_ite, AgentState_last_set_ite,
    AgentState_last_ite, AgentState_last_unset_ite, ite_same]

/-! ### eliminateSig -/

private theorem eliminateSig_l_label (l r : AgentState ψ) :
    (eliminateSig hψ l r).1.label = l.label := by
  simp only [eliminateSig, Prod_fst_ite, AgentState_label_ite, ite_same]

private theorem eliminateSig_r_label (l r : AgentState ψ) :
    (eliminateSig hψ l r).2.label = r.label := by
  simp only [eliminateSig, Prod_snd_ite, AgentState_label_ite, ite_same]

/-! ### disappear -/

private theorem disappear_l_label (l r : AgentState ψ) :
    (disappear hψ l r).1.label = l.label := by
  simp only [disappear, Prod_fst_ite, Prod_snd_ite, AgentState_label_ite, ite_same]

private theorem disappear_r_label (l r : AgentState ψ) :
    (disappear hψ l r).2.label = r.label := by
  simp only [disappear, Prod_fst_ite, Prod_snd_ite, AgentState_label_ite, ite_same]

/-! ### cleanSig -/

private theorem cleanSigGenConnect_label (u : AgentState ψ) :
    (cleanSigGenConnect u).label = u.label := by
  unfold cleanSigGenConnect; try dsimp only []
  repeat (first | rfl | split)

private theorem cleanSigCleanApply_label (u : AgentState ψ) :
    (cleanSigCleanApply u).label = u.label := by
  unfold cleanSigCleanApply; try dsimp only []
  repeat (first | rfl | split)

private theorem cleanSigStep3_l_label (l r : AgentState ψ) :
    (cleanSigStep3 l r).1.label = l.label := by
  unfold cleanSigStep3; try dsimp only []
  repeat (first | rfl | split)

private theorem cleanSigStep3_r_label (l r : AgentState ψ) :
    (cleanSigStep3 l r).2.label = r.label := by
  unfold cleanSigStep3; try dsimp only []
  repeat (first | rfl | split)

private theorem cleanSigStep4_l_label (l r : AgentState ψ) :
    (cleanSigStep4 l r).1.label = l.label := by
  unfold cleanSigStep4; try dsimp only []
  repeat (first | rfl | split)

private theorem cleanSigStep4_r_label (l r : AgentState ψ) :
    (cleanSigStep4 l r).2.label = r.label := by
  unfold cleanSigStep4; try dsimp only []
  repeat (first | rfl | split)

private theorem cleanSigStep5_l_label (l r : AgentState ψ) :
    (cleanSigStep5 hψ l r).1.label = l.label := by
  unfold cleanSigStep5; try dsimp only []
  repeat (first | rfl | split)

private theorem cleanSigStep5_r_label (l r : AgentState ψ) :
    (cleanSigStep5 hψ l r).2.label = r.label := by
  unfold cleanSigStep5; try dsimp only []
  repeat (first | rfl | split)

private theorem cleanSigStep6_l_label (l r : AgentState ψ) :
    (cleanSigStep6 hψ l r).1.label = l.label := by
  unfold cleanSigStep6; try dsimp only []
  repeat (first | rfl | split)

private theorem cleanSigStep6_r_label (l r : AgentState ψ) :
    (cleanSigStep6 hψ l r).2.label = r.label := by
  unfold cleanSigStep6; try dsimp only []
  repeat (first | rfl | split)

private theorem cleanSig_l_label (l r : AgentState ψ) :
    (cleanSig hψ l r).1.label = l.label := by
  simp only [cleanSig, cleanSigCleanApply_label, cleanSigStep6_l_label,
    cleanSigStep5_l_label, cleanSigStep4_l_label, cleanSigStep3_l_label,
    cleanSigGenConnect_label]

private theorem cleanSig_r_label (l r : AgentState ψ) :
    (cleanSig hψ l r).2.label = r.label := by
  simp only [cleanSig, cleanSigCleanApply_label, cleanSigStep6_r_label,
    cleanSigStep5_r_label, cleanSigStep4_r_label, cleanSigStep3_r_label,
    cleanSigGenConnect_label]

/-! ### sigMove -/

private theorem sigMoveStep1_l_label (l r : AgentState ψ) :
    (sigMoveStep1 l r).1.label = l.label := by
  unfold sigMoveStep1; try dsimp only []
  repeat (first | rfl | split)

private theorem sigMoveStep1_r_label (l r : AgentState ψ) :
    (sigMoveStep1 l r).2.label = r.label := by
  unfold sigMoveStep1; try dsimp only []
  repeat (first | rfl | split)

private theorem sigMoveApplyControl_label (u : AgentState ψ) :
    (sigMoveApplyControl hψ u).label = u.label := by
  unfold sigMoveApplyControl; try dsimp only []
  repeat (first | rfl | split)

private theorem sigMoveStep2_l_label (l r : AgentState ψ) :
    (sigMoveStep2 l r).1.label = l.label := by
  unfold sigMoveStep2; try dsimp only []
  repeat (first | rfl | split)

private theorem sigMoveStep2_r_label (l r : AgentState ψ) :
    (sigMoveStep2 l r).2.label = r.label := by
  unfold sigMoveStep2; try dsimp only []
  repeat (first | rfl | split)

private theorem sigMoveStep3_l_label (l r : AgentState ψ) :
    (sigMoveStep3 l r).1.label = l.label := by
  unfold sigMoveStep3; try dsimp only []
  repeat (first | rfl | split)

private theorem sigMoveStep3_r_label (l r : AgentState ψ) :
    (sigMoveStep3 l r).2.label = r.label := by
  unfold sigMoveStep3; try dsimp only []
  repeat (first | rfl | split)

private theorem sigMoveStep4_l_label (l r : AgentState ψ) :
    (sigMoveStep4 l r).1.label = l.label := by
  unfold sigMoveStep4; try dsimp only []
  repeat (first | rfl | split)

private theorem sigMoveStep4_r_label (l r : AgentState ψ) :
    (sigMoveStep4 l r).2.label = r.label := by
  unfold sigMoveStep4; try dsimp only []
  repeat (first | rfl | split)

private theorem sigMoveStep5_l_label (l r : AgentState ψ) :
    (sigMoveStep5 l r).1.label = l.label := by
  unfold sigMoveStep5; try dsimp only []
  repeat (first | rfl | split)

private theorem sigMoveStep5_r_label (l r : AgentState ψ) :
    (sigMoveStep5 l r).2.label = r.label := by
  unfold sigMoveStep5; try dsimp only []
  repeat (first | rfl | split)

private theorem sigMove_l_label (l r : AgentState ψ) :
    (sigMove hψ l r).1.label = l.label := by
  simp only [sigMove,
    sigMoveStep1_l_label, sigMoveStep2_l_label, sigMoveStep3_l_label,
    sigMoveStep4_l_label, sigMoveStep5_l_label,
    sigMoveApplyControl_label,
    AgentState_label_ite, ite_same]

private theorem sigMove_r_label (l r : AgentState ψ) :
    (sigMove hψ l r).2.label = r.label := by
  simp only [sigMove,
    sigMoveStep1_r_label, sigMoveStep2_r_label, sigMoveStep3_r_label,
    sigMoveStep4_r_label, sigMoveStep5_r_label,
    sigMoveApplyControl_label]

/-! ### checkSig -/

private theorem checkSigSetReady_label (u : AgentState ψ) :
    (checkSigSetReady u).label = u.label := by
  unfold checkSigSetReady; try dsimp only []
  repeat (first | rfl | split)

private theorem checkSigCheckL_label (u : AgentState ψ) :
    (checkSigCheckL hψ u).label = u.label := by
  unfold checkSigCheckL; try dsimp only []
  repeat (first | rfl | split)

private theorem checkSigCheckR_label (l r : AgentState ψ) :
    (checkSigCheckR hψ l r).label = r.label := by
  unfold checkSigCheckR; try dsimp only []
  repeat (first | rfl | split)

private theorem checkSigSetResult_label (u : AgentState ψ) :
    (checkSigSetResult u).label = u.label := by
  unfold checkSigSetResult; try dsimp only []
  repeat (first | rfl | split)

private theorem checkSig_l_label (l r : AgentState ψ) :
    (checkSig hψ l r).1.label = l.label := by
  simp only [checkSig,
    checkSigSetReady_label, checkSigCheckL_label, checkSigSetResult_label]

private theorem checkSig_r_label (l r : AgentState ψ) :
    (checkSig hψ l r).2.label = r.label := by
  simp only [checkSig,
    checkSigSetReady_label, checkSigCheckR_label, checkSigSetResult_label,
    AgentState_label_ite, ite_same]

/-! ### compareSig (includes cmpUpdate, compareBit) -/

private theorem compareBitUpdateL_label (l : AgentState ψ) :
    (compareBitUpdateL hψ l).label = l.label := by
  unfold compareBitUpdateL; try dsimp only []
  repeat (first | rfl | split)

private theorem compareBitUpdateR_label (r : AgentState ψ) :
    (compareBitUpdateR hψ r).label = r.label := by
  unfold compareBitUpdateR; try dsimp only []
  repeat (first | rfl | split)

private theorem compareBit_l_label (l r : AgentState ψ) :
    (compareBit hψ l r).1.label = l.label := by
  simp only [compareBit, compareBitUpdateL_label]

private theorem compareBit_r_label (l r : AgentState ψ) :
    (compareBit hψ l r).2.label = r.label := by
  simp only [compareBit, compareBitUpdateR_label]

private theorem cmpUpdatePropagate_l_label (l r : AgentState ψ) :
    (cmpUpdatePropagate hψ l r).1.label = l.label := by
  unfold cmpUpdatePropagate; try dsimp only []
  repeat (first | rfl | split)

private theorem cmpUpdatePropagate_r_label (l r : AgentState ψ) :
    (cmpUpdatePropagate hψ l r).2.label = r.label := by
  unfold cmpUpdatePropagate; try dsimp only []
  repeat (first | rfl | split)

private theorem cmpUpdateSetPath2_label (l : AgentState ψ) :
    (cmpUpdateSetPath2 hψ l).label = l.label := by
  unfold cmpUpdateSetPath2; try dsimp only []
  repeat (first | rfl | split)

private theorem cmpUpdate_l_label (l r : AgentState ψ) :
    (cmpUpdate hψ l r).1.label = l.label := by
  simp only [cmpUpdate,
    cmpUpdatePropagate_l_label, cmpUpdateSetPath2_label,
    AgentState_label_ite, ite_same]

private theorem cmpUpdate_r_label (l r : AgentState ψ) :
    (cmpUpdate hψ l r).2.label = r.label := by
  simp only [cmpUpdate,
    cmpUpdatePropagate_r_label]

private theorem compareSigInit_label (l : AgentState ψ) :
    (compareSigInit l).label = l.label := by
  unfold compareSigInit; try dsimp only []
  repeat (first | rfl | split)

private theorem compareSigInit_path (l : AgentState ψ) :
    (compareSigInit l).path = l.path := by
  unfold compareSigInit; split <;> rfl

private theorem compareSigDispatch_l_label (l r : AgentState ψ) :
    (compareSigDispatch hψ l r).1.label = l.label := by
  unfold compareSigDispatch
  repeat (first | exact compareBit_l_label hψ l r | rfl | split)

private theorem compareSigDispatch_r_label (l r : AgentState ψ) :
    (compareSigDispatch hψ l r).2.label = r.label := by
  unfold compareSigDispatch
  repeat (first | exact compareBit_r_label hψ l r | rfl | split)

private theorem compareSig_l_label (l r : AgentState ψ) :
    (compareSig hψ l r).1.label = l.label := by
  unfold compareSig; dsimp only []
  split
  · exact compareSigInit_label l
  · split
    · simp only [compareSigDispatch_l_label, cmpUpdate_l_label, compareSigInit_label]
    · exact compareSigInit_label l

private theorem compareSig_r_label (l r : AgentState ψ) :
    (compareSig hψ l r).2.label = r.label := by
  unfold compareSig; dsimp only []
  split
  · rfl
  · split
    · simp only [compareSigDispatch_r_label, cmpUpdate_r_label]
    · rfl

/-! ### writeAction -/

private theorem writeActionApplyOverwrite_label (r : AgentState ψ) :
    (writeActionApplyOverwrite r).label = r.label := by
  unfold writeActionApplyOverwrite; cases r.path3 <;> rfl

private theorem writeActionApplyMoveFlip_label (r : AgentState ψ) :
    (writeActionApplyMoveFlip r).label = r.label := by
  unfold writeActionApplyMoveFlip; cases r.path3 <;> rfl

/-- Algorithm 19 frames the initiator label. -/
theorem writeAction_l_label (l r : AgentState ψ) :
    (writeAction hψ l r).1.label = l.label := by
  unfold writeAction writeActionToState
  simp only [Prod_fst_ite, AgentState_label_ite, ite_same]

/-- Algorithm 19 frames the responder label. -/
theorem writeAction_r_label (l r : AgentState ψ) :
    (writeAction hψ l r).2.label = r.label := by
  unfold writeAction writeActionToState
  simp only [writeActionApplyOverwrite_label, writeActionApplyMoveFlip_label,
    Prod_snd_ite, AgentState_label_ite, ite_same]

/-! ### moveWsig (includes moveWsigTransfer) -/

private theorem moveWsigTransfer_l_label (l r : AgentState ψ) :
    (moveWsigTransfer l r).1.label = l.label := by
  unfold moveWsigTransfer; try dsimp only []
  repeat (first | rfl | split)

private theorem moveWsigTransfer_r_label (l r : AgentState ψ) :
    (moveWsigTransfer l r).2.label = r.label := by
  unfold moveWsigTransfer; try dsimp only []
  repeat (first | rfl | split)

private theorem moveWsigCheckGenWs_label (l r : AgentState ψ) :
    (moveWsigCheckGenWs l r).label = r.label := by
  unfold moveWsigCheckGenWs; repeat (first | rfl | split)

private theorem moveWsigCheckLast_label (l : AgentState ψ) :
    (moveWsigCheckLast l).label = l.label := by
  unfold moveWsigCheckLast; repeat (first | rfl | split)

/-- Algorithm 20 frames the initiator label. -/
theorem moveWsig_l_label (l r : AgentState ψ) :
    (moveWsig hψ l r).1.label = l.label := by
  unfold moveWsig
  simp only [moveWsigCheckGenWs_label, moveWsigCheckLast_label,
    moveWsigTransfer_l_label, moveWsigTransfer_r_label,
    Prod_fst_ite, Prod_snd_ite, AgentState_label_ite, ite_same]

/-- Algorithm 20 frames the responder label. -/
theorem moveWsig_r_label (l r : AgentState ψ) :
    (moveWsig hψ l r).2.label = r.label := by
  unfold moveWsig
  simp only [moveWsigCheckGenWs_label, moveWsigCheckLast_label,
    moveWsigTransfer_l_label, moveWsigTransfer_r_label,
    Prod_fst_ite, Prod_snd_ite, AgentState_label_ite, ite_same]

/-! ### gensigWriteseq -/

private theorem gensigWriteseq_l_label (l r : AgentState ψ) :
    (gensigWriteseq hψ l r).1.label = l.label := by
  simp only [gensigWriteseq, Prod_fst_ite, Prod_snd_ite, AgentState_label_ite, ite_same]

private theorem gensigWriteseq_r_label (l r : AgentState ψ) :
    (gensigWriteseq hψ l r).2.label = r.label := by
  simp only [gensigWriteseq, Prod_fst_ite, Prod_snd_ite, AgentState_label_ite, ite_same]

/-! ### writeSeq (composition) -/

private theorem writeSeqSetWriteReady_label (u : AgentState ψ) :
    (writeSeqSetWriteReady u).label = u.label := by
  unfold writeSeqSetWriteReady; repeat (first | rfl | split)

private theorem writeSeqCheckBit_label (r : AgentState ψ) :
    (writeSeqCheckBit r).label = r.label := by
  unfold writeSeqCheckBit; cases r.path3 <;> rfl

private theorem writeSeqSetWriteAct_label (u : AgentState ψ) :
    (writeSeqSetWriteAct u).label = u.label := by
  unfold writeSeqSetWriteAct; dsimp only []
  repeat (first | rfl | split)

private theorem writeSeqFinalR_label (r : AgentState ψ) :
    (writeSeqFinalR r).label = r.label := by
  unfold writeSeqFinalR; repeat (first | rfl | split)

/-- The complete WRITE sequence frames the initiator label. -/
theorem writeSeq_l_label (l r : AgentState ψ) :
    (writeSeq hψ l r).1.label = l.label := by
  unfold writeSeq writeSeqThroughPrepare writeSeqAfterPrepare
    writeSeqLeaderMove writeSeqGenerate writeSeqPrepare
    writeSeqReady writeSeqCompare writeSeqCommands
  simp only [writeSeqSetWriteReady_label, writeSeqCheckBit_label,
    writeSeqSetWriteAct_label,
    moveWsig_l_label,
    writeAction_l_label,
    gensigWriteseq_l_label, gensigWriteseq_r_label,
    groupInfo_l_label, groupInfo_r_label,
    Prod_fst_ite, Prod_snd_ite, AgentState_label_ite, ite_same]

/-- The complete WRITE sequence frames the responder label. -/
theorem writeSeq_r_label (l r : AgentState ψ) :
    (writeSeq hψ l r).2.label = r.label := by
  unfold writeSeq writeSeqThroughPrepare writeSeqAfterPrepare
    writeSeqLeaderMove writeSeqGenerate writeSeqPrepare
    writeSeqReady writeSeqCompare writeSeqCommands
  simp only [writeSeqSetWriteReady_label, writeSeqCheckBit_label,
    writeSeqSetWriteAct_label, writeSeqFinalR_label,
    moveWsig_r_label,
    writeAction_r_label,
    gensigWriteseq_l_label, gensigWriteseq_r_label,
    groupInfo_l_label, groupInfo_r_label,
    Prod_fst_ite, Prod_snd_ite, AgentState_label_ite, ite_same]

/-! ## ppll label stability and no_new_barrier -/

private theorem ppll_l_label (κ : Nat) (l r : AgentState ψ) :
    (ppll hψ κ l r).1.label = l.label := by
  unfold ppll ppllBeforeWriteSeq ppllBeforeEliminateLeaders ppllAfterCheck ppllBeforeCheck
  simp only [writeSeq_l_label, eliminateLeaders_l_label, suppressSig_l_label,
    compareSig_l_label, disappear_l_label, checkSig_l_label, sigMove_l_label,
    eliminateSig_l_label, cleanSig_l_label, genSig_l_label, pPsi_l_label]

private theorem ppll_r_label_of_non_barrier (κ : Nat) (l r : AgentState ψ)
    (h : ¬isBarrier hψ l r) :
    (ppll hψ κ l r).2.label = r.label := by
  unfold ppll ppllBeforeWriteSeq ppllBeforeEliminateLeaders ppllAfterCheck ppllBeforeCheck
  simp only [writeSeq_r_label, eliminateLeaders_r_label, suppressSig_r_label,
    compareSig_r_label, disappear_r_label, checkSig_r_label, sigMove_r_label,
    eliminateSig_r_label, cleanSig_r_label, genSig_r_label]
  exact pPsi_r_label_of_non_barrier hψ l r h

/-- The initiator label is invariant through the complete concrete transition. -/
theorem ppll_initiator_label_stable (κ : Nat) (l r : AgentState ψ) :
    (ppll hψ κ l r).1.label = l.label :=
  ppll_l_label hψ κ l r

/-- A non-barrier responder keeps its label through the complete transition. -/
theorem ppll_responder_label_stable_of_nonbarrier (κ : Nat)
    (l r : AgentState ψ) (h : ¬isBarrier hψ l r) :
    (ppll hψ κ l r).2.label = r.label :=
  ppll_r_label_of_non_barrier hψ κ l r h

/-- A responder leader already at label zero also keeps its label, including on
its blocked barrier edge. -/
theorem ppll_responder_label_stable_of_leader_zero (κ : Nat)
    (l r : AgentState ψ) (hr : r.leader = true)
    (hlabel : r.label = ⟨0, hψ⟩) :
    (ppll hψ κ l r).2.label = r.label := by
  simp only [ppll, ppllBeforeWriteSeq, ppllBeforeEliminateLeaders,
    ppllAfterCheck, ppllBeforeCheck,
    pPsi_r_label_of_leader_zero_early hψ l r hr hlabel,
    genSig_r_label, cleanSig_r_label, eliminateSig_r_label,
    sigMove_r_label, checkSig_r_label, disappear_r_label,
    compareSig_r_label, suppressSig_r_label, eliminateLeaders_r_label,
    writeSeq_r_label]
  exact hlabel.symm

private theorem isBarrier_iff_of_labels {l l' r r' : AgentState ψ}
    (hl : l'.label = l.label) (hr : r'.label = r.label) :
    isBarrier hψ l' r' ↔ isBarrier hψ l r := by
  simp only [isBarrier, hl, hr]

theorem ppll_no_new_barrier (κ : Nat) (l r : AgentState ψ)
    (h : ¬isBarrier hψ l r) :
    ¬isBarrier hψ (ppll hψ κ l r).1 (ppll hψ κ l r).2 :=
  fun hb => h ((isBarrier_iff_of_labels hψ (ppll_l_label hψ κ l r)
    (ppll_r_label_of_non_barrier hψ κ l r h)).mp hb)

/-! ## Leader field stability proofs -/

/-! ### Single-agent step leader stability -/

private theorem cleanSigGenConnect_leader (u : AgentState ψ) :
    (cleanSigGenConnect u).leader = u.leader := by
  unfold cleanSigGenConnect; try dsimp only []
  repeat (first | rfl | split)

private theorem cleanSigCleanApply_leader (u : AgentState ψ) :
    (cleanSigCleanApply u).leader = u.leader := by
  unfold cleanSigCleanApply; try dsimp only []
  repeat (first | rfl | split)

private theorem checkSigSetReady_leader (u : AgentState ψ) :
    (checkSigSetReady u).leader = u.leader := by
  unfold checkSigSetReady; try dsimp only []
  repeat (first | rfl | split)

private theorem checkSigCheckL_leader (u : AgentState ψ) :
    (checkSigCheckL hψ u).leader = u.leader := by
  unfold checkSigCheckL; try dsimp only []
  repeat (first | rfl | split)

private theorem checkSigCheckR_leader (l r : AgentState ψ) :
    (checkSigCheckR hψ l r).leader = r.leader := by
  unfold checkSigCheckR; try dsimp only []
  repeat (first | rfl | split)

private theorem checkSigSetResult_leader (u : AgentState ψ) :
    (checkSigSetResult u).leader = u.leader := by
  unfold checkSigSetResult; try dsimp only []
  repeat (first | rfl | split)

private theorem compareBitUpdateL_leader (l : AgentState ψ) :
    (compareBitUpdateL hψ l).leader = l.leader := by
  unfold compareBitUpdateL; try dsimp only []
  repeat (first | rfl | split)

private theorem compareBitUpdateR_leader (r : AgentState ψ) :
    (compareBitUpdateR hψ r).leader = r.leader := by
  unfold compareBitUpdateR; try dsimp only []
  repeat (first | rfl | split)

private theorem cmpUpdatePropagate_l_leader (l r : AgentState ψ) :
    (cmpUpdatePropagate hψ l r).1.leader = l.leader := by
  unfold cmpUpdatePropagate; try dsimp only []
  repeat (first | rfl | split)

private theorem cmpUpdatePropagate_r_leader (l r : AgentState ψ) :
    (cmpUpdatePropagate hψ l r).2.leader = r.leader := by
  unfold cmpUpdatePropagate; try dsimp only []
  repeat (first | rfl | split)

private theorem cmpUpdateSetPath2_leader (l : AgentState ψ) :
    (cmpUpdateSetPath2 hψ l).leader = l.leader := by
  unfold cmpUpdateSetPath2; try dsimp only []
  repeat (first | rfl | split)

private theorem sigMoveApplyControl_leader (u : AgentState ψ) :
    (sigMoveApplyControl hψ u).leader = u.leader := by
  unfold sigMoveApplyControl; try dsimp only []
  repeat (first | rfl | split)

private theorem compareSigInit_leader (l : AgentState ψ) :
    (compareSigInit l).leader = l.leader := by
  unfold compareSigInit; split <;> rfl

private theorem writeActionApplyOverwrite_leader (r : AgentState ψ) :
    (writeActionApplyOverwrite r).leader = r.leader := by
  unfold writeActionApplyOverwrite; cases r.path3 <;> rfl

private theorem writeActionApplyMoveFlip_leader (r : AgentState ψ) :
    (writeActionApplyMoveFlip r).leader = r.leader := by
  unfold writeActionApplyMoveFlip; cases r.path3 <;> rfl

private theorem moveWsigCheckGenWs_leader (l r : AgentState ψ) :
    (moveWsigCheckGenWs l r).leader = r.leader := by
  unfold moveWsigCheckGenWs; repeat (first | rfl | split)

private theorem moveWsigCheckLast_leader (l : AgentState ψ) :
    (moveWsigCheckLast l).leader = l.leader := by
  unfold moveWsigCheckLast; repeat (first | rfl | split)

private theorem writeSeqSetWriteReady_leader (u : AgentState ψ) :
    (writeSeqSetWriteReady u).leader = u.leader := by
  unfold writeSeqSetWriteReady; repeat (first | rfl | split)

private theorem writeSeqCheckBit_leader (r : AgentState ψ) :
    (writeSeqCheckBit r).leader = r.leader := by
  unfold writeSeqCheckBit; cases r.path3 <;> rfl

private theorem writeSeqSetWriteAct_leader (u : AgentState ψ) :
    (writeSeqSetWriteAct u).leader = u.leader := by
  unfold writeSeqSetWriteAct; dsimp only []
  repeat (first | rfl | split)

private theorem writeSeqFinalR_leader (r : AgentState ψ) :
    (writeSeqFinalR r).leader = r.leader := by
  unfold writeSeqFinalR; repeat (first | rfl | split)

/-! ### Pair step leader stability -/

private theorem cleanSigStep3_r_leader (l r : AgentState ψ) :
    (cleanSigStep3 l r).2.leader = r.leader := by
  unfold cleanSigStep3; try dsimp only []
  repeat (first | rfl | split)

private theorem cleanSigStep4_r_leader (l r : AgentState ψ) :
    (cleanSigStep4 l r).2.leader = r.leader := by
  unfold cleanSigStep4; try dsimp only []
  repeat (first | rfl | split)

private theorem cleanSigStep5_r_leader (l r : AgentState ψ) :
    (cleanSigStep5 hψ l r).2.leader = r.leader := by
  unfold cleanSigStep5; try dsimp only []
  repeat (first | rfl | split)

private theorem cleanSigStep6_r_leader (l r : AgentState ψ) :
    (cleanSigStep6 hψ l r).2.leader = r.leader := by
  unfold cleanSigStep6; try dsimp only []
  repeat (first | rfl | split)

private theorem sigMoveStep1_r_leader (l r : AgentState ψ) :
    (sigMoveStep1 l r).2.leader = r.leader := by
  unfold sigMoveStep1; try dsimp only []
  repeat (first | rfl | split)

private theorem sigMoveStep2_r_leader (l r : AgentState ψ) :
    (sigMoveStep2 l r).2.leader = r.leader := by
  unfold sigMoveStep2; try dsimp only []
  repeat (first | rfl | split)

private theorem sigMoveStep3_r_leader (l r : AgentState ψ) :
    (sigMoveStep3 l r).2.leader = r.leader := by
  unfold sigMoveStep3; try dsimp only []
  repeat (first | rfl | split)

private theorem sigMoveStep4_r_leader (l r : AgentState ψ) :
    (sigMoveStep4 l r).2.leader = r.leader := by
  unfold sigMoveStep4; try dsimp only []
  repeat (first | rfl | split)

private theorem sigMoveStep5_r_leader (l r : AgentState ψ) :
    (sigMoveStep5 l r).2.leader = r.leader := by
  unfold sigMoveStep5; try dsimp only []
  repeat (first | rfl | split)

private theorem moveWsigTransfer_l_leader (l r : AgentState ψ) :
    (moveWsigTransfer l r).1.leader = l.leader := by
  unfold moveWsigTransfer; try dsimp only []
  repeat (first | rfl | split)

private theorem moveWsigTransfer_r_leader (l r : AgentState ψ) :
    (moveWsigTransfer l r).2.leader = r.leader := by
  unfold moveWsigTransfer; try dsimp only []
  repeat (first | rfl | split)

/-! ### Composition leader stability -/

private theorem cleanSig_r_leader (l r : AgentState ψ) :
    (cleanSig hψ l r).2.leader = r.leader := by
  simp only [cleanSig, cleanSigCleanApply_leader, cleanSigStep6_r_leader,
    cleanSigStep5_r_leader, cleanSigStep4_r_leader, cleanSigStep3_r_leader,
    cleanSigGenConnect_leader]

private theorem compareBit_r_leader (l r : AgentState ψ) :
    (compareBit hψ l r).2.leader = r.leader := by
  simp only [compareBit, compareBitUpdateR_leader]

private theorem cmpUpdate_r_leader (l r : AgentState ψ) :
    (cmpUpdate hψ l r).2.leader = r.leader := by
  simp only [cmpUpdate, cmpUpdatePropagate_r_leader]

private theorem compareSigDispatch_r_leader (l r : AgentState ψ) :
    (compareSigDispatch hψ l r).2.leader = r.leader := by
  unfold compareSigDispatch
  repeat (first | exact compareBit_r_leader hψ l r | rfl | split)

private theorem compareSig_r_leader (l r : AgentState ψ) :
    (compareSig hψ l r).2.leader = r.leader := by
  unfold compareSig; dsimp only []
  split
  · rfl
  · split
    · simp only [compareSigDispatch_r_leader, cmpUpdate_r_leader]
    · rfl

private theorem sigMove_r_leader (l r : AgentState ψ) :
    (sigMove hψ l r).2.leader = r.leader := by
  simp only [sigMove,
    sigMoveStep1_r_leader, sigMoveStep2_r_leader, sigMoveStep3_r_leader,
    sigMoveStep4_r_leader, sigMoveStep5_r_leader,
    sigMoveApplyControl_leader]

private theorem writeAction_r_leader (l r : AgentState ψ) :
    (writeAction hψ l r).2.leader = r.leader := by
  unfold writeAction writeActionToState
  simp only [writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader,
    Prod_snd_ite, AgentState_leader_ite, ite_same]

private theorem moveWsig_r_leader (l r : AgentState ψ) :
    (moveWsig hψ l r).2.leader = r.leader := by
  unfold moveWsig
  simp only [moveWsigCheckGenWs_leader, moveWsigCheckLast_leader,
    moveWsigTransfer_l_leader, moveWsigTransfer_r_leader,
    Prod_fst_ite, Prod_snd_ite, AgentState_leader_ite, ite_same]

private theorem genSig_r_leader (κ : Nat) (l r : AgentState ψ) :
    (genSig hψ κ l r).2.leader = r.leader := by
  simp only [genSig, wait, Prod_fst_ite, Prod_snd_ite, AgentState_leader_ite, ite_same]

private theorem eliminateSig_r_leader (l r : AgentState ψ) :
    (eliminateSig hψ l r).2.leader = r.leader := by
  simp only [eliminateSig, Prod_snd_ite, AgentState_leader_ite, ite_same]

private theorem disappear_r_leader (l r : AgentState ψ) :
    (disappear hψ l r).2.leader = r.leader := by
  simp only [disappear, Prod_fst_ite, Prod_snd_ite, AgentState_leader_ite, ite_same]

private theorem suppressSig_r_leader (l r : AgentState ψ) :
    (suppressSig hψ l r).2.leader = r.leader := by
  simp only [suppressSig, Prod_fst_ite, Prod_snd_ite,
    AgentState_leader_ite, AgentState_reset_cmd_ite,
    AgentState_echo_ite, AgentState_count_ite, ite_same]

private theorem eliminateLeaders_r_leader (l r : AgentState ψ) :
    (eliminateLeaders hψ l r).2.leader = r.leader := by
  simp only [eliminateLeaders, Prod_fst_ite, Prod_snd_ite,
    AgentState_leader_ite, AgentState_signal_B_ite,
    AgentState_bullet_ite, AgentState_shield_ite, ite_same]

private theorem groupInfo_r_leader (l r : AgentState ψ) :
    (groupInfo hψ l r).2.leader = r.leader := by
  simp only [groupInfo, Prod_fst_ite, Prod_snd_ite,
    AgentState_leader_ite, AgentState_last_set_ite,
    AgentState_last_ite, AgentState_last_unset_ite, ite_same]

private theorem gensigWriteseq_r_leader (l r : AgentState ψ) :
    (gensigWriteseq hψ l r).2.leader = r.leader := by
  simp only [gensigWriteseq, Prod_fst_ite, Prod_snd_ite, AgentState_leader_ite, ite_same]

/-! ### Conditional leader stability -/

private theorem checkSig_r_leader_of_true (l r : AgentState ψ)
    (h : r.leader = true) :
    (checkSig hψ l r).2.leader = true := by
  simp only [checkSig,
    checkSigSetReady_leader, checkSigCheckR_leader, checkSigSetResult_leader,
    AgentState_leader_ite, h, ite_same]

private theorem pPsi_r_leader_of_leader (l r : AgentState ψ)
    (h : r.leader = true) :
    (pPsi hψ l r).2.leader = true := by
  unfold pPsi
  split <;> simp [h]

private theorem pPsi_r_label_of_leader_zero (l r : AgentState ψ)
    (hleader : r.leader = true) (hlabel : r.label = ⟨0, hψ⟩) :
    (pPsi hψ l r).2.label = ⟨0, hψ⟩ := by
  unfold pPsi
  split <;> simp [hleader, hlabel]

private theorem writeSeq_r_leader_of_label_zero (l r : AgentState ψ)
    (hl : r.label = ⟨0, hψ⟩) :
    (writeSeq hψ l r).2.leader = r.leader := by
  have hneg : ¬(r.leader = true ∧ r.label ≠ ⟨0, hψ⟩) := by
    intro ⟨_, hne⟩; exact hne hl
  simp only [writeSeq, writeSeqThroughPrepare, writeSeqAfterPrepare,
    writeSeqLeaderMove, writeSeqGenerate, writeSeqPrepare, writeSeqReady,
    writeSeqCompare, writeSeqCommands, if_neg hneg,
    writeSeqSetWriteReady_leader, writeSeqCheckBit_leader,
    writeSeqSetWriteAct_leader, writeSeqFinalR_leader,
    moveWsig_r_leader, writeAction_r_leader,
    gensigWriteseq_r_leader, groupInfo_r_leader,
    Prod_fst_ite, Prod_snd_ite, AgentState_leader_ite, ite_same]

/-! ## ProtocolProperties axiom: leader_responder_stable -/

theorem ppll_leader_responder_stable (κ : Nat) (l r : AgentState ψ)
    (hleader : r.leader = true) (hlabel : r.label = ⟨0, hψ⟩) :
    (ppll hψ κ l r).2.leader = true := by
  simp only [ppll, ppllBeforeWriteSeq, ppllBeforeEliminateLeaders,
    ppllAfterCheck, ppllBeforeCheck, pPsi_r_leader_of_leader hψ l r hleader,
    pPsi_r_label_of_leader_zero hψ l r hleader hlabel,
    genSig_r_leader, genSig_r_label,
    cleanSig_r_leader, cleanSig_r_label,
    eliminateSig_r_leader, eliminateSig_r_label,
    sigMove_r_leader, sigMove_r_label,
    checkSig_r_leader_of_true, checkSig_r_label,
    disappear_r_leader, disappear_r_label,
    compareSig_r_leader, compareSig_r_label,
    suppressSig_r_leader, suppressSig_r_label,
    eliminateLeaders_r_leader, eliminateLeaders_r_label,
    writeSeq_r_leader_of_label_zero]

/-! ## Leader initiator stability: l.leader through ppll -/

/-! ### l.leader pair step lemmas -/

private theorem cleanSigStep3_l_leader (l r : AgentState ψ) :
    (cleanSigStep3 l r).1.leader = l.leader := by
  unfold cleanSigStep3; try dsimp only []
  repeat (first | rfl | split)

private theorem cleanSigStep4_l_leader (l r : AgentState ψ) :
    (cleanSigStep4 l r).1.leader = l.leader := by
  unfold cleanSigStep4; try dsimp only []
  repeat (first | rfl | split)

private theorem cleanSigStep5_l_leader (l r : AgentState ψ) :
    (cleanSigStep5 hψ l r).1.leader = l.leader := by
  unfold cleanSigStep5; try dsimp only []
  repeat (first | rfl | split)

private theorem cleanSigStep6_l_leader (l r : AgentState ψ) :
    (cleanSigStep6 hψ l r).1.leader = l.leader := by
  unfold cleanSigStep6; try dsimp only []
  repeat (first | rfl | split)

private theorem sigMoveStep1_l_leader (l r : AgentState ψ) :
    (sigMoveStep1 l r).1.leader = l.leader := by
  unfold sigMoveStep1; try dsimp only []
  repeat (first | rfl | split)

private theorem sigMoveStep2_l_leader (l r : AgentState ψ) :
    (sigMoveStep2 l r).1.leader = l.leader := by
  unfold sigMoveStep2; try dsimp only []
  repeat (first | rfl | split)

private theorem sigMoveStep3_l_leader (l r : AgentState ψ) :
    (sigMoveStep3 l r).1.leader = l.leader := by
  unfold sigMoveStep3; try dsimp only []
  repeat (first | rfl | split)

private theorem sigMoveStep4_l_leader (l r : AgentState ψ) :
    (sigMoveStep4 l r).1.leader = l.leader := by
  unfold sigMoveStep4; try dsimp only []
  repeat (first | rfl | split)

private theorem sigMoveStep5_l_leader (l r : AgentState ψ) :
    (sigMoveStep5 l r).1.leader = l.leader := by
  unfold sigMoveStep5; try dsimp only []
  repeat (first | rfl | split)

/-! ### l.leader composition lemmas (pPsi through suppressSig) -/

private theorem pPsi_l_leader (l r : AgentState ψ) :
    (pPsi hψ l r).1.leader = l.leader := by
  unfold pPsi; try dsimp only []
  repeat (first | rfl | split)

private theorem genSig_l_leader (κ : Nat) (l r : AgentState ψ) :
    (genSig hψ κ l r).1.leader = l.leader := by
  simp only [genSig, wait, Prod_fst_ite, Prod_snd_ite, AgentState_leader_ite, ite_same]

private theorem cleanSig_l_leader (l r : AgentState ψ) :
    (cleanSig hψ l r).1.leader = l.leader := by
  simp only [cleanSig, cleanSigCleanApply_leader, cleanSigGenConnect_leader,
    cleanSigStep3_l_leader, cleanSigStep4_l_leader,
    cleanSigStep5_l_leader, cleanSigStep6_l_leader]

private theorem eliminateSig_l_leader (l r : AgentState ψ) :
    (eliminateSig hψ l r).1.leader = l.leader := by
  simp only [eliminateSig, Prod_fst_ite, AgentState_leader_ite, ite_same]

private theorem sigMove_l_leader (l r : AgentState ψ) :
    (sigMove hψ l r).1.leader = l.leader := by
  simp only [sigMove,
    sigMoveStep1_l_leader, sigMoveStep2_l_leader, sigMoveStep3_l_leader,
    sigMoveStep4_l_leader, sigMoveStep5_l_leader,
    sigMoveApplyControl_leader,
    Prod_fst_ite, Prod_snd_ite, AgentState_leader_ite, ite_same]

private theorem checkSig_l_leader (l r : AgentState ψ) :
    (checkSig hψ l r).1.leader = l.leader := by
  simp only [checkSig, checkSigSetReady_leader, checkSigCheckL_leader,
    checkSigSetResult_leader]

private theorem disappear_l_leader (l r : AgentState ψ) :
    (disappear hψ l r).1.leader = l.leader := by
  simp only [disappear, Prod_fst_ite, Prod_snd_ite, AgentState_leader_ite, ite_same]

private theorem compareBit_l_leader (l r : AgentState ψ) :
    (compareBit hψ l r).1.leader = l.leader := by
  simp only [compareBit, compareBitUpdateL_leader]

private theorem cmpUpdate_l_leader (l r : AgentState ψ) :
    (cmpUpdate hψ l r).1.leader = l.leader := by
  simp only [cmpUpdate, cmpUpdatePropagate_l_leader, cmpUpdateSetPath2_leader,
    AgentState_leader_ite, ite_same]

private theorem compareSigDispatch_l_leader (l r : AgentState ψ) :
    (compareSigDispatch hψ l r).1.leader = l.leader := by
  unfold compareSigDispatch
  repeat (first | exact compareBit_l_leader hψ l r | rfl | split)

private theorem compareSig_l_leader (l r : AgentState ψ) :
    (compareSig hψ l r).1.leader = l.leader := by
  unfold compareSig; dsimp only []
  split
  · exact compareSigInit_leader l
  · split
    · simp only [compareSigDispatch_l_leader, cmpUpdate_l_leader, compareSigInit_leader]
    · exact compareSigInit_leader l

private theorem suppressSig_l_leader (l r : AgentState ψ) :
    (suppressSig hψ l r).1.leader = l.leader := by
  simp only [suppressSig, Prod_fst_ite, Prod_snd_ite,
    AgentState_leader_ite, AgentState_reset_cmd_ite,
    AgentState_echo_ite, AgentState_count_ite, ite_same]

/-! ### l.shield stability through pPsi..suppressSig -/

/-! Single-agent shield step lemmas -/

private theorem cleanSigGenConnect_shield (u : AgentState ψ) :
    (cleanSigGenConnect u).shield = u.shield := by
  unfold cleanSigGenConnect; try dsimp only []
  repeat (first | rfl | split)

private theorem cleanSigCleanApply_shield (u : AgentState ψ) :
    (cleanSigCleanApply u).shield = u.shield := by
  unfold cleanSigCleanApply; try dsimp only []
  repeat (first | rfl | split)

private theorem checkSigSetReady_shield (u : AgentState ψ) :
    (checkSigSetReady u).shield = u.shield := by
  unfold checkSigSetReady; try dsimp only []
  repeat (first | rfl | split)

private theorem checkSigCheckL_shield (u : AgentState ψ) :
    (checkSigCheckL hψ u).shield = u.shield := by
  unfold checkSigCheckL; try dsimp only []
  repeat (first | rfl | split)

private theorem checkSigCheckR_shield (l r : AgentState ψ) :
    (checkSigCheckR hψ l r).shield = r.shield := by
  unfold checkSigCheckR; try dsimp only []
  repeat (first | rfl | split)

private theorem checkSigSetResult_shield (u : AgentState ψ) :
    (checkSigSetResult u).shield = u.shield := by
  unfold checkSigSetResult; try dsimp only []
  repeat (first | rfl | split)

private theorem compareBitUpdateL_shield (l : AgentState ψ) :
    (compareBitUpdateL hψ l).shield = l.shield := by
  unfold compareBitUpdateL; try dsimp only []
  repeat (first | rfl | split)

private theorem cmpUpdateSetPath2_shield (l : AgentState ψ) :
    (cmpUpdateSetPath2 hψ l).shield = l.shield := by
  unfold cmpUpdateSetPath2; try dsimp only []
  repeat (first | rfl | split)

private theorem sigMoveApplyControl_shield (u : AgentState ψ) :
    (sigMoveApplyControl hψ u).shield = u.shield := by
  unfold sigMoveApplyControl; try dsimp only []
  repeat (first | rfl | split)

private theorem compareSigInit_shield (l : AgentState ψ) :
    (compareSigInit l).shield = l.shield := by
  unfold compareSigInit; split <;> rfl

/-! Pair shield step lemmas -/

private theorem cleanSigStep3_l_shield (l r : AgentState ψ) :
    (cleanSigStep3 l r).1.shield = l.shield := by
  unfold cleanSigStep3; try dsimp only []
  repeat (first | rfl | split)

private theorem cleanSigStep4_l_shield (l r : AgentState ψ) :
    (cleanSigStep4 l r).1.shield = l.shield := by
  unfold cleanSigStep4; try dsimp only []
  repeat (first | rfl | split)

private theorem cleanSigStep5_l_shield (l r : AgentState ψ) :
    (cleanSigStep5 hψ l r).1.shield = l.shield := by
  unfold cleanSigStep5; try dsimp only []
  repeat (first | rfl | split)

private theorem cleanSigStep6_l_shield (l r : AgentState ψ) :
    (cleanSigStep6 hψ l r).1.shield = l.shield := by
  unfold cleanSigStep6; try dsimp only []
  repeat (first | rfl | split)

private theorem sigMoveStep1_l_shield (l r : AgentState ψ) :
    (sigMoveStep1 l r).1.shield = l.shield := by
  unfold sigMoveStep1; try dsimp only []
  repeat (first | rfl | split)

private theorem sigMoveStep2_l_shield (l r : AgentState ψ) :
    (sigMoveStep2 l r).1.shield = l.shield := by
  unfold sigMoveStep2; try dsimp only []
  repeat (first | rfl | split)

private theorem sigMoveStep3_l_shield (l r : AgentState ψ) :
    (sigMoveStep3 l r).1.shield = l.shield := by
  unfold sigMoveStep3; try dsimp only []
  repeat (first | rfl | split)

private theorem sigMoveStep4_l_shield (l r : AgentState ψ) :
    (sigMoveStep4 l r).1.shield = l.shield := by
  unfold sigMoveStep4; try dsimp only []
  repeat (first | rfl | split)

private theorem sigMoveStep5_l_shield (l r : AgentState ψ) :
    (sigMoveStep5 l r).1.shield = l.shield := by
  unfold sigMoveStep5; try dsimp only []
  repeat (first | rfl | split)

private theorem cmpUpdatePropagate_l_shield (l r : AgentState ψ) :
    (cmpUpdatePropagate hψ l r).1.shield = l.shield := by
  unfold cmpUpdatePropagate; try dsimp only []
  repeat (first | rfl | split)

private theorem moveWsigTransfer_l_shield (l r : AgentState ψ) :
    (moveWsigTransfer l r).1.shield = l.shield := by
  unfold moveWsigTransfer; try dsimp only []
  repeat (first | rfl | split)

/-! Shield composition lemmas -/

private theorem pPsi_l_shield (l r : AgentState ψ) :
    (pPsi hψ l r).1.shield = l.shield := by
  unfold pPsi; try dsimp only []
  repeat (first | rfl | split)

private theorem genSig_l_shield (κ : Nat) (l r : AgentState ψ) :
    (genSig hψ κ l r).1.shield = l.shield := by
  simp only [genSig, wait, Prod_fst_ite, Prod_snd_ite, AgentState_shield_ite, ite_same]

private theorem cleanSig_l_shield (l r : AgentState ψ) :
    (cleanSig hψ l r).1.shield = l.shield := by
  simp only [cleanSig, cleanSigCleanApply_shield, cleanSigGenConnect_shield,
    cleanSigStep3_l_shield, cleanSigStep4_l_shield,
    cleanSigStep5_l_shield, cleanSigStep6_l_shield]

private theorem eliminateSig_l_shield (l r : AgentState ψ) :
    (eliminateSig hψ l r).1.shield = l.shield := by
  simp only [eliminateSig, Prod_fst_ite, AgentState_shield_ite, ite_same]

private theorem sigMove_l_shield (l r : AgentState ψ) :
    (sigMove hψ l r).1.shield = l.shield := by
  simp only [sigMove,
    sigMoveStep1_l_shield, sigMoveStep2_l_shield, sigMoveStep3_l_shield,
    sigMoveStep4_l_shield, sigMoveStep5_l_shield,
    sigMoveApplyControl_shield,
    Prod_fst_ite, Prod_snd_ite, AgentState_shield_ite, ite_same]

private theorem checkSig_l_shield (l r : AgentState ψ) :
    (checkSig hψ l r).1.shield = l.shield := by
  simp only [checkSig, checkSigSetReady_shield, checkSigCheckL_shield,
    checkSigSetResult_shield]

private theorem disappear_l_shield (l r : AgentState ψ) :
    (disappear hψ l r).1.shield = l.shield := by
  simp only [disappear, Prod_fst_ite, Prod_snd_ite, AgentState_shield_ite, ite_same]

private theorem compareBit_l_shield (l r : AgentState ψ) :
    (compareBit hψ l r).1.shield = l.shield := by
  simp only [compareBit, compareBitUpdateL_shield]

private theorem cmpUpdate_l_shield (l r : AgentState ψ) :
    (cmpUpdate hψ l r).1.shield = l.shield := by
  simp only [cmpUpdate, cmpUpdatePropagate_l_shield, cmpUpdateSetPath2_shield,
    AgentState_shield_ite, ite_same]

private theorem compareSigDispatch_l_shield (l r : AgentState ψ) :
    (compareSigDispatch hψ l r).1.shield = l.shield := by
  unfold compareSigDispatch
  repeat (first | exact compareBit_l_shield hψ l r | rfl | split)

private theorem compareSig_l_shield (l r : AgentState ψ) :
    (compareSig hψ l r).1.shield = l.shield := by
  unfold compareSig; dsimp only []
  split
  · exact compareSigInit_shield l
  · split
    · simp only [compareSigDispatch_l_shield, cmpUpdate_l_shield, compareSigInit_shield]
    · exact compareSigInit_shield l

private theorem suppressSig_l_shield (l r : AgentState ψ) :
    (suppressSig hψ l r).1.shield = l.shield := by
  simp only [suppressSig, Prod_fst_ite, Prod_snd_ite,
    AgentState_shield_ite, AgentState_leader_ite,
    AgentState_reset_cmd_ite, AgentState_echo_ite,
    AgentState_count_ite, ite_same]

/-! ### r.bullet stability through pPsi..suppressSig -/

/-! Single-agent bullet step lemmas -/

private theorem cleanSigGenConnect_bullet (u : AgentState ψ) :
    (cleanSigGenConnect u).bullet = u.bullet := by
  unfold cleanSigGenConnect; try dsimp only []
  repeat (first | rfl | split)

private theorem cleanSigCleanApply_bullet (u : AgentState ψ) :
    (cleanSigCleanApply u).bullet = u.bullet := by
  unfold cleanSigCleanApply; try dsimp only []
  repeat (first | rfl | split)

private theorem checkSigSetReady_bullet (u : AgentState ψ) :
    (checkSigSetReady u).bullet = u.bullet := by
  unfold checkSigSetReady; try dsimp only []
  repeat (first | rfl | split)

private theorem checkSigCheckL_bullet (u : AgentState ψ) :
    (checkSigCheckL hψ u).bullet = u.bullet := by
  unfold checkSigCheckL; try dsimp only []
  repeat (first | rfl | split)

private theorem checkSigCheckR_bullet (l r : AgentState ψ) :
    (checkSigCheckR hψ l r).bullet = r.bullet := by
  unfold checkSigCheckR; try dsimp only []
  repeat (first | rfl | split)

private theorem checkSigSetResult_bullet (u : AgentState ψ) :
    (checkSigSetResult u).bullet = u.bullet := by
  unfold checkSigSetResult; try dsimp only []
  repeat (first | rfl | split)

private theorem compareBitUpdateR_bullet (r : AgentState ψ) :
    (compareBitUpdateR hψ r).bullet = r.bullet := by
  unfold compareBitUpdateR; try dsimp only []
  repeat (first | rfl | split)

private theorem cmpUpdateSetPath2_bullet (l : AgentState ψ) :
    (cmpUpdateSetPath2 hψ l).bullet = l.bullet := by
  unfold cmpUpdateSetPath2; try dsimp only []
  repeat (first | rfl | split)

private theorem sigMoveApplyControl_bullet (u : AgentState ψ) :
    (sigMoveApplyControl hψ u).bullet = u.bullet := by
  unfold sigMoveApplyControl; try dsimp only []
  repeat (first | rfl | split)

private theorem compareSigInit_bullet (l : AgentState ψ) :
    (compareSigInit l).bullet = l.bullet := by
  unfold compareSigInit; split <;> rfl

/-! Pair bullet step lemmas -/

private theorem cleanSigStep3_r_bullet (l r : AgentState ψ) :
    (cleanSigStep3 l r).2.bullet = r.bullet := by
  unfold cleanSigStep3; try dsimp only []
  repeat (first | rfl | split)

private theorem cleanSigStep4_r_bullet (l r : AgentState ψ) :
    (cleanSigStep4 l r).2.bullet = r.bullet := by
  unfold cleanSigStep4; try dsimp only []
  repeat (first | rfl | split)

private theorem cleanSigStep5_r_bullet (l r : AgentState ψ) :
    (cleanSigStep5 hψ l r).2.bullet = r.bullet := by
  unfold cleanSigStep5; try dsimp only []
  repeat (first | rfl | split)

private theorem cleanSigStep6_r_bullet (l r : AgentState ψ) :
    (cleanSigStep6 hψ l r).2.bullet = r.bullet := by
  unfold cleanSigStep6; try dsimp only []
  repeat (first | rfl | split)

private theorem sigMoveStep1_r_bullet (l r : AgentState ψ) :
    (sigMoveStep1 l r).2.bullet = r.bullet := by
  unfold sigMoveStep1; try dsimp only []
  repeat (first | rfl | split)

private theorem sigMoveStep2_r_bullet (l r : AgentState ψ) :
    (sigMoveStep2 l r).2.bullet = r.bullet := by
  unfold sigMoveStep2; try dsimp only []
  repeat (first | rfl | split)

private theorem sigMoveStep3_r_bullet (l r : AgentState ψ) :
    (sigMoveStep3 l r).2.bullet = r.bullet := by
  unfold sigMoveStep3; try dsimp only []
  repeat (first | rfl | split)

private theorem sigMoveStep4_r_bullet (l r : AgentState ψ) :
    (sigMoveStep4 l r).2.bullet = r.bullet := by
  unfold sigMoveStep4; try dsimp only []
  repeat (first | rfl | split)

private theorem sigMoveStep5_r_bullet (l r : AgentState ψ) :
    (sigMoveStep5 l r).2.bullet = r.bullet := by
  unfold sigMoveStep5; try dsimp only []
  repeat (first | rfl | split)

private theorem cmpUpdatePropagate_r_bullet (l r : AgentState ψ) :
    (cmpUpdatePropagate hψ l r).2.bullet = r.bullet := by
  unfold cmpUpdatePropagate; try dsimp only []
  repeat (first | rfl | split)

private theorem moveWsigTransfer_r_bullet (l r : AgentState ψ) :
    (moveWsigTransfer l r).2.bullet = r.bullet := by
  unfold moveWsigTransfer; try dsimp only []
  repeat (first | rfl | split)

private theorem moveWsigCheckGenWs_bullet (l r : AgentState ψ) :
    (moveWsigCheckGenWs l r).bullet = r.bullet := by
  unfold moveWsigCheckGenWs; repeat (first | rfl | split)

/-! Bullet composition lemmas -/

private theorem pPsi_r_bullet (l r : AgentState ψ) :
    (pPsi hψ l r).2.bullet = r.bullet := by
  unfold pPsi; try dsimp only []
  repeat (first | rfl | split)

private theorem genSig_r_bullet (κ : Nat) (l r : AgentState ψ) :
    (genSig hψ κ l r).2.bullet = r.bullet := by
  simp only [genSig, wait, Prod_fst_ite, Prod_snd_ite, AgentState_bullet_ite, ite_same]

private theorem cleanSig_r_bullet (l r : AgentState ψ) :
    (cleanSig hψ l r).2.bullet = r.bullet := by
  simp only [cleanSig, cleanSigCleanApply_bullet, cleanSigGenConnect_bullet,
    cleanSigStep3_r_bullet, cleanSigStep4_r_bullet,
    cleanSigStep5_r_bullet, cleanSigStep6_r_bullet]

private theorem eliminateSig_r_bullet (l r : AgentState ψ) :
    (eliminateSig hψ l r).2.bullet = r.bullet := by
  simp only [eliminateSig, Prod_snd_ite, AgentState_bullet_ite, ite_same]

private theorem sigMove_r_bullet (l r : AgentState ψ) :
    (sigMove hψ l r).2.bullet = r.bullet := by
  simp only [sigMove,
    sigMoveStep1_r_bullet, sigMoveStep2_r_bullet, sigMoveStep3_r_bullet,
    sigMoveStep4_r_bullet, sigMoveStep5_r_bullet,
    sigMoveApplyControl_bullet,
    Prod_fst_ite, Prod_snd_ite, AgentState_bullet_ite, ite_same]

private theorem checkSig_r_bullet (l r : AgentState ψ) :
    (checkSig hψ l r).2.bullet = r.bullet := by
  simp only [checkSig, checkSigSetReady_bullet, checkSigCheckR_bullet,
    checkSigSetResult_bullet, AgentState_bullet_ite, ite_same]

private theorem disappear_r_bullet (l r : AgentState ψ) :
    (disappear hψ l r).2.bullet = r.bullet := by
  simp only [disappear, Prod_fst_ite, Prod_snd_ite, AgentState_bullet_ite, ite_same]

private theorem compareBit_r_bullet (l r : AgentState ψ) :
    (compareBit hψ l r).2.bullet = r.bullet := by
  simp only [compareBit, compareBitUpdateR_bullet]

private theorem cmpUpdate_r_bullet (l r : AgentState ψ) :
    (cmpUpdate hψ l r).2.bullet = r.bullet := by
  simp only [cmpUpdate, cmpUpdatePropagate_r_bullet, cmpUpdateSetPath2_bullet,
    AgentState_bullet_ite, ite_same]

private theorem compareSigDispatch_r_bullet (l r : AgentState ψ) :
    (compareSigDispatch hψ l r).2.bullet = r.bullet := by
  unfold compareSigDispatch
  repeat (first | exact compareBit_r_bullet hψ l r | rfl | split)

private theorem compareSig_r_bullet (l r : AgentState ψ) :
    (compareSig hψ l r).2.bullet = r.bullet := by
  unfold compareSig; dsimp only []
  split
  · rfl
  · split
    · simp only [compareSigDispatch_r_bullet, cmpUpdate_r_bullet]
    · rfl

private theorem suppressSig_r_bullet (l r : AgentState ψ) :
    (suppressSig hψ l r).2.bullet = r.bullet := by
  simp only [suppressSig, Prod_fst_ite, Prod_snd_ite,
    AgentState_bullet_ite, AgentState_leader_ite,
    AgentState_reset_cmd_ite, AgentState_echo_ite,
    AgentState_count_ite, ite_same]

/-! ### eliminateLeaders: l.leader either preserved or cleared with bullet/shield condition -/

private theorem eliminateLeaders_l_leader_or_bullet (l r : AgentState ψ)
    (hleader : l.leader = true) :
    (eliminateLeaders hψ l r).1.leader = true ∨
    (r.bullet = ⟨2, by omega⟩ ∧ l.shield = false) := by
  simp only [eliminateLeaders]
  repeat split
  all_goals simp_all
  all_goals (
    by_cases hb : r.bullet = (2 : Fin 3)
    · cases l.shield <;> simp_all
    · exact Or.inl (Or.inr (Or.inl hb)))

/-- EliminateLeaders' may destroy an initiator leader but never creates one. -/
private theorem eliminateLeaders_l_leader_true_implies
    (l r : AgentState ψ)
    (h : (eliminateLeaders hψ l r).1.leader = true) :
    l.leader = true := by
  cases hl : l.leader
  · simp only [eliminateLeaders, hl, Bool.false_eq_true, false_and,
      if_false, Prod_fst_ite, AgentState_leader_ite, ite_same] at h
  · rfl

/-! ### l.leader stability for writeSeq sub-algorithms -/

private theorem groupInfo_l_leader (l r : AgentState ψ) :
    (groupInfo hψ l r).1.leader = l.leader := by
  simp only [groupInfo, Prod_fst_ite, Prod_snd_ite,
    AgentState_leader_ite, AgentState_last_set_ite,
    AgentState_last_ite, AgentState_last_unset_ite, ite_same]

private theorem gensigWriteseq_l_leader (l r : AgentState ψ) :
    (gensigWriteseq hψ l r).1.leader = l.leader := by
  simp only [gensigWriteseq, Prod_fst_ite, Prod_snd_ite,
    AgentState_leader_ite, AgentState_bit_ite,
    AgentState_write_state_ite, AgentState_b_carry_ite, ite_same]

private theorem writeAction_l_leader (l r : AgentState ψ) :
    (writeAction hψ l r).1.leader = l.leader := by
  unfold writeAction writeActionToState
  simp only [writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader,
    Prod_fst_ite, AgentState_leader_ite, AgentState_write_state_ite, ite_same]

private theorem moveWsig_l_leader (l r : AgentState ψ) :
    (moveWsig hψ l r).1.leader = l.leader := by
  unfold moveWsig
  simp only [moveWsigCheckGenWs_leader, moveWsigCheckLast_leader,
    moveWsigTransfer_l_leader, moveWsigTransfer_r_leader,
    Prod_fst_ite, Prod_snd_ite, AgentState_leader_ite, ite_same]

/-! ### writeSeq: l.leader = true is preserved -/

private theorem writeSeq_l_leader_of_true (l r : AgentState ψ)
    (h : l.leader = true) :
    (writeSeq hψ l r).1.leader = true := by
  simp only [writeSeq, writeSeqThroughPrepare, writeSeqAfterPrepare,
    writeSeqLeaderMove, writeSeqGenerate, writeSeqPrepare, writeSeqReady,
    writeSeqCompare, writeSeqCommands, h,
    writeSeqSetWriteReady_leader, writeSeqSetWriteAct_leader,
    groupInfo_l_leader, gensigWriteseq_l_leader,
    writeAction_l_leader, moveWsig_l_leader,
    Prod_fst_ite, Prod_snd_ite, AgentState_leader_ite, ite_same]

/-! ## eliminateLeaders and writeSeq shield stability -/

private theorem eliminateLeaders_l_shield_of_true (l r : AgentState ψ)
    (hs : l.shield = true) :
    (eliminateLeaders hψ l r).1.shield = true := by
  simp only [eliminateLeaders, Prod_fst_ite, Prod_snd_ite,
    AgentState_shield_ite, AgentState_leader_ite, AgentState_signal_B_ite,
    AgentState_bullet_ite, ite_same, hs]
  repeat split <;> simp_all

private theorem groupInfo_l_shield (l r : AgentState ψ) :
    (groupInfo hψ l r).1.shield = l.shield := by
  simp only [groupInfo, Prod_fst_ite, Prod_snd_ite,
    AgentState_shield_ite, AgentState_last_set_ite,
    AgentState_last_ite, AgentState_last_unset_ite, ite_same]

private theorem gensigWriteseq_l_shield (l r : AgentState ψ) :
    (gensigWriteseq hψ l r).1.shield = l.shield := by
  simp only [gensigWriteseq, Prod_fst_ite, Prod_snd_ite,
    AgentState_shield_ite, AgentState_bit_ite,
    AgentState_write_state_ite, AgentState_path3_ite,
    AgentState_gen_ws_ite, AgentState_b_carry_ite, ite_same]

private theorem writeSeqSetWriteReady_shield (u : AgentState ψ) :
    (writeSeqSetWriteReady u).shield = u.shield := by
  unfold writeSeqSetWriteReady; repeat (first | rfl | split)

private theorem writeSeqCheckBit_shield (r : AgentState ψ) :
    (writeSeqCheckBit r).shield = r.shield := by
  unfold writeSeqCheckBit; repeat (first | rfl | split)

private theorem writeSeqSetWriteAct_shield (u : AgentState ψ) :
    (writeSeqSetWriteAct u).shield = u.shield := by
  unfold writeSeqSetWriteAct
  simp only [AgentState_shield_ite]
  split
  · split
    · split <;> simp_all
    · simp_all
  · simp_all

private theorem writeSeqFinalR_shield (r : AgentState ψ) :
    (writeSeqFinalR r).shield = r.shield := by
  unfold writeSeqFinalR; repeat (first | rfl | split)

private theorem writeActionApplyOverwrite_shield (r : AgentState ψ) :
    (writeActionApplyOverwrite r).shield = r.shield := by
  unfold writeActionApplyOverwrite; repeat (first | rfl | split)

private theorem writeActionApplyMoveFlip_shield (r : AgentState ψ) :
    (writeActionApplyMoveFlip r).shield = r.shield := by
  unfold writeActionApplyMoveFlip; repeat (first | rfl | split)

private theorem writeAction_l_shield (l r : AgentState ψ) :
    (writeAction hψ l r).1.shield = l.shield := by
  simp only [writeAction, Prod_fst_ite, Prod_snd_ite,
    AgentState_shield_ite, writeActionApplyOverwrite_shield,
    writeActionApplyMoveFlip_shield,
    AgentState_write_state_ite, AgentState_write_ite,
    AgentState_bit_ite, ite_same]

private theorem moveWsigCheckGenWs_shield (l r : AgentState ψ) :
    (moveWsigCheckGenWs l r).shield = r.shield := by
  unfold moveWsigCheckGenWs; repeat (first | rfl | split)

private theorem moveWsigCheckLast_shield (l : AgentState ψ) :
    (moveWsigCheckLast l).shield = l.shield := by
  unfold moveWsigCheckLast; repeat (first | rfl | split)

private theorem moveWsig_l_shield (l r : AgentState ψ) :
    (moveWsig hψ l r).1.shield = l.shield := by
  simp only [moveWsig, moveWsigTransfer_l_shield, moveWsigCheckLast_shield,
    Prod_fst_ite, Prod_snd_ite, AgentState_shield_ite,
    AgentState_path3_ite, AgentState_write_ite, AgentState_write_state_ite,
    AgentState_signal_ws_ite, AgentState_gen_ws_ite,
    AgentState_ws_echo_ite, ite_same]

private theorem writeSeq_l_shield (l r : AgentState ψ) :
    (writeSeq hψ l r).1.shield = l.shield := by
  simp only [writeSeq, writeSeqThroughPrepare, writeSeqAfterPrepare,
    writeSeqLeaderMove, writeSeqGenerate, writeSeqPrepare, writeSeqReady,
    writeSeqCompare, writeSeqCommands, groupInfo_l_shield,
    gensigWriteseq_l_shield,
    writeSeqSetWriteReady_shield,
    writeSeqSetWriteAct_shield,
    writeAction_l_shield, moveWsig_l_shield,
    Prod_fst_ite, Prod_snd_ite, AgentState_shield_ite, ite_same]

/-! ## ProtocolProperties axiom: leader_initiator_stable -/

private theorem eliminateLeaders_l_leader_of (l r : AgentState ψ)
    (hl : l.leader = true)
    (hk : ¬(r.bullet = ⟨2, by omega⟩ ∧ l.shield = false)) :
    (eliminateLeaders hψ l r).1.leader = true := by
  rcases eliminateLeaders_l_leader_or_bullet hψ l r hl with h | ⟨hb, hs⟩
  · exact h
  · exact absurd ⟨hb, hs⟩ hk

theorem ppll_leader_initiator_stable (κ : Nat) (l r : AgentState ψ)
    (hleader : l.leader = true) :
    (ppll hψ κ l r).1.leader = true ∨
    (r.bullet = ⟨2, by omega⟩ ∧ l.shield = false) := by
  by_cases hk : r.bullet = ⟨2, by omega⟩ ∧ l.shield = false
  · right; exact hk
  · left
    have key : ∀ l' r' : AgentState ψ,
        l'.leader = l.leader → l'.shield = l.shield → r'.bullet = r.bullet →
        (eliminateLeaders hψ l' r').1.leader = true := by
      intro l' r' hl' hs' hb'
      apply eliminateLeaders_l_leader_of
      · rw [hl']; exact hleader
      · intro ⟨hb, hs⟩; exact hk ⟨hb' ▸ hb, hs' ▸ hs⟩
    simp only [ppll, ppllBeforeWriteSeq, ppllBeforeEliminateLeaders,
      ppllAfterCheck, ppllBeforeCheck, pPsi_l_leader, genSig_l_leader, cleanSig_l_leader,
      eliminateSig_l_leader, sigMove_l_leader, checkSig_l_leader,
      disappear_l_leader, compareSig_l_leader, suppressSig_l_leader,
      pPsi_l_shield, genSig_l_shield, cleanSig_l_shield,
      eliminateSig_l_shield, sigMove_l_shield, checkSig_l_shield,
      disappear_l_shield, compareSig_l_shield, suppressSig_l_shield,
      pPsi_r_bullet, genSig_r_bullet, cleanSig_r_bullet,
      eliminateSig_r_bullet, sigMove_r_bullet, checkSig_r_bullet,
      disappear_r_bullet, compareSig_r_bullet, suppressSig_r_bullet,
      key, writeSeq_l_leader_of_true]

/-! ## Concrete leader-creation classification -/

/-- The named boundaries are definitionally the original Algorithm-1 order. -/
theorem ppll_eq_writeSeq_after_named_prefix (κ : Nat)
    (l r : AgentState ψ) :
    ppll hψ κ l r =
      writeSeq hψ (ppllBeforeWriteSeq hψ κ l r).1
        (ppllBeforeWriteSeq hψ κ l r).2 := by
  rfl

private theorem ppllBeforeCheck_r_leader (κ : Nat)
    (l r : AgentState ψ) :
    (ppllBeforeCheck hψ κ l r).2.leader = (pPsi hψ l r).2.leader := by
  simp only [ppllBeforeCheck, genSig_r_leader, cleanSig_r_leader,
    eliminateSig_r_leader, sigMove_r_leader]

private theorem ppllBeforeWriteSeq_r_leader (κ : Nat)
    (l r : AgentState ψ) :
    (ppllBeforeWriteSeq hψ κ l r).2.leader =
      (ppllAfterCheck hψ κ l r).2.leader := by
  simp only [ppllBeforeWriteSeq, ppllBeforeEliminateLeaders,
    disappear_r_leader, compareSig_r_leader, suppressSig_r_leader,
    eliminateLeaders_r_leader]

private theorem ppllBeforeWriteSeq_l_leader_true_implies
    (κ : Nat) (l r : AgentState ψ)
    (h : (ppllBeforeWriteSeq hψ κ l r).1.leader = true) :
    l.leader = true := by
  have hstep :
      (eliminateLeaders hψ (ppllBeforeEliminateLeaders hψ κ l r).1
        (ppllBeforeEliminateLeaders hψ κ l r).2).1.leader = true := by
    simpa only [ppllBeforeWriteSeq] using h
  have hq : (ppllBeforeEliminateLeaders hψ κ l r).1.leader = true :=
    eliminateLeaders_l_leader_true_implies hψ _ _ hstep
  have hqeq :
      (ppllBeforeEliminateLeaders hψ κ l r).1.leader = l.leader := by
    simp only [ppllBeforeEliminateLeaders, ppllAfterCheck, ppllBeforeCheck,
      pPsi_l_leader, genSig_l_leader, cleanSig_l_leader,
      eliminateSig_l_leader, sigMove_l_leader, checkSig_l_leader,
      disappear_l_leader, compareSig_l_leader, suppressSig_l_leader]
  exact hqeq.symm.trans hq

/-- P'_ψ can turn a follower responder into a leader only when its probe meets
a barrier. This is the exact concrete Algorithm-2 creation case. -/
theorem pPsi_new_responder_leader_requires_probe_barrier
    (l r : AgentState ψ)
    (hnew : (pPsi hψ l r).2.leader = true)
    (hold : r.leader = false) :
    r.probe = true ∧ isBarrier hψ l r := by
  have hbar : isBarrier hψ l r := by
    unfold isBarrier
    by_cases heq : r.label =
        ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
    · have hnbar : ¬r.label ≠
          ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩ :=
        fun hne => hne heq
      simp only [pPsi, if_neg hnbar] at hnew
      split at hnew <;> simp_all
    · exact heq
  refine ⟨?_, hbar⟩
  by_cases hp : r.probe = true
  · exact hp
  · have hpfalse : r.probe = false := by
      cases h : r.probe <;> simp_all
    unfold isBarrier at hbar
    simp only [pPsi, if_pos hbar, hpfalse, Bool.false_eq_true,
      if_false] at hnew
    split at hnew <;> simp_all

/-- CHECK can turn a follower responder into a leader only at a terminal
`.equal` state. The condition is stated on the output because CHECK may compute
`.equal` during the same interaction. -/
theorem checkSig_new_responder_leader_requires_terminal_equal
    (l r : AgentState ψ)
    (hnew : (checkSig hψ l r).2.leader = true)
    (hold : r.leader = false) :
    (checkSig hψ l r).2.label = ⟨ψ - 1, by omega⟩ ∧
    (checkSig hψ l r).2.state = .equal := by
  let l₀ := checkSigSetReady l
  let r₀ := checkSigSetReady r
  let l₁ := checkSigCheckL hψ l₀
  let r₁ := checkSigCheckR hψ l₁ r₀
  let r₂ := checkSigSetResult r₁
  have hrleader : r₂.leader = r.leader := by
    simp only [r₂, r₁, r₀, checkSigSetResult_leader,
      checkSigCheckR_leader, checkSigSetReady_leader]
  by_cases hterminal :
      r₂.label = ⟨ψ - 1, by omega⟩ ∧ r₂.state = .equal
  · simpa only [checkSig, l₀, r₀, l₁, r₁, r₂, hterminal,
      and_self, if_true] using hterminal
  · exfalso
    have hnew' : r₂.leader = true := by
      simpa only [checkSig, l₀, r₀, l₁, r₁, r₂, hterminal,
        if_false] using hnew
    rw [hrleader, hold] at hnew'
    contradiction

/-- WRITE_SEQ never creates leadership at the responder position. It either
preserves the responder or migrates its leadership to the initiator. -/
theorem writeSeq_responder_leader_was_leader
    (l r : AgentState ψ)
    (hnew : (writeSeq hψ l r).2.leader = true) :
    r.leader = true := by
  by_cases hmigrate : r.leader = true ∧ r.label ≠ ⟨0, hψ⟩
  · exact hmigrate.1
  · have hout : (writeSeq hψ l r).2.leader = r.leader := by
      simp only [writeSeq, writeSeqThroughPrepare, writeSeqAfterPrepare,
        writeSeqLeaderMove, writeSeqGenerate, writeSeqPrepare, writeSeqReady,
        writeSeqCompare, writeSeqCommands, if_neg hmigrate,
        writeSeqSetWriteReady_leader, writeSeqCheckBit_leader,
        writeSeqSetWriteAct_leader, writeSeqFinalR_leader,
        groupInfo_r_leader, gensigWriteseq_r_leader,
        writeAction_r_leader, moveWsig_r_leader,
        Prod_fst_ite, Prod_snd_ite, AgentState_leader_ite, ite_same]
    rw [hout] at hnew
    exact hnew

/-- A nonzero-label responder leader is migrated atomically by WRITE_SEQ;
the responder endpoint is cleared rather than duplicated. -/
theorem writeSeq_responder_false_of_nonzero_leader
    (l r : AgentState ψ)
    (hmigrate : r.leader = true ∧ r.label ≠ ⟨0, hψ⟩) :
    (writeSeq hψ l r).2.leader = false := by
  simp only [writeSeq, writeSeqThroughPrepare, writeSeqAfterPrepare,
    writeSeqLeaderMove, writeSeqGenerate, writeSeqPrepare, writeSeqReady,
    writeSeqCompare, writeSeqCommands, if_pos hmigrate,
    writeSeqSetWriteReady_leader, writeSeqCheckBit_leader,
    writeSeqSetWriteAct_leader, writeSeqFinalR_leader,
    groupInfo_r_leader, gensigWriteseq_r_leader,
    writeAction_r_leader, moveWsig_r_leader,
    Prod_fst_ite, Prod_snd_ite, AgentState_leader_ite, ite_same]

/-- A nonzero-label responder leader is migrated to the initiator by
WRITE_SEQ.  This is the positive half of the same atomic source branch whose
responder-clear half is stated above. -/
theorem writeSeq_initiator_true_of_nonzero_responder_leader
    (l r : AgentState ψ)
    (hmigrate : r.leader = true ∧ r.label ≠ ⟨0, hψ⟩) :
    (writeSeq hψ l r).1.leader = true := by
  simp only [writeSeq, writeSeqThroughPrepare, writeSeqAfterPrepare,
    writeSeqLeaderMove, writeSeqGenerate, writeSeqPrepare, writeSeqReady,
    writeSeqCompare, writeSeqCommands, if_pos hmigrate,
    writeSeqSetWriteReady_leader, writeSeqCheckBit_leader,
    writeSeqSetWriteAct_leader, writeSeqFinalR_leader,
    groupInfo_l_leader, gensigWriteseq_l_leader,
    writeAction_l_leader, moveWsig_l_leader,
    Prod_fst_ite, Prod_snd_ite, AgentState_leader_ite, ite_same]

/-- WRITE_SEQ can turn a follower initiator into a leader only by migrating
an existing responder leader whose label is nonzero. Thus this operation moves
a leader; it is not an independent source of leader-count increase. -/
theorem writeSeq_new_initiator_requires_responder_leader
    (l r : AgentState ψ)
    (hnew : (writeSeq hψ l r).1.leader = true)
    (hold : l.leader = false) :
    r.leader = true ∧ r.label ≠ ⟨0, hψ⟩ := by
  by_cases hmigrate : r.leader = true ∧ r.label ≠ ⟨0, hψ⟩
  · exact hmigrate
  · exfalso
    have hout : (writeSeq hψ l r).1.leader = l.leader := by
      simp only [writeSeq, writeSeqThroughPrepare, writeSeqAfterPrepare,
        writeSeqLeaderMove, writeSeqGenerate, writeSeqPrepare, writeSeqReady,
        writeSeqCompare, writeSeqCommands, if_neg hmigrate,
        writeSeqSetWriteReady_leader, writeSeqSetWriteAct_leader,
        groupInfo_l_leader, gensigWriteseq_l_leader,
        writeAction_l_leader, moveWsig_l_leader,
        Prod_fst_ite, Prod_snd_ite, AgentState_leader_ite, ite_same]
    rw [hout, hold] at hnew
    contradiction

/-- Complete responder-side creation classification for concrete P_PLL.
If a follower responder is a leader after the full transition, either Algorithm
2 used a probe at an original barrier, or Algorithm 11 produced a terminal
`.equal` result at the named CHECK boundary. Later algorithms cannot create a
responder leader, and WRITE_SEQ can only preserve or migrate it away. -/
theorem ppll_new_responder_leader_requires_barrier_or_check
    (κ : Nat) (l r : AgentState ψ)
    (hnew : (ppll hψ κ l r).2.leader = true)
    (hold : r.leader = false) :
    (r.probe = true ∧ isBarrier hψ l r) ∨
    ((ppllAfterCheck hψ κ l r).2.label = ⟨ψ - 1, by omega⟩ ∧
     (ppllAfterCheck hψ κ l r).2.state = .equal) := by
  rw [ppll_eq_writeSeq_after_named_prefix] at hnew
  have hbeforeWrite :
      (ppllBeforeWriteSeq hψ κ l r).2.leader = true :=
    writeSeq_responder_leader_was_leader hψ _ _ hnew
  have hafterCheck : (ppllAfterCheck hψ κ l r).2.leader = true := by
    rw [ppllBeforeWriteSeq_r_leader] at hbeforeWrite
    exact hbeforeWrite
  by_cases hbefore : (ppllBeforeCheck hψ κ l r).2.leader = true
  · left
    have hpPsi : (pPsi hψ l r).2.leader = true := by
      rw [ppllBeforeCheck_r_leader] at hbefore
      exact hbefore
    exact pPsi_new_responder_leader_requires_probe_barrier hψ l r hpPsi hold
  · right
    have hbeforeFalse :
        (ppllBeforeCheck hψ κ l r).2.leader = false := by
      cases h : (ppllBeforeCheck hψ κ l r).2.leader <;> simp_all
    exact checkSig_new_responder_leader_requires_terminal_equal hψ
      (ppllBeforeCheck hψ κ l r).1 (ppllBeforeCheck hψ κ l r).2
      hafterCheck hbeforeFalse

/-- A follower initiator cannot gain leadership from a responder leader already
at stable label zero: all prefix algorithms preserve initiator non-leadership,
and WRITE_SEQ migrates only nonzero-label responder leaders. -/
theorem ppll_initiator_not_created_of_responder_leader_zero
    (κ : Nat) (l r : AgentState ψ)
    (hl : l.leader = false) (hr : r.leader = true)
    (hrlabel : r.label = ⟨0, hψ⟩) :
    (ppll hψ κ l r).1.leader = false := by
  cases hout : (ppll hψ κ l r).1.leader
  · rfl
  · have hnew : (ppll hψ κ l r).1.leader = true := hout
    rw [ppll_eq_writeSeq_after_named_prefix] at hnew
    by_cases hleftBefore :
        (ppllBeforeWriteSeq hψ κ l r).1.leader = true
    · have horiginal := ppllBeforeWriteSeq_l_leader_true_implies
        hψ κ l r hleftBefore
      have himpossible : false = true := hl.symm.trans horiginal
      exact Bool.noConfusion himpossible
    · have hleftBeforeFalse :
          (ppllBeforeWriteSeq hψ κ l r).1.leader = false := by
        cases h : (ppllBeforeWriteSeq hψ κ l r).1.leader
        · rfl
        · exact (hleftBefore h).elim
      have hmigrate := writeSeq_new_initiator_requires_responder_leader hψ
        (ppllBeforeWriteSeq hψ κ l r).1
        (ppllBeforeWriteSeq hψ κ l r).2 hnew hleftBeforeFalse
      have hlabel :
          (ppllBeforeWriteSeq hψ κ l r).2.label = ⟨0, hψ⟩ := by
        simp only [ppllBeforeWriteSeq, ppllBeforeEliminateLeaders,
          ppllAfterCheck, ppllBeforeCheck,
          pPsi_r_label_of_leader_zero hψ l r hr hrlabel,
          genSig_r_label, cleanSig_r_label, eliminateSig_r_label,
          sigMove_r_label, checkSig_r_label, disappear_r_label,
          compareSig_r_label, suppressSig_r_label, eliminateLeaders_r_label]
      exact (hmigrate.2 hlabel).elim

/-- Complete initiator-side origin classification. Every final initiator leader
was either already one, was migrated from an original responder leader, or is
traceable to one of the two genuine creation mechanisms. -/
theorem ppll_initiator_leader_has_origin
    (κ : Nat) (l r : AgentState ψ)
    (hnew : (ppll hψ κ l r).1.leader = true) :
    l.leader = true ∨ r.leader = true ∨
      (r.probe = true ∧ isBarrier hψ l r) ∨
      ((ppllAfterCheck hψ κ l r).2.label = ⟨ψ - 1, by omega⟩ ∧
       (ppllAfterCheck hψ κ l r).2.state = .equal) := by
  by_cases hl : l.leader = true
  · exact .inl hl
  · right
    by_cases hr : r.leader = true
    · exact .inl hr
    · right
      have hlfalse : l.leader = false := by
        cases h : l.leader
        · rfl
        · exact (hl h).elim
      have hrfalse : r.leader = false := by
        cases h : r.leader
        · rfl
        · exact (hr h).elim
      rw [ppll_eq_writeSeq_after_named_prefix] at hnew
      by_cases hleftBefore :
          (ppllBeforeWriteSeq hψ κ l r).1.leader = true
      · have horiginal := ppllBeforeWriteSeq_l_leader_true_implies
          hψ κ l r hleftBefore
        exact (hl horiginal).elim
      · have hleftBeforeFalse :
            (ppllBeforeWriteSeq hψ κ l r).1.leader = false := by
          cases h : (ppllBeforeWriteSeq hψ κ l r).1.leader
          · rfl
          · exact (hleftBefore h).elim
        have hrightBefore :
            (ppllBeforeWriteSeq hψ κ l r).2.leader = true :=
          (writeSeq_new_initiator_requires_responder_leader hψ
            (ppllBeforeWriteSeq hψ κ l r).1
            (ppllBeforeWriteSeq hψ κ l r).2 hnew hleftBeforeFalse).1
        have hafterCheck :
            (ppllAfterCheck hψ κ l r).2.leader = true := by
          rw [ppllBeforeWriteSeq_r_leader] at hrightBefore
          exact hrightBefore
        by_cases hbefore :
            (ppllBeforeCheck hψ κ l r).2.leader = true
        · left
          have hpPsi : (pPsi hψ l r).2.leader = true := by
            rw [ppllBeforeCheck_r_leader] at hbefore
            exact hbefore
          exact pPsi_new_responder_leader_requires_probe_barrier
            hψ l r hpPsi hrfalse
        · right
          have hbeforeFalse :
              (ppllBeforeCheck hψ κ l r).2.leader = false := by
            cases h : (ppllBeforeCheck hψ κ l r).2.leader
            · rfl
            · exact (hbefore h).elim
          exact checkSig_new_responder_leader_requires_terminal_equal hψ
            (ppllBeforeCheck hψ κ l r).1
            (ppllBeforeCheck hψ κ l r).2 hafterCheck hbeforeFalse

/-! ## Algorithm-6 nesting regression -/

/-- In the printed Algorithm 6, `COMPARE_BIT` is nested under `r.path ≠ ⊥`.
Consequently COMPARE is inert when the initiator has a signal but the responder
does not, even if a stale `path2` value exists. This guards a former Lean
mistranscription that dispatched `COMPARE_BIT` outside that branch. -/
theorem compareSig_inert_of_right_path_bot (l r : AgentState ψ)
    (hl : l.path ≠ .bot) (hr : r.path = .bot) :
    compareSig hψ l r = (l, r) := by
  unfold compareSig compareSigInit
  cases hp : l.path with
  | bot => exact (hl hp).elim
  | some _ _ =>
    simp only [hp, hr]

/-! ## Corollaries: leader_destruction + shield stability -/

theorem ppll_leader_destruction_requires_bullet_no_shield (κ : Nat)
    (l r : AgentState ψ)
    (hleader : l.leader = true) (hnot : (ppll hψ κ l r).1.leader ≠ true) :
    r.bullet = ⟨2, by omega⟩ ∧ l.shield = false := by
  rcases ppll_leader_initiator_stable hψ κ l r hleader with h | h
  · exact absurd h hnot
  · exact h

theorem ppll_shield_stable_of_true (κ : Nat) (l r : AgentState ψ)
    (hs : l.shield = true) :
    (ppll hψ κ l r).1.shield = true := by
  simp only [ppll, ppllBeforeWriteSeq, ppllBeforeEliminateLeaders,
    ppllAfterCheck, ppllBeforeCheck, pPsi_l_shield, genSig_l_shield, cleanSig_l_shield,
    eliminateSig_l_shield, sigMove_l_shield, checkSig_l_shield,
    disappear_l_shield, compareSig_l_shield, suppressSig_l_shield,
    eliminateLeaders_l_shield_of_true, writeSeq_l_shield, hs]

theorem ppll_shield_removed_only_by_dummy (κ : Nat) (l r : AgentState ψ)
    (_hleader : l.leader = true) (hshield : l.shield = true)
    (hnot : (ppll hψ κ l r).1.shield ≠ true) :
    (ppll hψ κ l r).1.bullet = ⟨1, by omega⟩ := by
  exact absurd (ppll_shield_stable_of_true hψ κ l r hshield) hnot

/-! ## Public field-frame API for repaired transition factoring -/

/-- P'_ψ preserves the two fields inspected by ELIMINATE_LEADERS. -/
theorem pPsi_kill_fields_eq (l r : AgentState ψ) :
    (pPsi hψ l r).1.shield = l.shield ∧
      (pPsi hψ l r).2.bullet = r.bullet :=
  ⟨pPsi_l_shield hψ l r, pPsi_r_bullet hψ l r⟩

/-- CLEAN_SIG preserves the two fields inspected by ELIMINATE_LEADERS. -/
theorem cleanSig_kill_fields_eq (l r : AgentState ψ) :
    (cleanSig hψ l r).1.shield = l.shield ∧
      (cleanSig hψ l r).2.bullet = r.bullet :=
  ⟨cleanSig_l_shield hψ l r, cleanSig_r_bullet hψ l r⟩

/-- ELIMINATE_SIG preserves the two fields inspected by ELIMINATE_LEADERS. -/
theorem eliminateSig_kill_fields_eq (l r : AgentState ψ) :
    (eliminateSig hψ l r).1.shield = l.shield ∧
      (eliminateSig hψ l r).2.bullet = r.bullet :=
  ⟨eliminateSig_l_shield hψ l r, eliminateSig_r_bullet hψ l r⟩

/-- SIGMOVE preserves the two fields inspected by ELIMINATE_LEADERS. -/
theorem sigMove_kill_fields_eq (l r : AgentState ψ) :
    (sigMove hψ l r).1.shield = l.shield ∧
      (sigMove hψ l r).2.bullet = r.bullet :=
  ⟨sigMove_l_shield hψ l r, sigMove_r_bullet hψ l r⟩

/-- CHECK preserves the two fields inspected by ELIMINATE_LEADERS. -/
theorem checkSig_kill_fields_eq (l r : AgentState ψ) :
    (checkSig hψ l r).1.shield = l.shield ∧
      (checkSig hψ l r).2.bullet = r.bullet :=
  ⟨checkSig_l_shield hψ l r, checkSig_r_bullet hψ l r⟩

/-- DISAPPEAR preserves the two fields inspected by ELIMINATE_LEADERS. -/
theorem disappear_kill_fields_eq (l r : AgentState ψ) :
    (disappear hψ l r).1.shield = l.shield ∧
      (disappear hψ l r).2.bullet = r.bullet :=
  ⟨disappear_l_shield hψ l r, disappear_r_bullet hψ l r⟩

/-- COMPARE's update kernel preserves the two fields inspected by
ELIMINATE_LEADERS. -/
theorem cmpUpdate_kill_fields_eq (l r : AgentState ψ) :
    (cmpUpdate hψ l r).1.shield = l.shield ∧
      (cmpUpdate hψ l r).2.bullet = r.bullet :=
  ⟨cmpUpdate_l_shield hψ l r, cmpUpdate_r_bullet hψ l r⟩

/-- COMPARE dispatch preserves the two fields inspected by ELIMINATE_LEADERS. -/
theorem compareSigDispatch_kill_fields_eq (l r : AgentState ψ) :
    (compareSigDispatch hψ l r).1.shield = l.shield ∧
      (compareSigDispatch hψ l r).2.bullet = r.bullet :=
  ⟨compareSigDispatch_l_shield hψ l r,
    compareSigDispatch_r_bullet hψ l r⟩

/-- SUPPRESS_SIG preserves the two fields inspected by ELIMINATE_LEADERS. -/
theorem suppressSig_kill_fields_eq (l r : AgentState ψ) :
    (suppressSig hψ l r).1.shield = l.shield ∧
      (suppressSig hψ l r).2.bullet = r.bullet :=
  ⟨suppressSig_l_shield hψ l r, suppressSig_r_bullet hψ l r⟩

/-- P'_ψ preserves the initiator label. -/
theorem pPsi_initiator_label_eq (l r : AgentState ψ) :
    (pPsi hψ l r).1.label = l.label :=
  pPsi_l_label hψ l r

/-- P'_ψ preserves a non-barrier responder label. -/
theorem pPsi_responder_label_of_nonbarrier (l r : AgentState ψ)
    (h : ¬isBarrier hψ l r) : (pPsi hψ l r).2.label = r.label :=
  pPsi_r_label_of_non_barrier hψ l r h

/-- A label-zero responder leader keeps its label through P'_ψ. -/
theorem pPsi_responder_label_of_leader_zero (l r : AgentState ψ)
    (hr : r.leader = true) (hrLabel : r.label = ⟨0, hψ⟩) :
    (pPsi hψ l r).2.label = r.label := by
  rw [pPsi_r_label_of_leader_zero hψ l r hr hrLabel, hrLabel]

/-- P'_ψ preserves an existing responder leader. -/
theorem pPsi_responder_leader_of_true (l r : AgentState ψ)
    (hr : r.leader = true) : (pPsi hψ l r).2.leader = true :=
  pPsi_r_leader_of_leader hψ l r hr

/-- P'_ψ never changes the initiator's leader bit. -/
theorem pPsi_initiator_leader_eq (l r : AgentState ψ) :
    (pPsi hψ l r).1.leader = l.leader :=
  pPsi_l_leader hψ l r

/-- CHECK never changes the initiator's leader bit. -/
theorem checkSig_initiator_leader_eq (l r : AgentState ψ) :
    (checkSig hψ l r).1.leader = l.leader :=
  checkSig_l_leader hψ l r

/-- CHECK never removes an existing responder leader. -/
theorem checkSig_responder_leader_of_true (l r : AgentState ψ)
    (hr : r.leader = true) :
    (checkSig hψ l r).2.leader = true :=
  checkSig_r_leader_of_true hψ l r hr

/-- CLEAN_SIG frames both labels. -/
theorem cleanSig_labels_eq (l r : AgentState ψ) :
    (cleanSig hψ l r).1.label = l.label ∧
      (cleanSig hψ l r).2.label = r.label :=
  ⟨cleanSig_l_label hψ l r, cleanSig_r_label hψ l r⟩

/-- The SIGMOVE control interpreter frames labels. -/
theorem sigMoveApplyControl_label_eq (u : AgentState ψ) :
    (sigMoveApplyControl hψ u).label = u.label :=
  sigMoveApplyControl_label hψ u

/-- The SIGMOVE control interpreter frames shields. -/
theorem sigMoveApplyControl_shield_eq (u : AgentState ψ) :
    (sigMoveApplyControl hψ u).shield = u.shield :=
  sigMoveApplyControl_shield hψ u

/-- ELIMINATE_SIG frames both labels. -/
theorem eliminateSig_labels_eq (l r : AgentState ψ) :
    (eliminateSig hψ l r).1.label = l.label ∧
      (eliminateSig hψ l r).2.label = r.label :=
  ⟨eliminateSig_l_label hψ l r, eliminateSig_r_label hψ l r⟩

/-- SIGMOVE frames both labels. -/
theorem sigMove_labels_eq (l r : AgentState ψ) :
    (sigMove hψ l r).1.label = l.label ∧
      (sigMove hψ l r).2.label = r.label :=
  ⟨sigMove_l_label hψ l r, sigMove_r_label hψ l r⟩

/-- CHECK frames both labels. -/
theorem checkSig_labels_eq (l r : AgentState ψ) :
    (checkSig hψ l r).1.label = l.label ∧
      (checkSig hψ l r).2.label = r.label :=
  ⟨checkSig_l_label hψ l r, checkSig_r_label hψ l r⟩

/-- DISAPPEAR frames both labels. -/
theorem disappear_labels_eq (l r : AgentState ψ) :
    (disappear hψ l r).1.label = l.label ∧
      (disappear hψ l r).2.label = r.label :=
  ⟨disappear_l_label hψ l r, disappear_r_label hψ l r⟩

/-- COMPARE dispatch frames both labels. -/
theorem compareSigDispatch_labels_eq (l r : AgentState ψ) :
    (compareSigDispatch hψ l r).1.label = l.label ∧
      (compareSigDispatch hψ l r).2.label = r.label :=
  ⟨compareSigDispatch_l_label hψ l r,
    compareSigDispatch_r_label hψ l r⟩

/-- SUPPRESS_SIG frames both labels. -/
theorem suppressSig_labels_eq (l r : AgentState ψ) :
    (suppressSig hψ l r).1.label = l.label ∧
      (suppressSig hψ l r).2.label = r.label :=
  ⟨suppressSig_l_label hψ l r, suppressSig_r_label hψ l r⟩

/-- CLEAN_SIG frames both leader bits. -/
theorem cleanSig_leaders_eq (l r : AgentState ψ) :
    (cleanSig hψ l r).1.leader = l.leader ∧
      (cleanSig hψ l r).2.leader = r.leader :=
  ⟨cleanSig_l_leader hψ l r, cleanSig_r_leader hψ l r⟩

/-- ELIMINATE_SIG frames both leader bits. -/
theorem eliminateSig_leaders_eq (l r : AgentState ψ) :
    (eliminateSig hψ l r).1.leader = l.leader ∧
      (eliminateSig hψ l r).2.leader = r.leader :=
  ⟨eliminateSig_l_leader hψ l r, eliminateSig_r_leader hψ l r⟩

/-- SIGMOVE frames both leader bits. -/
theorem sigMove_leaders_eq (l r : AgentState ψ) :
    (sigMove hψ l r).1.leader = l.leader ∧
      (sigMove hψ l r).2.leader = r.leader :=
  ⟨sigMove_l_leader hψ l r, sigMove_r_leader hψ l r⟩

/-- DISAPPEAR frames both leader bits. -/
theorem disappear_leaders_eq (l r : AgentState ψ) :
    (disappear hψ l r).1.leader = l.leader ∧
      (disappear hψ l r).2.leader = r.leader :=
  ⟨disappear_l_leader hψ l r, disappear_r_leader hψ l r⟩

/-- The final COMPARE dispatch frames both leader bits. -/
theorem compareSigDispatch_leaders_eq (l r : AgentState ψ) :
    (compareSigDispatch hψ l r).1.leader = l.leader ∧
      (compareSigDispatch hψ l r).2.leader = r.leader :=
  ⟨compareSigDispatch_l_leader hψ l r,
    compareSigDispatch_r_leader hψ l r⟩

/-- Literal COMPARE frames both leader bits. -/
theorem compareSig_leaders_eq (l r : AgentState ψ) :
    (compareSig hψ l r).1.leader = l.leader ∧
      (compareSig hψ l r).2.leader = r.leader :=
  ⟨compareSig_l_leader hψ l r, compareSig_r_leader hψ l r⟩

/-- SUPPRESS_SIG frames both leader bits. -/
theorem suppressSig_leaders_eq (l r : AgentState ψ) :
    (suppressSig hψ l r).1.leader = l.leader ∧
      (suppressSig hψ l r).2.leader = r.leader :=
  ⟨suppressSig_l_leader hψ l r, suppressSig_r_leader hψ l r⟩

/-- WRITE_SEQ preserves an existing initiator leader. -/
theorem writeSeq_initiator_leader_of_true (l r : AgentState ψ)
    (hl : l.leader = true) : (writeSeq hψ l r).1.leader = true :=
  writeSeq_l_leader_of_true hψ l r hl

/-- WRITE_SEQ preserves a responder leader hosted at label zero. -/
theorem writeSeq_responder_leader_of_label_zero (l r : AgentState ψ)
    (hr : r.leader = true) (hrLabel : r.label = ⟨0, hψ⟩) :
    (writeSeq hψ l r).2.leader = true := by
  rw [writeSeq_r_leader_of_label_zero hψ l r hrLabel, hr]

/-- Algorithm 19 frames both leader bits. -/
theorem writeAction_leaders_eq (l r : AgentState ψ) :
    (writeAction hψ l r).1.leader = l.leader ∧
      (writeAction hψ l r).2.leader = r.leader :=
  ⟨writeAction_l_leader hψ l r, writeAction_r_leader hψ l r⟩

/-- Algorithm 20 frames both leader bits. -/
theorem moveWsig_leaders_eq (l r : AgentState ψ) :
    (moveWsig hψ l r).1.leader = l.leader ∧
      (moveWsig hψ l r).2.leader = r.leader :=
  ⟨moveWsig_l_leader hψ l r, moveWsig_r_leader hψ l r⟩

/-- Algorithm 15 never changes the responder's leader bit. -/
theorem eliminateLeaders_responder_leader_eq (l r : AgentState ψ) :
    (eliminateLeaders hψ l r).2.leader = r.leader :=
  eliminateLeaders_r_leader hψ l r

/-! ## Why there is no ProtocolProperties instance for ppll

**Five fields are verified by standalone, sorry-free theorems:**
- `ppll_no_new_barrier`
- `ppll_leader_responder_stable`
- `ppll_leader_initiator_stable`
- `ppll_leader_destruction_requires_bullet_no_shield`
- `ppll_shield_removed_only_by_dummy`

There is deliberately no `ProtocolProperties` instance for concrete `ppll`.
Several remaining class fields are false, not merely difficult to elaborate:
`reset_cmd_stable`, `quiescent_stable`, and comparison-leader blocking all
have concrete counterexamples.  Installing a sorry-backed instance would make
the conditional closedness theorem appear to apply to a transition that does
not satisfy its hypotheses.  `Leader.Wu.Safety.Counterexamples` instead records a
machine-checked failure of the literal five-condition predicate and motivates
the reachable-signal-coherence invariant still needed for faithful closedness.
-/

end PPLLVerify
