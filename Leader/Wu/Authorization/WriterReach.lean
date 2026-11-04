import Leader.Wu.Authorization.BitFrozenClosure
/-! Reaching half of Z-div stage 2: the writer word `W_wr = D ++ F*` drives a leaderless,
perfectly labelled AuthF ring into `LeaderlessBitFrozen`.

Every served edge of a leaderless run is `writeSeq` on inputs with the original writer
projection (`PPLLAuthBitFrozen.served_pair`, restated here as `step_pair`), so the arguments
below are about `writeSeq`. Words: `E(g,k) = cell g k` (position `gψ+k`),
`B_g = bE g` (position `gψ+n-1 mod n`), `D_g = dW g 0 = E(g,0),…,E(g,ψ-2),E(g,ψ-2)`,
`D = wD m`, `F_g = fW g = E(g,0), B_g, D_g`, `F*_g = fS g (ψ-1)`, `F* = wFS m`,
`W_wr = wWr m = D ++ F*`, the same sequence as `ZZSimClaims.wordDFStar m ψ n`;
`wWr_length`: `|W_wr| = n + (n/ψ)(ψ-1)(ψ+2)`.

## Part 1: Phase D (`phaseD`)

Along a leaderless run of `D` every cell ends with `write = none`. A forward edge clears the
initiator's command and hands the responder at most the initiator's command
(`writeSeq_internal`); the doubled terminal edge hands the terminal the already-cleared
command. No `NoInc` hypothesis is needed.

## Part 2: one group (`fStar_secures`)

From a leaderless, perfectly labelled ring with no pending `increment_group` command, a
leaderless run of `F*_g` leaves group `g` secured (`SecG`: `TerminalSafe` at the terminal,
or no `HeadOW` at the head and no pending overwrite in the group) and all its cells `NoInc`.
One attempt (`attemptF`): `E(g,0)` leaves the head with `write_state ≠ depart`; if the head
still satisfies `HeadOW` then `B_g` creates `write = overwrite` there (`prepare_creates`);
`D_g` carries it forward (`move_carry`) unless `CheckLast` deletes a `path3` at the carrier
(`sweepF`); an arriving command is executed by the doubled terminal edge, which leaves the
terminal `TerminalSafe`. Deletion at the head kills `HeadOW`; deletion at an interior cell
lowers `icnt`, the number of interior `path3` holders (at most `ψ-2`), which never rises
(`path3` is never created on a leaderless `NoInc` row). So `ψ-1` attempts suffice.

## Part 3: composition (`writer_reach`)

Phase D gives `NoInc` on commands; each `F*_g` secures group `g`; security of a group is
closed under every leaderless `NoInc` edge (`secG_step`). Hence, unless some prefix of
`W_wr` produces a leader, the endpoint satisfies `LBF` and `PL`. Hypotheses: `2 ≤ ψ`,
`ψ ∣ n`, `1 < n`; no reset/echo or `inProtocolDomain` hypothesis is used.
-/

namespace PPLLAuthWriterReach
open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard
  PPLLFableDesignR1 PPLLAstraDesign2 PPLLAstraDesign3 PPLLAuthF PPLLAuthResetDrain
  PPLLAuthWriterFrame PPLLAuthBitFrozen
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ### Writer-level lemmas without `NoInc` -/

section Local
variable {ψ : Nat} (hψ : ψ > 0)

theorem owS_basic (r : AgentState ψ) :
    (owS r).label = r.label ∧ (owS r).leader = r.leader ∧ (owS r).write = r.write := by
  unfold owS writeActionApplyOverwrite
  split
  · split
    · exact ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩

theorem mfS_basic (r : AgentState ψ) :
    (mfS r).label = r.label ∧ (mfS r).leader = r.leader ∧ (mfS r).write = r.write := by
  unfold mfS writeActionApplyMoveFlip
  split
  · split
    · exact ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩

theorem incS_basic (r : AgentState ψ) :
    (incS r).label = r.label ∧ (incS r).leader = r.leader ∧ (incS r).write = r.write := by
  unfold incS
  split
  · split
    · exact ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩

theorem activate_id (u : AgentState ψ) (h : u.label.val ≠ ψ - 1) :
    writeActionActivate hψ u = u := by
  unfold writeActionActivate
  rw [if_neg]
  intro he
  exact h (by rw [he])

/-- Algorithm 19 with no hypothesis: labels and leaders are kept, the initiator keeps
`bit`/`path3`, and a non-terminal keeps its command. -/
theorem writeAction_gen (l r : AgentState ψ) :
    (writeAction hψ l r).1.label = l.label ∧ (writeAction hψ l r).1.leader = l.leader ∧
    (writeAction hψ l r).1.bit = l.bit ∧ (writeAction hψ l r).1.path3 = l.path3 ∧
    (l.label.val ≠ ψ - 1 → (writeAction hψ l r).1.write = l.write) ∧
    (writeAction hψ l r).2.label = r.label ∧ (writeAction hψ l r).2.leader = r.leader ∧
    (r.label.val ≠ ψ - 1 → (writeAction hψ l r).2.write = r.write) := by
  rw [writeAction_eq_staged]
  unfold writeActionStaged
  obtain ⟨la1, la2, la3, la4, _, _, _⟩ := activate_facts hψ l
  obtain ⟨_, _, ra3, ra4, _, _, _⟩ := activate_facts hψ r
  have hlw : l.label.val ≠ ψ - 1 → (writeActionActivate hψ l).write = l.write := by
    intro h; rw [activate_id hψ l h]
  have hrw : r.label.val ≠ ψ - 1 → (writeActionActivate hψ r).write = r.write := by
    intro h; rw [activate_id hψ r h]
  generalize writeActionActivate hψ l = l1 at la1 la2 la3 la4 hlw ⊢
  generalize writeActionActivate hψ r = r1 at ra3 ra4 hrw ⊢
  by_cases hc : l1.label < r1.label ∨ r1.label = ⟨0, hψ⟩
  · rw [execute_eq hψ l1 r1 hc]
    obtain ⟨o1, o2, o3⟩ := owS_basic r1
    obtain ⟨m1, m2, m3⟩ := mfS_basic (owS r1)
    obtain ⟨i1, i2, i3⟩ := incS_basic (mfS (owS r1))
    have hr1 : (incS (mfS (owS r1))).label = r.label := i1.trans (m1.trans (o1.trans ra3))
    have hr2 : (incS (mfS (owS r1))).leader = r.leader := i2.trans (m2.trans (o2.trans ra4))
    have hr3 : r.label.val ≠ ψ - 1 → (incS (mfS (owS r1))).write = r.write :=
      fun h => i3.trans (m3.trans (o3.trans (hrw h)))
    split
    · exact ⟨la3, la4, la1, la2, hlw, hr1, hr2, hr3⟩
    · exact ⟨la3, la4, la1, la2, hlw, hr1, hr2, hr3⟩
  · unfold writeActionExecute
    rw [if_neg hc]
    exact ⟨la3, la4, la1, la2, hlw, ra3, ra4, hrw⟩

theorem transfer_gen (l r : AgentState ψ) :
    ((moveWsigTransfer l r).1.write = l.write ∨ (moveWsigTransfer l r).1.write = .none) ∧
    (moveWsigTransfer l r).1.label = l.label ∧ (moveWsigTransfer l r).1.leader = l.leader ∧
    (moveWsigTransfer l r).2.label = r.label ∧ (moveWsigTransfer l r).2.leader = r.leader ∧
    (moveWsigTransfer l r).2.write = r.write := by
  unfold moveWsigTransfer
  repeat' (first | (dsimp only) | split)
  all_goals first
    | exact ⟨Or.inl rfl, rfl, rfl, rfl, rfl, rfl⟩
    | exact ⟨Or.inr rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Algorithm 20 on a forward edge: the initiator's command is cleared and the responder
receives at most the initiator's command. -/
theorem moveWsig_internal (l r : AgentState ψ) (hr : r.leader = false)
    (hlt : l.label < r.label) :
    (moveWsig hψ l r).1.write = .none ∧
    ((moveWsig hψ l r).2.write = l.write ∨ (moveWsig hψ l r).2.write = .none) := by
  rw [moveWsig_eq_staged]
  unfold moveWsigStaged
  dsimp only
  rw [start_id l r hr]
  dsimp only
  obtain ⟨_, _, k3, _, k5, _⟩ := checkLast_facts l
  obtain ⟨t1, t2, _, t4, _, t6⟩ := transfer_gen (moveWsigCheckLast l) r
  generalize moveWsigCheckLast l = l1 at k3 k5 t1 t2 t4 t6 ⊢
  generalize moveWsigTransfer l1 r = q at t1 t2 t4 t6 ⊢
  obtain ⟨l2, r2⟩ := q
  dsimp only at t1 t2 t4 t6 ⊢
  unfold moveWsigFinish
  dsimp only
  have hlt2 : l2.label < r2.label := by rw [t2, t4, k3]; exact hlt
  have hmw : moveWsigMoveWrite l2 r2 =
      ({ l2 with write := .none }, { r2 with write := l2.write }) := by
    unfold moveWsigMoveWrite; rw [if_pos hlt2]
  rw [hmw]
  dsimp only
  have f1 := leaderSignal_frame { l2 with write := .none } { r2 with write := l2.write }
  generalize moveWsigLeaderSignal { l2 with write := .none } { r2 with write := l2.write } = q2
    at f1 ⊢
  obtain ⟨l3, r3⟩ := q2
  obtain ⟨⟨_, _, a3, _, _, _⟩, ⟨_, _, b3, _, _, _⟩⟩ := f1
  dsimp only at a3 b3 ⊢
  have f2 := signalMove_frame l3 r3
  generalize moveWsigSignalMove l3 r3 = q3 at f2 ⊢
  obtain ⟨l4, r4⟩ := q3
  obtain ⟨⟨_, _, c3, _, _, _⟩, ⟨_, _, e3, _, _, _⟩⟩ := f2
  dsimp only at c3 e3 ⊢
  obtain ⟨⟨_, _, d3, _, _, _⟩, ⟨_, _, h3, _, _, _⟩⟩ := echoMove_frame l4 r4
  refine ⟨by rw [d3, c3, a3], ?_⟩
  rw [h3, e3, b3]
  rcases t1 with h | h
  · rw [h]; exact k5
  · right; exact h

/-- **Phase-D writer step.** On a leaderless forward edge the initiator ends with no
command and the responder with at most the initiator's command. -/
theorem writeSeq_internal (h2 : 2 ≤ ψ) (a b : AgentState ψ) (ha : a.leader = false)
    (hb : b.leader = false) (hlt : a.label < b.label) :
    (writeSeq hψ a b).1.write = .none ∧
    ((writeSeq hψ a b).2.write = a.write ∨ (writeSeq hψ a b).2.write = .none) := by
  rw [writeSeq_eq_afterPrepare]
  unfold writeSeqThroughPrepare writeSeqAfterPrepare
  dsimp only
  rw [leaderMove_id hψ a b hb]
  dsimp only
  have hg := groupInfo_frame hψ a b
  generalize groupInfo hψ a b = g at hg
  obtain ⟨a1, b1⟩ := g
  obtain ⟨⟨g1, g2, g3, g4, g5, g6⟩, ⟨g7, g8, g9, g10, g11, g12⟩⟩ := hg
  dsimp only at g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 ⊢
  rw [generate_id hψ a1 b1 (g6.trans ha)]
  dsimp only
  have hp := prepare_facts hψ h2 a1 b1
  dsimp only at hp
  generalize writeSeqPrepare hψ a1 b1 = p at hp
  obtain ⟨a4, b4⟩ := p
  obtain ⟨⟨p1, p2, p3, p4, p5, p6⟩, ⟨p7, p8, p9, p10, _, _, _, _, _, _, _⟩⟩ := hp
  dsimp only at p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 ⊢
  have hw := writeAction_gen hψ a4 b4
  generalize writeAction hψ a4 b4 = w at hw
  obtain ⟨a5, b5⟩ := w
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8⟩ := hw
  dsimp only at w1 w2 w3 w4 w5 w6 w7 w8 ⊢
  have hlt5 : a5.label < b5.label := by rw [w1, w6, p3, p9, g5, g11]; exact hlt
  have hnt : a4.label.val ≠ ψ - 1 := by
    rw [p3, g5]
    have hb' := b.label.isLt
    rw [Fin.lt_def] at hlt
    exact fun h => by omega
  obtain ⟨m1, m2⟩ := moveWsig_internal hψ a5 b5 (by rw [w7, p10, g12, hb]) hlt5
  refine ⟨m1, ?_⟩
  rw [w5 hnt, p5, g3] at m2
  exact m2

/-! ### Writer-level lemmas under `NoInc` (for the `F*` phase) -/

theorem tsc_of_map {u v : AgentState ψ} (hb : u.bit = v.bit)
    (hp : ∀ p', u.path3 = some p' → ∃ p, v.path3 = some p ∧ p'.bit = p.bit) (hv : TSc v) :
    TSc u := by
  intro p' hp'
  obtain ⟨p, hp0, hpb⟩ := hp p' hp'
  rw [hb, hv p hp0, hpb]

theorem owS_id (r : AgentState ψ) (h : r.write_state ≠ .overwrite) : owS r = r := by
  unfold owS; rw [if_neg h]

theorem mfS_id (r : AgentState ψ) (h : r.write_state ≠ .move_flip) : mfS r = r := by
  unfold mfS; rw [if_neg h]

/-- An executed overwrite leaves the cell `TerminalSafe`. -/
theorem owS_tsc (r : AgentState ψ) (h : r.write_state = .overwrite) : TSc (owS r) := by
  unfold owS
  rw [if_pos h]
  unfold writeActionApplyOverwrite
  split
  · next p hp =>
    intro p' hp'
    dsimp only at hp'
    obtain rfl := Option.some.inj hp'
    rfl
  · next hp =>
    intro p' hp'
    rw [hp] at hp'
    cases hp'

theorem owS_gen (r : AgentState ψ) :
    (owS r).write_state = r.write_state ∧ ((owS r).bit = r.bit ∨ TSc (owS r)) ∧
    (∀ p', (owS r).path3 = some p' → ∃ p, r.path3 = some p ∧ p'.bit = p.bit) := by
  by_cases h : r.write_state = .overwrite
  · refine ⟨?_, Or.inr (owS_tsc r h), ?_⟩
    · unfold owS writeActionApplyOverwrite
      rw [if_pos h]
      split
      · rfl
      · rfl
    · intro p' hp'
      unfold owS writeActionApplyOverwrite at hp'
      rw [if_pos h] at hp'
      split at hp'
      · next p hp =>
        dsimp only at hp'
        obtain rfl := Option.some.inj hp'
        exact ⟨p, hp, rfl⟩
      · exact ⟨p', hp', rfl⟩
  · rw [owS_id r h]
    exact ⟨rfl, Or.inl rfl, fun p' hp' => ⟨p', hp', rfl⟩⟩

/-- Algorithm 19 on a prepared leaderless pair (no terminal-safety hypothesis). -/
theorem action_ni (l r : AgentState ψ)
    (hlr : l.label < r.label ∨ r.label = ⟨0, hψ⟩)
    (hlws : l.write_state = .ready ∨ l.write_state = .none)
    (hrws : r.write_state ≠ .depart ∧ r.write_state ≠ .overwrite ∧
      r.write_state ≠ .move_flip ∧ r.write_state ≠ .increment_group)
    (hlw : l.write ≠ .increment_group) (hrw : r.write ≠ .increment_group) :
    ((writeAction hψ l r).1.bit = l.bit ∧ (writeAction hψ l r).1.path3 = l.path3 ∧
      (writeAction hψ l r).1.label = l.label ∧ (writeAction hψ l r).1.leader = l.leader ∧
      ((writeAction hψ l r).1.write = l.write ∨ (writeAction hψ l r).1.write = .none) ∧
      (l.label.val ≠ ψ - 1 → (writeAction hψ l r).1.write = l.write) ∧
      (writeAction hψ l r).1.write_state ≠ .depart ∧
      (writeAction hψ l r).1.write_state ≠ .increment_group) ∧
    ((writeAction hψ l r).2.label = r.label ∧ (writeAction hψ l r).2.leader = r.leader ∧
      (r.label.val ≠ ψ - 1 → (writeAction hψ l r).2.bit = r.bit ∧
        (writeAction hψ l r).2.path3 = r.path3 ∧ (writeAction hψ l r).2.write = r.write) ∧
      ((writeAction hψ l r).2.bit = r.bit ∨ TSc (writeAction hψ l r).2) ∧
      (∀ p', (writeAction hψ l r).2.path3 = some p' →
        ∃ p, r.path3 = some p ∧ p'.bit = p.bit) ∧
      ((writeAction hψ l r).2.write = r.write ∨ (writeAction hψ l r).2.write = .none) ∧
      (writeAction hψ l r).2.write_state = .depart ∧
      (r.label.val = ψ - 1 → r.write = .overwrite → TSc (writeAction hψ l r).2)) := by
  rw [writeAction_eq_staged]
  unfold writeActionStaged
  obtain ⟨la1, la2, la3, la4, la5, la6, la7⟩ := activate_facts hψ l
  obtain ⟨ra1, ra2, ra3, ra4, ra5, ra6, ra7⟩ := activate_facts hψ r
  have hlr1 : (writeActionActivate hψ l).label < (writeActionActivate hψ r).label ∨
      (writeActionActivate hψ r).label = ⟨0, hψ⟩ := by rw [la3, ra3]; exact hlr
  have hl1ws : (writeActionActivate hψ l).write_state ≠ .depart ∧
      (writeActionActivate hψ l).write_state ≠ .increment_group := by
    by_cases ht : l.label.val = ψ - 1
    · rw [la7 ht]; exact ⟨toState_ne_depart _, toState_ne_inc hlw⟩
    · rw [la6 ht]; rcases hlws with h | h <;> rw [h] <;> simp
  have hr1ws : (writeActionActivate hψ r).write_state ≠ .depart ∧
      (writeActionActivate hψ r).write_state ≠ .increment_group := by
    by_cases ht : r.label.val = ψ - 1
    · rw [ra7 ht]; exact ⟨toState_ne_depart _, toState_ne_inc hrw⟩
    · rw [ra6 ht]; exact ⟨hrws.1, hrws.2.2.2⟩
  have hlw1 : l.label.val ≠ ψ - 1 → (writeActionActivate hψ l).write = l.write :=
    fun h => by rw [activate_id hψ l h]
  have hr1nt : r.label.val ≠ ψ - 1 → writeActionActivate hψ r = r := activate_id hψ r
  have hr1ow : r.label.val = ψ - 1 → r.write = .overwrite →
      (writeActionActivate hψ r).write_state = .overwrite := fun ht hw => by rw [ra7 ht, hw]; rfl
  generalize writeActionActivate hψ l = l1 at la1 la2 la3 la4 la5 la6 la7 hlr1 hl1ws hlw1 ⊢
  generalize writeActionActivate hψ r = r1 at ra1 ra2 ra3 ra4 ra5 ra6 ra7 hlr1 hr1ws hr1nt hr1ow ⊢
  rw [execute_eq hψ l1 r1 hlr1]
  obtain ⟨o1, o2, o3⟩ := owS_gen r1
  obtain ⟨ob1, ob2, ob3⟩ := owS_basic r1
  obtain ⟨m1, m2, m3, m4, m5, m6, m7⟩ := mfS_facts (owS r1)
  have hinc : incS (mfS (owS r1)) = mfS (owS r1) :=
    incS_id _ (by rw [m5, o1]; exact hr1ws.2)
  rw [hinc]
  have hws3 : (mfS (owS r1)).write_state = r1.write_state := m5.trans o1
  have hmap3 : ∀ p', (mfS (owS r1)).path3 = some p' → ∃ p, r.path3 = some p ∧ p'.bit = p.bit := by
    intro p' hp'
    obtain ⟨p1, hp1, e1, _⟩ := m7 p' hp'
    obtain ⟨p0, hp0, e3⟩ := o3 p1 hp1
    exact ⟨p0, by rw [← ra2]; exact hp0, e1.trans e3⟩
  have hbit3 : (mfS (owS r1)).bit = r.bit ∨ TSc (mfS (owS r1)) := by
    rcases o2 with h | h
    · left; rw [m1, h, ra1]
    · right
      refine tsc_of_map m1 ?_ h
      intro p' hp'
      obtain ⟨p1, hp1, e1, _⟩ := m7 p' hp'
      exact ⟨p1, hp1, e1⟩
  have hnt3 : r.label.val ≠ ψ - 1 → (mfS (owS r1)).bit = r.bit ∧
      (mfS (owS r1)).path3 = r.path3 ∧ (mfS (owS r1)).write = r.write := by
    intro ht
    rw [hr1nt ht, owS_id r hrws.2.1, mfS_id r hrws.2.2.1]
    exact ⟨rfl, rfl, rfl⟩
  have htow3 : r.label.val = ψ - 1 → r.write = .overwrite → TSc (mfS (owS r1)) := by
    intro ht hw
    have h1 := owS_tsc r1 (hr1ow ht hw)
    refine tsc_of_map m1 ?_ h1
    intro p' hp'
    obtain ⟨p1, hp1, e1, _⟩ := m7 p' hp'
    exact ⟨p1, hp1, e1⟩
  have hw3 : (mfS (owS r1)).write = r.write ∨ (mfS (owS r1)).write = .none := by
    rw [m4, ob3]; exact ra5
  have hl3 : (mfS (owS r1)).label = r.label := m2.trans (ob1.trans ra3)
  have hd3 : (mfS (owS r1)).leader = r.leader := m3.trans (ob2.trans ra4)
  generalize mfS (owS r1) = r3 at hws3 hmap3 hbit3 hnt3 htow3 hw3 hl3 hd3 ⊢
  have hrp : (r3.label.val ≠ ψ - 1 → r3.bit = r.bit ∧ r3.path3 = r.path3 ∧ r3.write = r.write) ∧
      (r3.bit = r.bit ∨ TSc r3) ∧
      (∀ p', r3.path3 = some p' → ∃ p, r.path3 = some p ∧ p'.bit = p.bit) ∧
      (r3.write = r.write ∨ r3.write = .none) ∧
      (r.label.val = ψ - 1 → r.write = .overwrite → TSc r3) :=
    ⟨fun h => hnt3 (by rw [← hl3]; exact h), hbit3, hmap3, hw3, htow3⟩
  obtain ⟨q1, q2, q3, q4, q5⟩ := hrp
  split
  · refine ⟨⟨la1, la2, la3, la4, la5, hlw1, ?_, ?_⟩,
      ⟨hl3, hd3, fun h => q1 (by rw [hl3]; exact h), q2, q3, q4, rfl, q5⟩⟩
    · show r3.write_state ≠ _; rw [hws3]; exact hr1ws.1
    · show r3.write_state ≠ _; rw [hws3]; exact hr1ws.2
  · exact ⟨⟨la1, la2, la3, la4, la5, hlw1, hl1ws.1, hl1ws.2⟩,
      ⟨hl3, hd3, fun h => q1 (by rw [hl3]; exact h), q2, q3, q4, rfl, q5⟩⟩

theorem checkLast_cases (l : AgentState ψ) :
    moveWsigCheckLast l = l ∨
      ((∃ p, l.path3 = some p) ∧ (moveWsigCheckLast l).path3 = none) := by
  unfold moveWsigCheckLast
  split
  · next p hp =>
    split
    · right; exact ⟨⟨p, hp⟩, rfl⟩
    · left; rfl
  · left; rfl

/-- Algorithm 20 on a forward edge: the initiator's command reaches the responder unless
`CheckLast` deleted the initiator's `path3`. -/
theorem move_carry (l r : AgentState ψ) (hr : r.leader = false)
    (hws : l.write_state ≠ .depart) (hlt : l.label < r.label) :
    (moveWsig hψ l r).2.write = l.write ∨
      ((∃ p, l.path3 = some p) ∧ (moveWsig hψ l r).1.path3 = none) := by
  rw [moveWsig_eq_staged]
  unfold moveWsigStaged
  dsimp only
  rw [start_id l r hr]
  dsimp only
  obtain ⟨_, _, k3, _, _, k6⟩ := checkLast_facts l
  have hk : (moveWsigCheckLast l).write_state ≠ .depart := by
    rcases k6 with h | h <;> rw [h]
    · exact hws
    · simp
  have hcl := checkLast_cases l
  rw [transfer_id _ r hk]
  dsimp only
  generalize moveWsigCheckLast l = l1 at k3 hk hcl ⊢
  unfold moveWsigFinish
  dsimp only
  have hlt2 : l1.label < r.label := by rw [k3]; exact hlt
  have hmw : moveWsigMoveWrite l1 r =
      ({ l1 with write := .none }, { r with write := l1.write }) := by
    unfold moveWsigMoveWrite; rw [if_pos hlt2]
  rw [hmw]
  dsimp only
  have f1 := leaderSignal_frame { l1 with write := .none } { r with write := l1.write }
  generalize moveWsigLeaderSignal { l1 with write := .none } { r with write := l1.write } = q2
    at f1 ⊢
  obtain ⟨l3, r3⟩ := q2
  obtain ⟨⟨_, a2, _, _, _, _⟩, ⟨_, _, b3, _, _, _⟩⟩ := f1
  dsimp only at a2 b3 ⊢
  have f2 := signalMove_frame l3 r3
  generalize moveWsigSignalMove l3 r3 = q3 at f2 ⊢
  obtain ⟨l4, r4⟩ := q3
  obtain ⟨⟨_, c2, _, _, _, _⟩, ⟨_, _, e3, _, _, _⟩⟩ := f2
  dsimp only at c2 e3 ⊢
  obtain ⟨⟨_, d2, _, _, _, _⟩, ⟨_, _, h3, _, _, _⟩⟩ := echoMove_frame l4 r4
  rw [h3, e3, b3, d2, c2, a2]
  rcases hcl with h | ⟨hp, h⟩
  · left; rw [h]
  · right; exact ⟨hp, h⟩

theorem ready_of_how (r : AgentState ψ) (h0 : r.label.val = 0) (p : Path3Info)
    (hp : r.path3 = some p) (hpl : p.label = 0) (hws : r.write_state ≠ .depart) :
    writeSeqSetWriteReady r = { r with write_state := .ready } := by
  unfold writeSeqSetWriteReady
  split
  · next p' hp' =>
    rw [hp] at hp'
    obtain rfl := Option.some.inj hp'
    rw [if_pos ⟨by rw [h0, hpl], hws⟩]
  · next hp' => rw [hp] at hp'; cases hp'

theorem compare_larger (l r : AgentState ψ) (h0 : r.label.val = 0)
    (hr : r.write_state = .ready) (p : Path3Info) (hp : r.path3 = some p) (hb : r.bit = true)
    (hpb : p.bit = 0) (hle : l.write_state ≠ .equal) :
    (writeSeqCompare hψ l r).2.write_state = .larger ∧
    (writeSeqCompare hψ l r).2.path3 = r.path3 ∧ (writeSeqCompare hψ l r).2.label = r.label := by
  have hc : writeSeqCheckBit r = { r with write_state := .larger } := by
    unfold writeSeqCheckBit
    split
    · next p' hp' =>
      rw [hp] at hp'
      obtain rfl := Option.some.inj hp'
      rw [hb, hpb]; rfl
    · next hp' => rw [hp] at hp'; cases hp'
  unfold writeSeqCompare
  dsimp only
  rw [if_pos (show r.label = ⟨0, hψ⟩ ∧ r.write_state = .ready from ⟨Fin.ext h0, hr⟩), hc]
  split
  · next h => exact absurd h.2.1 hle
  · exact ⟨rfl, rfl, rfl⟩

theorem act_larger (u : AgentState ψ) (hws : u.write_state = .larger) (p : Path3Info)
    (hp : u.path3 = some p) (hpf : p.flag = 1) :
    (writeSeqSetWriteAct u).write = .overwrite ∧ (writeSeqSetWriteAct u).label = u.label := by
  unfold writeSeqSetWriteAct
  dsimp only
  rw [if_pos hws]
  split
  · next p' hp' =>
    rw [hp] at hp'
    obtain rfl := Option.some.inj hp'
    rw [if_pos hpf]
    split
    · next h => exact absurd (hws.symm.trans h) (by simp)
    · exact ⟨rfl, rfl⟩
  · next hp' => rw [hp] at hp'; cases hp'

/-- **Overwrite creation.** A label-0 responder satisfying `HeadOW` whose `write_state` is
not `depart` leaves command preparation with `write = overwrite`. -/
theorem prepare_creates (h2 : 2 ≤ ψ) (l r : AgentState ψ) (h0 : r.label.val = 0)
    (hh : HOWc r) (hws : r.write_state ≠ .depart) :
    (writeSeqPrepare hψ l r).2.write = .overwrite := by
  obtain ⟨p, hp, hpl, hpf, hb, hpb⟩ := hh
  have hle : (writeSeqSetWriteReady l).write_state ≠ .equal := by
    rcases (ready_facts l).2.2.2.2.2.1 with h | h <;> rw [h] <;> simp
  have hR := ready_of_how r h0 p hp hpl hws
  unfold writeSeqPrepare writeSeqReady
  dsimp only
  rw [hR]
  obtain ⟨c1, c2, c3⟩ := compare_larger hψ (writeSeqSetWriteReady l)
    { r with write_state := .ready } h0 rfl p hp hb hpb hle
  generalize writeSeqCompare hψ (writeSeqSetWriteReady l) { r with write_state := .ready } = q
    at c1 c2 c3
  obtain ⟨l2, r2⟩ := q
  dsimp only at c1 c2 c3 ⊢
  unfold writeSeqCommands
  dsimp only
  obtain ⟨a1, a2⟩ := act_larger r2 c1 p (by rw [c2]; exact hp) hpf
  generalize writeSeqSetWriteAct r2 = r3 at a1 a2 ⊢
  rw [if_neg]
  · exact a1
  · intro h
    have hv := congrArg Fin.val h.1
    rw [a2, c3] at hv
    have hv' : r.label.val = ψ - 1 := hv
    omega

/-- **Leaderless `writeSeq` under `NoInc`**, all facts used by the `F*` phase. -/
theorem writeSeq_ni (h2 : 2 ≤ ψ) (a b : AgentState ψ) (ha : a.leader = false)
    (hb : b.leader = false) (hlab : b.label.val = (a.label.val + 1) % ψ)
    (haw : a.write ≠ .increment_group) (hbw : b.write ≠ .increment_group) :
    (writeSeq hψ a b).1.bit = a.bit ∧
    ((writeSeq hψ a b).1.path3 = a.path3 ∨ (writeSeq hψ a b).1.path3 = none) ∧
    ((writeSeq hψ a b).2.bit = b.bit ∨ TSc (writeSeq hψ a b).2) ∧
    (b.label.val ≠ ψ - 1 → (writeSeq hψ a b).2.bit = b.bit ∧
      (writeSeq hψ a b).2.path3 = b.path3) ∧
    (∀ p', (writeSeq hψ a b).2.path3 = some p' → ∃ p, b.path3 = some p ∧ p'.bit = p.bit) ∧
    NIc (writeSeq hψ a b).1 ∧ NIc (writeSeq hψ a b).2 ∧
    (writeSeq hψ a b).1.write_state ≠ .depart ∧
    ((writeSeq hψ a b).1.write = .overwrite → a.write = .overwrite) ∧
    ((writeSeq hψ a b).2.write = .overwrite → (b.label.val ≠ 0 ∧ a.write = .overwrite) ∨
      (b.label.val = 0 ∧ (b.write = .overwrite ∨ HOWc b))) ∧
    (b.label.val ≠ 0 → a.write = .overwrite → (writeSeq hψ a b).2.write = .overwrite ∨
      ((∃ p, a.path3 = some p) ∧ (writeSeq hψ a b).1.path3 = none)) ∧
    (b.label.val ≠ 0 → b.label.val = ψ - 1 → b.write = .overwrite →
      TSc (writeSeq hψ a b).2) ∧
    (b.label.val = 0 → HOWc b → b.write_state ≠ .depart →
      (writeSeq hψ a b).2.write = .overwrite) := by
  rw [writeSeq_eq_afterPrepare]
  unfold writeSeqThroughPrepare writeSeqAfterPrepare
  dsimp only
  rw [leaderMove_id hψ a b hb]
  dsimp only
  have hg := groupInfo_frame hψ a b
  generalize groupInfo hψ a b = g at hg
  obtain ⟨a1, b1⟩ := g
  obtain ⟨⟨g1, g2, g3, g4, g5, g6⟩, ⟨g7, g8, g9, g10, g11, g12⟩⟩ := hg
  dsimp only at g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 ⊢
  rw [generate_id hψ a1 b1 (g6.trans ha)]
  dsimp only
  have hcre : b.label.val = 0 → HOWc b → b.write_state ≠ .depart →
      (writeSeqPrepare hψ a1 b1).2.write = .overwrite := by
    intro h0 hh hws
    apply prepare_creates hψ h2 a1 b1 (by rw [g11]; exact h0)
    · obtain ⟨p, hp, x1, x2, x3, x4⟩ := hh
      exact ⟨p, by rw [g8]; exact hp, x1, x2, by rw [g7]; exact x3, x4⟩
    · rw [g10]; exact hws
  have hp := prepare_facts hψ h2 a1 b1
  dsimp only at hp
  generalize writeSeqPrepare hψ a1 b1 = p at hp hcre
  obtain ⟨a4, b4⟩ := p
  obtain ⟨⟨p1, p2, p3, p4, p5, p6⟩, ⟨p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17⟩⟩ := hp
  dsimp only at p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 hcre ⊢
  have hlt : a.label < b.label ↔ b.label.val ≠ 0 := by
    have hal := a.label.isLt
    rw [Fin.lt_def]
    by_cases hc : a.label.val + 1 < ψ
    · rw [hlab, Nat.mod_eq_of_lt hc]
      exact ⟨fun _ => Nat.succ_ne_zero _, fun _ => Nat.lt_succ_self _⟩
    · have : a.label.val + 1 = ψ := Nat.le_antisymm hal (Nat.le_of_not_lt hc)
      rw [hlab, this, Nat.mod_self]
      exact ⟨fun h => absurd h (Nat.not_lt_zero _), fun h => absurd rfl h⟩
  have hlr : a4.label < b4.label ∨ b4.label = ⟨0, hψ⟩ := by
    rw [p3, p9, g5, g11]
    by_cases hz : b.label.val = 0
    · right; exact Fin.ext hz
    · left; exact hlt.2 hz
  have hw4 : b4.write ≠ .increment_group := p15 (by rw [g9]; exact hbw)
  have hact := action_ni hψ a4 b4 hlr p6 ⟨p11, p12, p13, p14⟩ (by rw [p5, g3]; exact haw) hw4
  generalize writeAction hψ a4 b4 = w at hact
  obtain ⟨a5, b5⟩ := w
  obtain ⟨⟨w1, w2, w3, w4, w5, w5', w6, w7⟩, ⟨w8, w9, w10, w11, w12, w13, w14, w15⟩⟩ := hact
  dsimp only at w1 w2 w3 w4 w5 w5' w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 ⊢
  have hlt5 : a5.label < b5.label ↔ b.label.val ≠ 0 := by
    rw [Fin.lt_def, w3, w8, p3, p9, g5, g11, ← Fin.lt_def]; exact hlt
  have hcarry : b.label.val ≠ 0 → a.write = .overwrite →
      (moveWsig hψ a5 b5).2.write = .overwrite ∨
        ((∃ p, a.path3 = some p) ∧ (moveWsig hψ a5 b5).1.path3 = none) := by
    intro hz hw
    have hant : a4.label.val ≠ ψ - 1 := by
      rw [p3, g5]
      have hb' := b.label.isLt
      have := hlt.2 hz
      rw [Fin.lt_def] at this
      exact fun h => by clear hlt hlt5; omega
    rcases move_carry hψ a5 b5 (by rw [w9, p10, g12, hb]) w6 (hlt5.2 hz) with h | ⟨hp, h⟩
    · left; rw [h, w5' hant, p5, g3, hw]
    · right; rw [w2, p2, g2] at hp; exact ⟨hp, h⟩
  have hm := move_facts hψ a5 b5 (by rw [w9, p10, g12, hb]) w6
  dsimp only at hm
  generalize moveWsig hψ a5 b5 = m at hm hcarry
  obtain ⟨a6, b6⟩ := m
  obtain ⟨⟨m1, m2, m3, m4, m5, m6⟩, ⟨m7, m8, m9, m10, m11, m12, m13⟩⟩ := hm
  dsimp only at m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 hcarry ⊢
  have hb6map : ∀ p', b6.path3 = some p' → ∃ p, b.path3 = some p ∧ p'.bit = p.bit := by
    intro p' hp'
    rw [m8] at hp'
    obtain ⟨p, hp, hb1⟩ := w12 p' hp'
    exact ⟨p, by rw [← g8, ← p8]; exact hp, hb1⟩
  refine ⟨?_, ?_, ?_, ?_, hb6map, ?_, ?_, ?_, ?_, ?_, hcarry, ?_, ?_⟩
  · rw [m1, w1, p1, g1]
  · rcases m2 with h | h
    · left; rw [h, w2, p2, g2]
    · right; exact h
  · rcases w11 with h | h
    · left; rw [m7, h, p7, g7]
    · right
      exact tsc_of_map m7 (fun p' hp' => ⟨p', by rw [← m8]; exact hp', rfl⟩) h
  · intro hnt
    obtain ⟨x1, x2, _⟩ := w10 (by rw [p9, g11]; exact hnt)
    exact ⟨by rw [m7, x1, p7, g7], by rw [m8, x2, p8, g8]⟩
  · constructor
    · rcases m5 with h | h
      · rw [h]; rcases w5 with h' | h'
        · rw [h', p5, g3]; exact haw
        · rw [h']; simp
      · rw [h]; simp
    · rcases m6 with h | h
      · rw [h]; exact w7
      · rw [h]; simp
  · constructor
    · by_cases hz : b.label.val = 0
      · rw [m12 (by rw [hlt5]; exact fun h => h hz)]
        rcases w13 with h | h
        · rw [h]; exact hw4
        · rw [h]; simp
      · rcases m11 (hlt5.2 hz) with h | h
        · rw [h]; rcases w5 with h' | h'
          · rw [h', p5, g3]; exact haw
          · rw [h']; simp
        · rw [h]; simp
    · rw [m13, w14]; simp
  · rcases m6 with h | h
    · rw [h]; exact w6
    · rw [h]; simp
  · intro h
    rcases m5 with h1 | h1
    · rw [h1] at h; rcases w5 with h' | h'
      · rw [h', p5, g3] at h; exact h
      · rw [h'] at h; cases h
    · rw [h1] at h; cases h
  · intro h
    by_cases hz : b.label.val = 0
    · right
      refine ⟨hz, ?_⟩
      rw [m12 (by rw [hlt5]; exact fun h => h hz)] at h
      rcases w13 with h' | h'
      · rw [h'] at h
        rcases p16 h with h'' | ⟨_, hh⟩
        · left; rw [← g9]; exact h''
        · right
          obtain ⟨p, hp, x1, x2, x3, x4⟩ := hh
          exact ⟨p, by rw [← g8]; exact hp, x1, x2, by rw [← g7]; exact x3, x4⟩
      · rw [h'] at h; cases h
    · left
      refine ⟨hz, ?_⟩
      rcases m11 (hlt5.2 hz) with h' | h'
      · rw [h'] at h; rcases w5 with h'' | h''
        · rw [h'', p5, g3] at h; exact h
        · rw [h''] at h; cases h
      · rw [h'] at h; cases h
  · intro hz ht hw
    have hz1 : b1.label.val ≠ 0 := by rw [g11]; exact hz
    have hw' : b4.write = .overwrite := by rw [p17 hz1, g9, hw]
    have hts := w15 (by rw [p9, g11]; exact ht) hw'
    exact tsc_of_map m7 (fun p' hp' => ⟨p', by rw [← m8]; exact hp', rfl⟩) hts
  · intro h0 hh hws
    have hc := hcre h0 hh hws
    have hnt : b4.label.val ≠ ψ - 1 := by
      rw [p9, g11, h0]
      exact Nat.ne_of_lt (Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le Nat.one_lt_two h2))
    rw [m12 (by rw [hlt5]; exact fun h => h h0), (w10 hnt).2.2, hc]

end Local

/-! ### Ring bookkeeping -/

section Ring
variable {n ψ : Nat}

theorem authRun_append (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (w1 w2 : List (Fin n)) : ∀ C : Fin n → AuthState ψ,
    authRun hp κ c ring C (w1 ++ w2) = authRun hp κ c ring (authRun hp κ c ring C w1) w2 := by
  induction w1 with
  | nil => intro C; rfl
  | cons e es ih => intro C; exact ih _

theorem authRun_cons (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (C : Fin n → AuthState ψ) (e : Fin n) (es : List (Fin n)) :
    authRun hp κ c ring C (e :: es) = authRun hp κ c ring (S hp κ c ring C e) es := rfl

theorem authRun_nil (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (C : Fin n → AuthState ψ) : authRun hp κ c ring C [] = C := rfl

/-- Every intermediate configuration of the run is leaderless. -/
def LLRun (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n) :
    (Fin n → AuthState ψ) → List (Fin n) → Prop
  | _, [] => True
  | C, e :: es => (∀ i, (S hp κ c ring C e i).core.leader = false) ∧
      LLRun hp κ c ring (S hp κ c ring C e) es

theorem LLRun_append (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (w1 w2 : List (Fin n)) : ∀ C : Fin n → AuthState ψ,
    LLRun hp κ c ring C (w1 ++ w2) ↔
      LLRun hp κ c ring C w1 ∧ LLRun hp κ c ring (authRun hp κ c ring C w1) w2 := by
  induction w1 with
  | nil => intro C; exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | cons e es ih =>
    intro C
    show (_ ∧ LLRun hp κ c ring _ (es ++ w2)) ↔ (_ ∧ _) ∧ _
    rw [ih]
    exact ⟨fun ⟨a, b, d⟩ => ⟨⟨a, b⟩, d⟩, fun ⟨⟨a, b⟩, d⟩ => ⟨a, b, d⟩⟩

/-- Leaderless with perfect labels. -/
def Good (C : Fin n → AuthState ψ) : Prop := (∀ i, (C i).core.leader = false) ∧ PL C

private theorem neighbor_ne (ring : DirectedRing n) (hn : 1 < n) (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro h
  have he := congrArg Fin.val h
  change (e.val + 1) % n = e.val at he
  by_cases hk : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hk] at he; omega
  · have hlast : e.val + 1 = n := by omega
    rw [hlast, Nat.mod_self] at he; omega

private theorem step_left (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (C : Fin n → AuthState ψ) (e : Fin n) :
    S hp κ c ring C e e = (PPLLAuthF.pipeline hp κ c (C e) (C (ring.rightNeighbor e))).1 := by
  simp [S, PopulationProtocol.step, authProtocol]

private theorem step_right (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (hn : 1 < n) (C : Fin n → AuthState ψ) (e : Fin n) :
    S hp κ c ring C e (ring.rightNeighbor e) =
      (PPLLAuthF.pipeline hp κ c (C e) (C (ring.rightNeighbor e))).2 := by
  have ne := neighbor_ne ring hn e
  simp [S, PopulationProtocol.step, authProtocol, ne]

theorem step_other (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (C : Fin n → AuthState ψ) (e i : Fin n) (h1 : i ≠ e) (h2 : i ≠ ring.rightNeighbor e) :
    S hp κ c ring C e i = C i := by
  simp [S, PopulationProtocol.step, authProtocol, h1, h2]

/-- A run whose edges never touch cell `i` leaves it unchanged. -/
theorem run_untouched (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (i : Fin n) : ∀ (w : List (Fin n)) (C : Fin n → AuthState ψ),
    (∀ e ∈ w, i ≠ e ∧ i ≠ ring.rightNeighbor e) → authRun hp κ c ring C w i = C i := by
  intro w
  induction w with
  | nil => intro C _; rfl
  | cons e es ih =>
    intro C h
    show authRun hp κ c ring (S hp κ c ring C e) es i = C i
    rw [ih _ (fun e' he' => h e' (List.mem_cons_of_mem _ he'))]
    obtain ⟨h1, h2⟩ := h e List.mem_cons_self
    exact step_other hp κ c ring C e i h1 h2

private theorem kernel_label_eq {a : AgentState ψ} {x : AgentState ψ} (h : wp a = wp x) :
    a.bit = x.bit ∧ a.path3 = x.path3 ∧ a.write = x.write ∧ a.write_state = x.write_state := by
  simp only [wp, Prod.mk.injEq] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

theorem wp_fields4 {a x : AgentState ψ} (h : wp a = wp x) :
    a.bit = x.bit ∧ a.path3 = x.path3 ∧ a.write = x.write ∧ a.write_state = x.write_state :=
  kernel_label_eq h

/-- **One served edge of a leaderless run.** The served pair is `writeSeq` on inputs with the
original writer projection and labels; the successor is again leaderless with perfect labels. -/
theorem step_pair (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (hd : ψ ∣ n) (hn : 1 < n) (C : Fin n → AuthState ψ) (hG : Good C) (e : Fin n)
    (hout : ∀ i, (S hp κ c ring C e i).core.leader = false) :
    Good (S hp κ c ring C e) ∧
    (∀ i, i ≠ e → i ≠ ring.rightNeighbor e → S hp κ c ring C e i = C i) ∧
    ∃ a b : AgentState ψ, wp a = wp (C e).core ∧ wp b = wp (C (ring.rightNeighbor e)).core ∧
      a.label = (C e).core.label ∧ b.label = (C (ring.rightNeighbor e)).core.label ∧
      a.leader = false ∧ b.leader = false ∧
      (S hp κ c ring C e e).core = (writeSeq hp a b).1 ∧
      (S hp κ c ring C e (ring.rightNeighbor e)).core = (writeSeq hp a b).2 := by
  have hDe := step_left hp κ c ring C e
  have hDe' := step_right hp κ c ring hn C e
  have hDo := step_other hp κ c ring C e
  have hne := neighbor_ne ring hn e
  have he'v : (ring.rightNeighbor e).val = (e.val + 1) % n := rfl
  have hlabv : (C (ring.rightNeighbor e)).core.label.val = ((C e).core.label.val + 1) % ψ := by
    rw [hG.2 _, hG.2 e, he'v]; exact succ_mod_of_dvd hd e.val
  have hnext : (C (ring.rightNeighbor e)).core.label =
      ⟨((C e).core.label.val + 1) % ψ, Nat.mod_lt _ hp⟩ := Fin.ext hlabv
  obtain ⟨a, b, hwa, hwb, hla, hlb, hal, hbl, hq1, hq2⟩ :=
    served_pair hp κ c (C e) (C (ring.rightNeighbor e)) (hG.1 e) (hG.1 _) hnext
      (by have := hout e; rw [hDe] at this; exact this)
      (by have := hout (ring.rightNeighbor e); rw [hDe'] at this; exact this)
  refine ⟨⟨hout, ?_⟩, fun i h1 h2 => hDo i h1 h2,
    a, b, hwa, hwb, hla, hlb, hal, hbl, by rw [hDe]; exact hq1, by rw [hDe']; exact hq2⟩
  intro i
  by_cases h1 : i = e
  · subst i
    rw [hDe, hq1, PPLLVerify.writeSeq_l_label, hla]; exact hG.2 e
  · by_cases h2 : i = ring.rightNeighbor e
    · subst i
      rw [hDe', hq2, PPLLVerify.writeSeq_r_label, hlb]; exact hG.2 _
    · rw [hDo i h1 h2]; exact hG.2 i

theorem good_run (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (hd : ψ ∣ n) (hn : 1 < n) : ∀ (w : List (Fin n)) (C : Fin n → AuthState ψ),
    Good C → LLRun hp κ c ring C w → Good (authRun hp κ c ring C w) := by
  intro w
  induction w with
  | nil => intro C hG _; exact hG
  | cons e es ih =>
    intro C hG hL
    exact ih _ (step_pair hp κ c ring hd hn C hG e hL.1).1 hL.2

/-! ### Cells and words -/

/-- Cell `k` of group `g`, i.e. physical position `gψ+k` (mod `n`). -/
def cell (ring : DirectedRing n) (ψ g k : Nat) : Fin n := ⟨(g * ψ + k) % n, Nat.mod_lt _ ring.hn⟩

theorem rn_cell (ring : DirectedRing n) (ψ g k : Nat) :
    ring.rightNeighbor (cell ring ψ g k) = cell ring ψ g (k + 1) := by
  apply Fin.ext
  show ((g * ψ + k) % n + 1) % n = (g * ψ + (k + 1)) % n
  rw [Nat.add_mod ((g * ψ + k) % n) 1 n, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]

theorem cell_val (ring : DirectedRing n) {m g k : Nat} (hmn : n = m * ψ) (hg : g < m)
    (hk : k < ψ) : (cell ring ψ g k).val = g * ψ + k := by
  show (g * ψ + k) % n = g * ψ + k
  apply Nat.mod_eq_of_lt
  have := Nat.mul_le_mul_right ψ (Nat.succ_le_of_lt hg)
  rw [Nat.succ_mul] at this
  omega

theorem cell_mod (g k : Nat) (hk : k < ψ) : (g * ψ + k) % ψ = k := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]

theorem cell_label (ring : DirectedRing n) {m g k : Nat} (hmn : n = m * ψ) (hg : g < m)
    (hk : k < ψ) {C : Fin n → AuthState ψ} (hpl : PL C) :
    (C (cell ring ψ g k)).core.label.val = k := by
  rw [hpl, cell_val ring hmn hg hk, cell_mod g k hk]

theorem cell_ne (ring : DirectedRing n) {m g g' k k' : Nat} (hmn : n = m * ψ) (hg : g < m)
    (hg' : g' < m) (hk : k < ψ) (hk' : k' < ψ) (h : g ≠ g' ∨ k ≠ k') :
    cell ring ψ g k ≠ cell ring ψ g' k' := by
  intro he
  have hv := congrArg Fin.val he
  rw [cell_val ring hmn hg hk, cell_val ring hmn hg' hk'] at hv
  rcases Nat.lt_trichotomy g g' with hlt | heq | hgt
  · have := Nat.mul_le_mul_right ψ (Nat.succ_le_of_lt hlt)
    rw [Nat.succ_mul] at this
    omega
  · subst heq
    rcases h with h | h
    · exact h rfl
    · omega
  · have := Nat.mul_le_mul_right ψ (Nat.succ_le_of_lt hgt)
    rw [Nat.succ_mul] at this
    omega

/-- `D_g` from cell `j` on: `E(g,j), …, E(g,ψ-2), E(g,ψ-2)`. -/
def dW (ring : DirectedRing n) (ψ g j : Nat) : List (Fin n) :=
  (List.range' j (ψ - 1 - j)).map (cell ring ψ g) ++ [cell ring ψ g (ψ - 2)]

theorem dW_cons (ring : DirectedRing n) (g j : Nat) (hj : j < ψ - 2) :
    dW ring ψ g j = cell ring ψ g j :: dW ring ψ g (j + 1) := by
  unfold dW
  rw [show ψ - 1 - j = (ψ - 1 - (j + 1)) + 1 by omega]
  rfl

theorem dW_last (ring : DirectedRing n) (g : Nat) (h2 : 2 ≤ ψ) :
    dW ring ψ g (ψ - 2) = [cell ring ψ g (ψ - 2), cell ring ψ g (ψ - 2)] := by
  unfold dW
  rw [show ψ - 1 - (ψ - 2) = 1 by omega]
  rfl

/-- `D = D_0 ++ … ++ D_(t-1)`. -/
def wD (ring : DirectedRing n) (ψ : Nat) : Nat → List (Fin n)
  | 0 => []
  | t + 1 => wD ring ψ t ++ dW ring ψ t 0

/-- `D_g` from cell `j` touches only cells `j … ψ-1` of group `g`. -/
theorem dW_untouched (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (h2 : 2 ≤ ψ) (g : Nat) (i : Fin n) :
    ∀ d j, j + d = ψ - 2 → (∀ k, j ≤ k → k ≤ ψ - 1 → i ≠ cell ring ψ g k) →
    ∀ X : Fin n → AuthState ψ, authRun hp κ c ring X (dW ring ψ g j) i = X i := by
  intro d
  induction d with
  | zero =>
    intro j hj hi X
    have hj' : j = ψ - 2 := by omega
    subst hj'
    apply run_untouched
    intro e he
    rw [dW_last ring g h2] at he
    have he' : e = cell ring ψ g (ψ - 2) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at he; exact he
    subst he'
    rw [rn_cell]
    exact ⟨hi _ (Nat.le_refl _) (by omega), by rw [show ψ - 2 + 1 = ψ - 1 by omega]; exact hi _ (by omega) (Nat.le_refl _)⟩
  | succ d ih =>
    intro j hj hi X
    rw [dW_cons ring g j (by omega)]
    show authRun hp κ c ring (S hp κ c ring X (cell ring ψ g j)) (dW ring ψ g (j + 1)) i = X i
    rw [ih (j + 1) (by omega) (fun k hk hk' => hi k (by omega) hk')]
    apply step_other
    · exact hi j (Nat.le_refl _) (by omega)
    · rw [rn_cell]; exact hi (j + 1) (by omega) (by omega)

/-- **Phase D, one group.** Along a leaderless run of `D_g` from cell `j`, cells
`j … ψ-1` of group `g` end with no command. -/
theorem sweepD (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (h2 : 2 ≤ ψ) (hd : ψ ∣ n) (hn : 1 < n) {m : Nat} (hmn : n = m * ψ) (g : Nat) (hg : g < m) :
    ∀ d j, j + d = ψ - 2 → ∀ X : Fin n → AuthState ψ, Good X →
    LLRun hp κ c ring X (dW ring ψ g j) →
    ∀ k, j ≤ k → k < ψ →
      (authRun hp κ c ring X (dW ring ψ g j) (cell ring ψ g k)).core.write = .none := by
  -- the served forward edge `E(g,k)`
  have fwd : ∀ (X : Fin n → AuthState ψ) (k : Nat), k ≤ ψ - 2 → Good X →
      (∀ i, (S hp κ c ring X (cell ring ψ g k) i).core.leader = false) →
      Good (S hp κ c ring X (cell ring ψ g k)) ∧
      (S hp κ c ring X (cell ring ψ g k) (cell ring ψ g k)).core.write = .none ∧
      ((S hp κ c ring X (cell ring ψ g k) (cell ring ψ g (k + 1))).core.write =
          (X (cell ring ψ g k)).core.write ∨
        (S hp κ c ring X (cell ring ψ g k) (cell ring ψ g (k + 1))).core.write = .none) ∧
      (∀ i, i ≠ cell ring ψ g k → i ≠ cell ring ψ g (k + 1) →
        S hp κ c ring X (cell ring ψ g k) i = X i) := by
    intro X k hk hG hout
    obtain ⟨hG', hoth, a, b, hwa, hwb, hla, hlb, hal, hbl, hq1, hq2⟩ :=
      step_pair hp κ c ring hd hn X hG (cell ring ψ g k) hout
    rw [rn_cell] at hwb hlb hq2 hoth
    have hlt : a.label < b.label := by
      rw [Fin.lt_def, hla, hlb, cell_label ring hmn hg (by omega) hG.2,
        cell_label ring hmn hg (by omega) hG.2]
      omega
    obtain ⟨i1, i2⟩ := writeSeq_internal hp h2 a b hal hbl hlt
    obtain ⟨_, _, fa3, _⟩ := wp_fields4 hwa
    refine ⟨hG', by rw [hq1]; exact i1, ?_, hoth⟩
    rw [hq2, ← fa3]; exact i2
  intro d
  induction d with
  | zero =>
    intro j hj X hG hL k hk hk'
    have hj' : j = ψ - 2 := by omega
    subst hj'
    rw [dW_last ring g h2] at hL ⊢
    obtain ⟨hout1, hout2, _⟩ := hL
    obtain ⟨hG1, n1, _, _⟩ := fwd X (ψ - 2) (Nat.le_refl _) hG hout1
    obtain ⟨_, n2, n3, _⟩ := fwd _ (ψ - 2) (Nat.le_refl _) hG1 hout2
    show (S hp κ c ring (S hp κ c ring X (cell ring ψ g (ψ - 2))) (cell ring ψ g (ψ - 2))
      (cell ring ψ g k)).core.write = .none
    rcases Nat.lt_or_ge k (ψ - 1) with hk1 | hk1
    · have : k = ψ - 2 := by omega
      subst this; exact n2
    · have : k = ψ - 2 + 1 := by omega
      subst this
      rcases n3 with h | h
      · rw [h]; exact n1
      · exact h
  | succ d ih =>
    intro j hj X hG hL k hk hk'
    rw [dW_cons ring g j (by omega)] at hL ⊢
    obtain ⟨hout1, hL1⟩ := hL
    obtain ⟨hG1, n1, _, _⟩ := fwd X j (by omega) hG hout1
    show (authRun hp κ c ring (S hp κ c ring X (cell ring ψ g j)) (dW ring ψ g (j + 1))
      (cell ring ψ g k)).core.write = .none
    rcases Nat.lt_or_ge j k with hjk | hjk
    · exact ih (j + 1) (by omega) _ hG1 hL1 k hjk hk'
    · have : k = j := by omega
      subst this
      rw [dW_untouched hp κ c ring h2 g _ d (k + 1) (by omega) ?_]
      · exact n1
      · intro k' hk1 hk2
        exact cell_ne ring hmn hg hg (by omega) (by omega) (Or.inr (by omega))

/-- **Phase D.** Along a leaderless run of `D = D_0 ++ … ++ D_(t-1)` (`t ≤ m`), every cell of
the first `t` groups ends with `write = none`. -/
theorem phaseD_groups (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (h2 : 2 ≤ ψ) (hd : ψ ∣ n) (hn : 1 < n) {m : Nat} (hmn : n = m * ψ) :
    ∀ t, t ≤ m → ∀ X : Fin n → AuthState ψ, Good X → LLRun hp κ c ring X (wD ring ψ t) →
    ∀ g k, g < t → k < ψ →
      (authRun hp κ c ring X (wD ring ψ t) (cell ring ψ g k)).core.write = .none := by
  intro t
  induction t with
  | zero => intro _ X _ _ g k hg; exact absurd hg (Nat.not_lt_zero _)
  | succ t ih =>
    intro ht X hG hL g k hg hk
    show (authRun hp κ c ring X (wD ring ψ t ++ dW ring ψ t 0) (cell ring ψ g k)).core.write = _
    have hL' := (LLRun_append hp κ c ring _ _ X).1 hL
    rw [authRun_append]
    have hGt := good_run hp κ c ring hd hn _ X hG hL'.1
    rcases Nat.lt_or_ge g t with hgt | hgt
    · rw [dW_untouched hp κ c ring h2 t _ (ψ - 2) 0 (by omega) ?_]
      · exact ih (by omega) X hG hL'.1 g k hgt hk
      · intro k' _ hk2
        exact cell_ne ring hmn (by omega) (by omega) hk (by omega) (Or.inl (by omega))
    · have : g = t := by omega
      subst this
      exact sweepD hp κ c ring h2 hd hn hmn g (by omega) (ψ - 2) 0 (by omega) _ hGt hL'.2 k
        (Nat.zero_le _) hk

/-- Every cell is some `cell g k` with `g < m`, `k < ψ`. -/
theorem cell_cover (ring : DirectedRing n) {m : Nat} (hp : ψ > 0) (hmn : n = m * ψ) (i : Fin n) :
    i.val / ψ < m ∧ i.val % ψ < ψ ∧ cell ring ψ (i.val / ψ) (i.val % ψ) = i := by
  have e1 := Nat.div_add_mod i.val ψ
  have hlt := i.isLt
  have hmod := Nat.mod_lt i.val hp
  have hq : i.val / ψ < m := by
    rcases Nat.lt_or_ge (i.val / ψ) m with h | h
    · exact h
    · exfalso
      have := Nat.mul_le_mul_left ψ h
      rw [Nat.mul_comm ψ m] at this
      omega
  refine ⟨hq, hmod, Fin.ext ?_⟩
  rw [cell_val ring hmn hq hmod, Nat.mul_comm]
  omega

/-- **Phase D (headline).** Along a leaderless run of the whole `D` from a leaderless ring
with perfect labels, every cell ends with `write = none`, and the endpoint is again
leaderless with perfect labels. -/
theorem phaseD (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (h2 : 2 ≤ ψ) (hd : ψ ∣ n) (hn : 1 < n) {m : Nat} (hmn : n = m * ψ)
    (X : Fin n → AuthState ψ) (hG : Good X) (hL : LLRun hp κ c ring X (wD ring ψ m)) :
    Good (authRun hp κ c ring X (wD ring ψ m)) ∧
    ∀ i, (authRun hp κ c ring X (wD ring ψ m) i).core.write = .none := by
  refine ⟨good_run hp κ c ring hd hn _ X hG hL, fun i => ?_⟩
  obtain ⟨hq, hr, hi⟩ := cell_cover ring hp hmn i
  rw [← hi]
  exact phaseD_groups hp κ c ring h2 hd hn hmn m (Nat.le_refl _) X hG hL _ _ hq hr

/-! ## Part 2: one group under `F*_g` -/

/-- No pending `increment_group` command anywhere. -/
def NIw (C : Fin n → AuthState ψ) : Prop := ∀ i, (C i).core.write ≠ .increment_group

theorem how_transfer {a x : AgentState ψ} (hb : a.bit = x.bit) (hp : a.path3 = x.path3)
    (h : HOWc a) : HOWc x := by
  obtain ⟨p, h1, x1, x2, x3, x4⟩ := h
  exact ⟨p, by rw [← hp]; exact h1, x1, x2, by rw [← hb]; exact x3, x4⟩

/-- **One served edge under `NoInc`**, in the fields of the original configuration. -/
theorem step_ni (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (h2 : 2 ≤ ψ) (hd : ψ ∣ n) (hn : 1 < n) (C : Fin n → AuthState ψ) (hG : Good C)
    (hN : NIw C) (e : Fin n) (hout : ∀ i, (S hp κ c ring C e i).core.leader = false) :
    Good (S hp κ c ring C e) ∧ NIw (S hp κ c ring C e) ∧
    (∀ i, i ≠ e → i ≠ ring.rightNeighbor e → S hp κ c ring C e i = C i) ∧
    -- initiator
    (S hp κ c ring C e e).core.bit = (C e).core.bit ∧
    ((S hp κ c ring C e e).core.path3 = (C e).core.path3 ∨
      (S hp κ c ring C e e).core.path3 = none) ∧
    NIc (S hp κ c ring C e e).core ∧
    (S hp κ c ring C e e).core.write_state ≠ .depart ∧
    ((S hp κ c ring C e e).core.write = .overwrite → (C e).core.write = .overwrite) ∧
    -- responder
    ((S hp κ c ring C e (ring.rightNeighbor e)).core.bit = (C (ring.rightNeighbor e)).core.bit ∨
      TSc (S hp κ c ring C e (ring.rightNeighbor e)).core) ∧
    ((C (ring.rightNeighbor e)).core.label.val ≠ ψ - 1 →
      (S hp κ c ring C e (ring.rightNeighbor e)).core.bit = (C (ring.rightNeighbor e)).core.bit ∧
      (S hp κ c ring C e (ring.rightNeighbor e)).core.path3 =
        (C (ring.rightNeighbor e)).core.path3) ∧
    (∀ p', (S hp κ c ring C e (ring.rightNeighbor e)).core.path3 = some p' →
      ∃ p, (C (ring.rightNeighbor e)).core.path3 = some p ∧ p'.bit = p.bit) ∧
    NIc (S hp κ c ring C e (ring.rightNeighbor e)).core ∧
    ((S hp κ c ring C e (ring.rightNeighbor e)).core.write = .overwrite →
      ((C (ring.rightNeighbor e)).core.label.val ≠ 0 ∧ (C e).core.write = .overwrite) ∨
      ((C (ring.rightNeighbor e)).core.label.val = 0 ∧
        ((C (ring.rightNeighbor e)).core.write = .overwrite ∨
          HOWc (C (ring.rightNeighbor e)).core))) ∧
    ((C (ring.rightNeighbor e)).core.label.val ≠ 0 → (C e).core.write = .overwrite →
      (S hp κ c ring C e (ring.rightNeighbor e)).core.write = .overwrite ∨
      ((∃ p, (C e).core.path3 = some p) ∧ (S hp κ c ring C e e).core.path3 = none)) ∧
    ((C (ring.rightNeighbor e)).core.label.val ≠ 0 →
      (C (ring.rightNeighbor e)).core.label.val = ψ - 1 →
      (C (ring.rightNeighbor e)).core.write = .overwrite →
      TSc (S hp κ c ring C e (ring.rightNeighbor e)).core) ∧
    ((C (ring.rightNeighbor e)).core.label.val = 0 → HOWc (C (ring.rightNeighbor e)).core →
      (C (ring.rightNeighbor e)).core.write_state ≠ .depart →
      (S hp κ c ring C e (ring.rightNeighbor e)).core.write = .overwrite) := by
  obtain ⟨hG', hoth, a, b, hwa, hwb, hla, hlb, hal, hbl, hq1, hq2⟩ :=
    step_pair hp κ c ring hd hn C hG e hout
  have hne := neighbor_ne ring hn e
  have hlabv : b.label.val = (a.label.val + 1) % ψ := by
    rw [hla, hlb, hG.2 _, hG.2 e]
    show (e.val + 1) % n % ψ = _
    exact succ_mod_of_dvd hd e.val
  obtain ⟨fa1, fa2, fa3, fa4⟩ := wp_fields4 hwa
  obtain ⟨fb1, fb2, fb3, fb4⟩ := wp_fields4 hwb
  obtain ⟨W1, W2, W3, W4, W5, W6, W7, W8, W9, W10, W11, W12, W13⟩ :=
    writeSeq_ni hp h2 a b hal hbl hlabv (by rw [fa3]; exact hN e) (by rw [fb3]; exact hN _)
  rw [← hq1, ← hq2] at *
  rw [fa1] at W1
  rw [fa2] at W2
  rw [fb1] at W3
  rw [hlb, fb1, fb2] at W4
  rw [fb2] at W5
  rw [fa3] at W9
  rw [hlb, fa3, fb3] at W10
  rw [hlb, fa3, fa2] at W11
  rw [hlb, fb3] at W12
  rw [hlb, fb4] at W13
  refine ⟨hG', ?_, hoth, W1, W2, W6, W8, W9, W3, W4, W5, W7, ?_, W11, W12, ?_⟩
  · intro i
    by_cases h1 : i = e
    · subst i; exact W6.1
    · by_cases h2' : i = ring.rightNeighbor e
      · subst i; exact W7.1
      · rw [hoth i h1 h2']; exact hN i
  · intro hw
    rcases W10 hw with h | ⟨h0, h | h⟩
    · exact Or.inl h
    · exact Or.inr ⟨h0, Or.inl h⟩
    · exact Or.inr ⟨h0, Or.inr (how_transfer fb1 fb2 h)⟩
  · intro h0 hh hws
    exact W13 h0 (how_transfer fb1.symm fb2.symm hh) hws

/-- Per-cell persistence along one served edge. -/
theorem step_persist (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (h2 : 2 ≤ ψ) (hd : ψ ∣ n) (hn : 1 < n) (C : Fin n → AuthState ψ) (hG : Good C)
    (hN : NIw C) (e : Fin n) (hout : ∀ i, (S hp κ c ring C e i).core.leader = false)
    (i : Fin n) :
    (TSc (C i).core → TSc (S hp κ c ring C e i).core) ∧
    ((C i).core.path3 = none → (S hp κ c ring C e i).core.path3 = none) ∧
    ((C i).core.label.val ≠ ψ - 1 → HOWc (S hp κ c ring C e i).core → HOWc (C i).core) ∧
    (NIc (C i).core → NIc (S hp κ c ring C e i).core) := by
  obtain ⟨-, -, hoth, L1, L2, L3, -, -, R1, R2, R3, R4, -, -, -, -⟩ :=
    step_ni hp κ c ring h2 hd hn C hG hN e hout
  by_cases h1 : i = e
  · subst i
    refine ⟨?_, ?_, ?_, fun _ => L3⟩
    · intro hs p hp3
      rw [L1]
      rcases L2 with h | h
      · exact hs p (by rw [← h]; exact hp3)
      · rw [h] at hp3; cases hp3
    · intro hno
      rcases L2 with h | h
      · rw [h, hno]
      · exact h
    · intro _ hh
      obtain ⟨p, hp3, x1, x2, x3, x4⟩ := hh
      rcases L2 with h | h
      · exact ⟨p, by rw [← h]; exact hp3, x1, x2, by rw [← L1]; exact x3, x4⟩
      · rw [h] at hp3; cases hp3
  · by_cases h2' : i = ring.rightNeighbor e
    · subst i
      refine ⟨?_, ?_, ?_, fun _ => R4⟩
      · intro hs
        rcases R1 with hb | ht
        · refine tsc_of_map hb ?_ hs
          intro p' hp'
          exact R3 p' hp'
        · exact ht
      · intro hno
        cases h : (S hp κ c ring C e (ring.rightNeighbor e)).core.path3 with
        | none => rfl
        | some p' =>
          obtain ⟨p, hp0, -⟩ := R3 p' h
          rw [hno] at hp0; cases hp0
      · intro hnt hh
        obtain ⟨hb, hpa⟩ := R2 hnt
        exact how_transfer hb hpa hh
    · rw [hoth i h1 h2']
      exact ⟨id, id, fun _ => id, id⟩

/-- Invariants of a leaderless `NoInc` run. -/
theorem run_persist (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (h2 : 2 ≤ ψ) (hd : ψ ∣ n) (hn : 1 < n) : ∀ (w : List (Fin n)) (C : Fin n → AuthState ψ),
    Good C → NIw C → LLRun hp κ c ring C w →
    Good (authRun hp κ c ring C w) ∧ NIw (authRun hp κ c ring C w) ∧ ∀ i,
    (TSc (C i).core → TSc (authRun hp κ c ring C w i).core) ∧
    ((C i).core.path3 = none → (authRun hp κ c ring C w i).core.path3 = none) ∧
    ((C i).core.label.val ≠ ψ - 1 → HOWc (authRun hp κ c ring C w i).core → HOWc (C i).core) ∧
    (NIc (C i).core → NIc (authRun hp κ c ring C w i).core) := by
  intro w
  induction w with
  | nil => intro C hG hN _; exact ⟨hG, hN, fun i => ⟨id, id, fun _ => id, id⟩⟩
  | cons e es ih =>
    intro C hG hN hL
    obtain ⟨hG1, hN1, -⟩ := step_ni hp κ c ring h2 hd hn C hG hN e hL.1
    obtain ⟨hG2, hN2, hi⟩ := ih _ hG1 hN1 hL.2
    refine ⟨hG2, hN2, fun i => ?_⟩
    obtain ⟨s1, s2, s3, s4⟩ := step_persist hp κ c ring h2 hd hn C hG hN e hL.1 i
    obtain ⟨t1, t2, t3, t4⟩ := hi i
    have hlab : (S hp κ c ring C e i).core.label.val = (C i).core.label.val := by
      rw [hG1.2 i, hG.2 i]
    exact ⟨fun h => t1 (s1 h), fun h => t2 (s2 h),
      fun hnt hh => s3 hnt (t3 (by rw [hlab]; exact hnt) hh), fun h => t4 (s4 h)⟩

/-! ### Counting interior `path3` holders -/

/-- `cntB f K = #{j < K | f j}`. -/
def cntB (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => cntB f k + (f k).toNat

theorem cntB_le (f : Nat → Bool) : ∀ K, cntB f K ≤ K := by
  intro K
  induction K with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    show cntB f k + (f k).toNat ≤ k + 1
    have : (f k).toNat ≤ 1 := by
      cases f k
      · exact Nat.zero_le _
      · exact Nat.le_refl _
    omega

theorem toNat_mono {x y : Bool} (h : x = true → y = true) : x.toNat ≤ y.toNat := by
  cases x <;> cases y
  · exact Nat.le_refl _
  · exact Nat.zero_le _
  · exact absurd (h rfl) Bool.false_ne_true
  · exact Nat.le_refl _

theorem cntB_mono (f f' : Nat → Bool) : ∀ K, (∀ j, j < K → f' j = true → f j = true) →
    cntB f' K ≤ cntB f K := by
  intro K
  induction K with
  | zero => intro _; exact Nat.le_refl _
  | succ k ih =>
    intro h
    show cntB f' k + (f' k).toNat ≤ cntB f k + (f k).toNat
    have h1 := ih (fun j hj => h j (by omega))
    have h2 := toNat_mono (h k (Nat.lt_succ_self k))
    omega

theorem cntB_lt (f f' : Nat → Bool) : ∀ K, (∀ j, j < K → f' j = true → f j = true) →
    ∀ j0, j0 < K → f j0 = true → f' j0 = false → cntB f' K < cntB f K := by
  intro K
  induction K with
  | zero => intro _ j0 hj0; exact absurd hj0 (Nat.not_lt_zero _)
  | succ k ih =>
    intro h j0 hj0 hf hf'
    show cntB f' k + (f' k).toNat < cntB f k + (f k).toNat
    have h2 := toNat_mono (h k (Nat.lt_succ_self k))
    rcases Nat.lt_or_ge j0 k with hlt | hge
    · have h1 := ih (fun j hj => h j (by omega)) j0 hlt hf hf'
      omega
    · have : j0 = k := by omega
      subst this
      have h1 := cntB_mono f f' j0 (fun j hj => h j (by omega))
      rw [hf, hf']
      show cntB f' j0 + 0 < cntB f j0 + 1
      omega

/-- Number of interior cells `1 … ψ-2` of group `g` holding a `path3`. -/
def icnt (ring : DirectedRing n) (ψ g : Nat) (C : Fin n → AuthState ψ) : Nat :=
  cntB (fun j => ((C (cell ring ψ g (j + 1))).core.path3).isSome) (ψ - 2)

/-! ### Words `F_g` and `F*_g` -/

/-- `B_g`, the edge from the previous group's terminal into the head of `g`. -/
def bE (ring : DirectedRing n) (ψ g : Nat) : Fin n :=
  ⟨(g * ψ + n - 1) % n, Nat.mod_lt _ ring.hn⟩

theorem rn_bE (ring : DirectedRing n) (ψ g : Nat) :
    ring.rightNeighbor (bE ring ψ g) = cell ring ψ g 0 := by
  apply Fin.ext
  show ((g * ψ + n - 1) % n + 1) % n = (g * ψ + 0) % n
  have hpos := ring.hn
  rw [Nat.add_mod ((g * ψ + n - 1) % n) 1 n, Nat.mod_mod, ← Nat.add_mod,
    show g * ψ + n - 1 + 1 = g * ψ + 0 + n by omega, Nat.add_mod_right]

/-- `F_g = E(g,0), B_g, D_g`. -/
def fW (ring : DirectedRing n) (ψ g : Nat) : List (Fin n) :=
  cell ring ψ g 0 :: bE ring ψ g :: dW ring ψ g 0

/-- `F_g` repeated `r` times. -/
def fS (ring : DirectedRing n) (ψ g : Nat) : Nat → List (Fin n)
  | 0 => []
  | r + 1 => fS ring ψ g r ++ fW ring ψ g

theorem psi_sub_one_ne (h2 : 2 ≤ ψ) : ψ - 1 ≠ 0 :=
  Nat.ne_of_gt (Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le Nat.one_lt_two h2))

theorem fS_succ (ring : DirectedRing n) (ψ g r : Nat) :
    fS ring ψ g (r + 1) = fS ring ψ g r ++ fW ring ψ g := rfl

/-- **The sweep carries an overwrite to the terminal**, unless `CheckLast` deletes some
`path3` at or after the carrier's cell. -/
theorem sweepF (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (h2 : 2 ≤ ψ) (hd : ψ ∣ n) (hn : 1 < n) {m : Nat} (hmn : n = m * ψ) (g : Nat) (hg : g < m) :
    ∀ d j, j + d = ψ - 2 → ∀ X : Fin n → AuthState ψ, Good X → NIw X →
    LLRun hp κ c ring X (dW ring ψ g j) → (X (cell ring ψ g j)).core.write = .overwrite →
    TSc (authRun hp κ c ring X (dW ring ψ g j) (cell ring ψ g (ψ - 1))).core ∨
    ∃ k, j ≤ k ∧ k ≤ ψ - 2 ∧ (X (cell ring ψ g k)).core.path3.isSome = true ∧
      (authRun hp κ c ring X (dW ring ψ g j) (cell ring ψ g k)).core.path3 = none := by
  have fwd : ∀ (X : Fin n → AuthState ψ) (k : Nat), k ≤ ψ - 2 → Good X → NIw X →
      (∀ i, (S hp κ c ring X (cell ring ψ g k) i).core.leader = false) →
      (X (cell ring ψ g k)).core.write = .overwrite →
      (S hp κ c ring X (cell ring ψ g k) (cell ring ψ g (k + 1))).core.write = .overwrite ∨
      ((X (cell ring ψ g k)).core.path3.isSome = true ∧
        (S hp κ c ring X (cell ring ψ g k) (cell ring ψ g k)).core.path3 = none) := by
    intro X k hk hG hN hout hw
    have hk1 : k + 1 < ψ := by omega
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, R9, -, -⟩ :=
      step_ni hp κ c ring h2 hd hn X hG hN (cell ring ψ g k) hout
    rw [rn_cell] at R9
    rcases R9 (by rw [cell_label ring hmn hg hk1 hG.2]; exact Nat.succ_ne_zero _) hw with
      h | ⟨⟨p, hp3⟩, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨by rw [hp3]; rfl, h⟩
  have term : ∀ (X : Fin n → AuthState ψ), Good X → NIw X →
      (∀ i, (S hp κ c ring X (cell ring ψ g (ψ - 2)) i).core.leader = false) →
      (X (cell ring ψ g (ψ - 1))).core.write = .overwrite →
      TSc (S hp κ c ring X (cell ring ψ g (ψ - 2)) (cell ring ψ g (ψ - 1))).core := by
    intro X hG hN hout hw
    have e1 : ψ - 2 + 1 = ψ - 1 := by omega
    have e2 : ψ - 1 < ψ := by omega
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, R10, -⟩ :=
      step_ni hp κ c ring h2 hd hn X hG hN (cell ring ψ g (ψ - 2)) hout
    rw [rn_cell, e1] at R10
    have hl := cell_label ring hmn hg e2 hG.2
    exact R10 (by rw [hl]; exact psi_sub_one_ne h2) hl hw
  intro d
  induction d with
  | zero =>
    intro j hj X hG hN hL hw
    have hj' : j = ψ - 2 := by omega
    subst hj'
    rw [dW_last ring g h2] at hL ⊢
    obtain ⟨hout1, hout2, -⟩ := hL
    obtain ⟨hG1, hN1, -⟩ := step_ni hp κ c ring h2 hd hn X hG hN _ hout1
    rw [authRun_cons, authRun_cons, authRun_nil]
    rcases fwd X (ψ - 2) (Nat.le_refl _) hG hN hout1 hw with h | ⟨hs, hdel⟩
    · left
      rw [show ψ - 2 + 1 = ψ - 1 by omega] at h
      exact term _ hG1 hN1 hout2 h
    · right
      refine ⟨ψ - 2, Nat.le_refl _, Nat.le_refl _, hs, ?_⟩
      exact (step_persist hp κ c ring h2 hd hn _ hG1 hN1 _ hout2 _).2.1 hdel
  | succ d ih =>
    intro j hj X hG hN hL hw
    rw [dW_cons ring g j (by omega)] at hL ⊢
    obtain ⟨hout1, hL1⟩ := hL
    obtain ⟨hG1, hN1, -⟩ := step_ni hp κ c ring h2 hd hn X hG hN _ hout1
    rw [authRun_cons]
    rcases fwd X j (by omega) hG hN hout1 hw with h | ⟨hs, hdel⟩
    · rcases ih (j + 1) (by omega) _ hG1 hN1 hL1 h with h' | ⟨k, hk1, hk2, hs', hdel'⟩
      · exact Or.inl h'
      · right
        refine ⟨k, by omega, hk2, ?_, hdel'⟩
        cases hx : (X (cell ring ψ g k)).core.path3 with
        | some _ => rfl
        | none =>
          have := (step_persist hp κ c ring h2 hd hn X hG hN _ hout1 (cell ring ψ g k)).2.1 hx
          rw [this] at hs'; cases hs'
    · right
      refine ⟨j, Nat.le_refl _, by omega, hs, ?_⟩
      exact (run_persist hp κ c ring h2 hd hn _ _ hG1 hN1 hL1).2.2 _ |>.2.1 hdel

/-- Along a leaderless `NoInc` run of `D_g` from cell `j`, cells `j … ψ-1` of group `g`
end `NoInc` in both fields. -/
theorem sweepNIc (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (h2 : 2 ≤ ψ) (hd : ψ ∣ n) (hn : 1 < n) {m : Nat} (hmn : n = m * ψ) (g : Nat) (hg : g < m) :
    ∀ d j, j + d = ψ - 2 → ∀ X : Fin n → AuthState ψ, Good X → NIw X →
    LLRun hp κ c ring X (dW ring ψ g j) →
    ∀ k, j ≤ k → k < ψ → NIc (authRun hp κ c ring X (dW ring ψ g j) (cell ring ψ g k)).core := by
  intro d
  induction d with
  | zero =>
    intro j hj X hG hN hL k hk hk'
    have hj' : j = ψ - 2 := by omega
    subst hj'
    rw [dW_last ring g h2] at hL ⊢
    obtain ⟨hout1, hout2, -⟩ := hL
    obtain ⟨hG1, hN1, -⟩ := step_ni hp κ c ring h2 hd hn X hG hN _ hout1
    obtain ⟨-, -, -, -, -, n1, -, -, -, -, -, n2, -⟩ :=
      step_ni hp κ c ring h2 hd hn _ hG1 hN1 _ hout2
    rw [rn_cell] at n2
    rw [authRun_cons, authRun_cons, authRun_nil]
    rcases Nat.lt_or_ge k (ψ - 1) with hk1 | hk1
    · have : k = ψ - 2 := by omega
      subst this; exact n1
    · have : k = ψ - 2 + 1 := by omega
      subst this; exact n2
  | succ d ih =>
    intro j hj X hG hN hL k hk hk'
    rw [dW_cons ring g j (by omega)] at hL ⊢
    obtain ⟨hout1, hL1⟩ := hL
    obtain ⟨hG1, hN1, -, -, -, n1, -⟩ := step_ni hp κ c ring h2 hd hn X hG hN _ hout1
    rw [authRun_cons]
    rcases Nat.lt_or_ge j k with hjk | hjk
    · exact ih (j + 1) (by omega) _ hG1 hN1 hL1 k hjk hk'
    · have : k = j := by omega
      subst this
      rw [dW_untouched hp κ c ring h2 g _ d (k + 1) (by omega) ?_]
      · exact n1
      · intro k' hk1 hk2
        exact cell_ne ring hmn hg hg (by omega) (by omega) (Or.inr (by omega))

theorem arith_km1 (k K : Nat) (h0 : 0 < k) (h : k ≤ K) : k - 1 < K ∧ k - 1 + 1 = k := by
  constructor
  · omega
  · omega

theorem arith_step (a b c r : Nat) (h : a < b) (h' : b + r ≤ c) : a + (r + 1) ≤ c := by
  omega

theorem arith_final (a b ψ : Nat) (h2 : 2 ≤ ψ) (h : a + (ψ - 1) ≤ b) (hb : b ≤ ψ - 2) :
    False := by
  omega

/-- **One attempt `F_g`.** Afterwards every cell of group `g` has no command and is `NoInc`,
and if the head still satisfies `HeadOW` then the terminal is `TerminalSafe` or an interior
`path3` was consumed. -/
theorem attemptF (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (h2 : 2 ≤ ψ) (hd : ψ ∣ n) (hn : 1 < n) {m : Nat} (hmn : n = m * ψ) (g : Nat) (hg : g < m)
    (X : Fin n → AuthState ψ) (hG : Good X) (hN : NIw X)
    (hL : LLRun hp κ c ring X (fW ring ψ g)) :
    (∀ k, k < ψ → (authRun hp κ c ring X (fW ring ψ g) (cell ring ψ g k)).core.write = .none) ∧
    (∀ k, k < ψ → NIc (authRun hp κ c ring X (fW ring ψ g) (cell ring ψ g k)).core) ∧
    (HOWc (authRun hp κ c ring X (fW ring ψ g) (cell ring ψ g 0)).core →
      TSc (authRun hp κ c ring X (fW ring ψ g) (cell ring ψ g (ψ - 1))).core ∨
      icnt ring ψ g (authRun hp κ c ring X (fW ring ψ g)) < icnt ring ψ g X) := by
  obtain ⟨hout1, hout2, hL3⟩ := hL
  obtain ⟨hG1, hN1, -, -, -, -, hws1, -⟩ := step_ni hp κ c ring h2 hd hn X hG hN _ hout1
  obtain ⟨hG2, hN2, -, -, -, -, -, -, -, -, -, -, -, -, -, R11⟩ :=
    step_ni hp κ c ring h2 hd hn _ hG1 hN1 (bE ring ψ g) hout2
  rw [rn_bE] at R11
  unfold fW
  rw [authRun_cons, authRun_cons]
  generalize hX1 : S hp κ c ring X (cell ring ψ g 0) = X1 at hG1 hN1 hws1 hout2 R11 hG2 hN2 hL3 ⊢
  generalize hX2 : S hp κ c ring X1 (bE ring ψ g) = X2 at hG2 hN2 hL3 R11 ⊢
  have hH0 : ∀ Y : Fin n → AuthState ψ, Good Y → (Y (cell ring ψ g 0)).core.label.val = 0 :=
    fun Y hY => cell_label ring hmn hg hp hY.2
  refine ⟨fun k hk => sweepD hp κ c ring h2 hd hn hmn g hg (ψ - 2) 0 (Nat.zero_add _) X2 hG2 hL3 k
      (Nat.zero_le _) hk,
    fun k hk => sweepNIc hp κ c ring h2 hd hn hmn g hg (ψ - 2) 0 (Nat.zero_add _) X2 hG2 hN2 hL3 k
      (Nat.zero_le _) hk, ?_⟩
  intro hhow
  have hP := run_persist hp κ c ring h2 hd hn _ X2 hG2 hN2 hL3
  have hnt0 : ψ - 1 ≠ 0 := psi_sub_one_ne h2
  -- `HeadOW` held before the run of `D_g`, and before `B_g`
  have hh2 : HOWc (X2 (cell ring ψ g 0)).core :=
    (hP.2.2 (cell ring ψ g 0)).2.2.1 (by rw [hH0 X2 hG2]; exact fun h => hnt0 h.symm) hhow
  have hh1 : HOWc (X1 (cell ring ψ g 0)).core := by
    have := (step_persist hp κ c ring h2 hd hn X1 hG1 hN1 (bE ring ψ g) hout2
      (cell ring ψ g 0)).2.2.1 (by rw [hH0 X1 hG1]; exact fun h => hnt0 h.symm)
    rw [hX2] at this
    exact this hh2
  have hw2 : (X2 (cell ring ψ g 0)).core.write = .overwrite := by
    exact R11 (hH0 X1 hG1) hh1 hws1
  rcases sweepF hp κ c ring h2 hd hn hmn g hg (ψ - 2) 0 (Nat.zero_add _) X2 hG2 hN2 hL3 hw2 with
    h | ⟨k, _, hk2, hs, hdel⟩
  · exact Or.inl h
  · right
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      obtain ⟨p, hp3, -⟩ := hhow
      rw [hdel] at hp3; cases hp3
    · -- an interior `path3` was consumed
      have hmono : ∀ Z : Fin n → AuthState ψ, ∀ Z' : Fin n → AuthState ψ,
          (∀ i, (Z i).core.path3 = none → (Z' i).core.path3 = none) →
          ∀ j, j < ψ - 2 → ((Z' (cell ring ψ g (j + 1))).core.path3).isSome = true →
            ((Z (cell ring ψ g (j + 1))).core.path3).isSome = true := by
        intro Z Z' hz j _ hj
        cases hx : (Z (cell ring ψ g (j + 1))).core.path3 with
        | some _ => rfl
        | none => rw [hz _ hx] at hj; cases hj
      have p1 : ∀ i, (X i).core.path3 = none → (X1 i).core.path3 = none := by
        intro i hi; rw [← hX1]
        exact (step_persist hp κ c ring h2 hd hn X hG hN _ hout1 i).2.1 hi
      have p2 : ∀ i, (X1 i).core.path3 = none → (X2 i).core.path3 = none := by
        intro i hi; rw [← hX2]
        exact (step_persist hp κ c ring h2 hd hn X1 hG1 hN1 _ hout2 i).2.1 hi
      have p3 : ∀ i, (X2 i).core.path3 = none →
          (authRun hp κ c ring X2 (dW ring ψ g 0) i).core.path3 = none :=
        fun i hi => (hP.2.2 i).2.1 hi
      have hlt := cntB_lt (fun j => ((X2 (cell ring ψ g (j + 1))).core.path3).isSome)
        (fun j => ((authRun hp κ c ring X2 (dW ring ψ g 0) (cell ring ψ g (j + 1))).core.path3).isSome)
        (ψ - 2) (hmono _ _ p3) (k - 1) (arith_km1 k (ψ - 2) hk0 hk2).1
        (by rw [(arith_km1 k (ψ - 2) hk0 hk2).2]; exact hs)
        (by rw [(arith_km1 k (ψ - 2) hk0 hk2).2, hdel]; rfl)
      have hle1 := cntB_mono (fun j => ((X1 (cell ring ψ g (j + 1))).core.path3).isSome)
        (fun j => ((X2 (cell ring ψ g (j + 1))).core.path3).isSome) (ψ - 2) (hmono _ _ p2)
      have hle0 := cntB_mono (fun j => ((X (cell ring ψ g (j + 1))).core.path3).isSome)
        (fun j => ((X1 (cell ring ψ g (j + 1))).core.path3).isSome) (ψ - 2) (hmono _ _ p1)
      unfold icnt
      exact Nat.lt_of_lt_of_le hlt (Nat.le_trans hle1 hle0)

/-- Per-group security: `TerminalSafe` or (no `HeadOW` and no pending overwrite). -/
def SecG (ring : DirectedRing n) (ψ g : Nat) (C : Fin n → AuthState ψ) : Prop :=
  TSc (C (cell ring ψ g (ψ - 1))).core ∨
  (¬ HOWc (C (cell ring ψ g 0)).core ∧
    ∀ k, k < ψ → (C (cell ring ψ g k)).core.write ≠ .overwrite)

/-- Decide `TerminalSafe` constructively. -/
theorem tsc_or_not (u : AgentState ψ) : TSc u ∨ ∃ p, u.path3 = some p ∧ u.bit ≠ (p.bit == 1) := by
  cases hx : u.path3 with
  | none => left; intro p hp; rw [hx] at hp; cases hp
  | some p =>
    by_cases hb : u.bit = (p.bit == 1)
    · left
      intro p' hp'
      rw [hx] at hp'
      obtain rfl := Option.some.inj hp'
      exact hb
    · right; exact ⟨p, rfl, hb⟩

/-- **Part 2 headline: `F*_g` secures group `g`.** Along a leaderless run of
`F*_g = F_g^(ψ-1)` from a leaderless, perfectly labelled ring with no pending increment,
group `g` ends `TerminalSafe` or (no `HeadOW` and no pending overwrite), and every cell of
the group is `NoInc`. -/
theorem fStar_secures (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (h2 : 2 ≤ ψ) (hd : ψ ∣ n) (hn : 1 < n) {m : Nat} (hmn : n = m * ψ) (g : Nat) (hg : g < m)
    (X : Fin n → AuthState ψ) (hG : Good X) (hN : NIw X)
    (hL : LLRun hp κ c ring X (fS ring ψ g (ψ - 1))) :
    Good (authRun hp κ c ring X (fS ring ψ g (ψ - 1))) ∧
    NIw (authRun hp κ c ring X (fS ring ψ g (ψ - 1))) ∧
    SecG ring ψ g (authRun hp κ c ring X (fS ring ψ g (ψ - 1))) ∧
    ∀ k, k < ψ → NIc (authRun hp κ c ring X (fS ring ψ g (ψ - 1)) (cell ring ψ g k)).core := by
  have hnt0 : ψ - 1 ≠ 0 := psi_sub_one_ne h2
  have main : ∀ r, ∀ Z : Fin n → AuthState ψ, Good Z → NIw Z →
      LLRun hp κ c ring Z (fS ring ψ g r) →
      Good (authRun hp κ c ring Z (fS ring ψ g r)) ∧ NIw (authRun hp κ c ring Z (fS ring ψ g r)) ∧
      (HOWc (authRun hp κ c ring Z (fS ring ψ g r) (cell ring ψ g 0)).core →
        TSc (authRun hp κ c ring Z (fS ring ψ g r) (cell ring ψ g (ψ - 1))).core ∨
        icnt ring ψ g (authRun hp κ c ring Z (fS ring ψ g r)) + r ≤ icnt ring ψ g Z) ∧
      (0 < r → ∀ k, k < ψ →
        (authRun hp κ c ring Z (fS ring ψ g r) (cell ring ψ g k)).core.write = .none ∧
        NIc (authRun hp κ c ring Z (fS ring ψ g r) (cell ring ψ g k)).core) := by
    intro r
    induction r with
    | zero =>
      intro Z hZ hNZ _
      exact ⟨hZ, hNZ, fun _ => Or.inr (Nat.le_refl _), fun h => absurd h (Nat.lt_irrefl _)⟩
    | succ r ih =>
      intro Z hZ hNZ hLZ
      have hLs := (LLRun_append hp κ c ring _ _ Z).1 hLZ
      obtain ⟨hGY, hNY, hY, -⟩ := ih Z hZ hNZ hLs.1
      rw [fS_succ, authRun_append]
      generalize authRun hp κ c ring Z (fS ring ψ g r) = Y at hGY hNY hY hLs
      have hP := run_persist hp κ c ring h2 hd hn _ Y hGY hNY hLs.2
      obtain ⟨a1, a2, a3⟩ := attemptF hp κ c ring h2 hd hn hmn g hg Y hGY hNY hLs.2
      refine ⟨hP.1, hP.2.1, ?_, fun _ k hk => ⟨a1 k hk, a2 k hk⟩⟩
      intro hh
      have hhY : HOWc (Y (cell ring ψ g 0)).core :=
        (hP.2.2 _).2.2.1 (by rw [cell_label ring hmn hg hp hGY.2]; exact fun h => hnt0 h.symm) hh
      rcases a3 hh with h | h
      · exact Or.inl h
      · rcases hY hhY with h' | h'
        · exact Or.inl ((hP.2.2 _).1 h')
        · right; exact arith_step _ _ _ r h h'
  obtain ⟨hG', hN', hH, hW⟩ := main (ψ - 1) X hG hN hL
  refine ⟨hG', hN', ?_, fun k hk => (hW (Nat.pos_of_ne_zero hnt0) k hk).2⟩
  rcases tsc_or_not (authRun hp κ c ring X (fS ring ψ g (ψ - 1)) (cell ring ψ g (ψ - 1))).core with
    h | ⟨p, hp3, hb⟩
  · exact Or.inl h
  · right
    refine ⟨fun hh => ?_, fun k hk hw => ?_⟩
    · rcases hH hh with h | h
      · exact hb (h p hp3)
      · have := cntB_le (fun j => ((X (cell ring ψ g (j + 1))).core.path3).isSome) (ψ - 2)
        unfold icnt at h
        exact arith_final _ _ ψ h2 h this
    · rw [(hW (Nat.pos_of_ne_zero hnt0) k hk).1] at hw; cases hw

/-! ## Part 3: composition -/

theorem rn_inj (ring : DirectedRing n) {a b : Fin n}
    (h : ring.rightNeighbor a = ring.rightNeighbor b) : a = b := by
  have hv := congrArg Fin.val h
  change (a.val + 1) % n = (b.val + 1) % n at hv
  have ha := a.isLt
  have hb := b.isLt
  apply Fin.ext
  by_cases h1 : a.val + 1 < n
  · by_cases h2 : b.val + 1 < n
    · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hv; omega
    · have e : b.val + 1 = n := by omega
      rw [Nat.mod_eq_of_lt h1, e, Nat.mod_self] at hv; omega
  · have e : a.val + 1 = n := by omega
    by_cases h2 : b.val + 1 < n
    · rw [e, Nat.mod_self, Nat.mod_eq_of_lt h2] at hv; omega
    · omega

theorem pred_lt (k : Nat) (hk : k < ψ) (h0 : k ≠ 0) : k - 1 < ψ ∧ k - 1 + 1 = k := by
  constructor
  · omega
  · omega

/-- **Per-group closure.** A served edge of a leaderless `NoInc` run keeps group `g`
secured. -/
theorem secG_step (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (h2 : 2 ≤ ψ) (hd : ψ ∣ n) (hn : 1 < n) {m : Nat} (hmn : n = m * ψ) (g : Nat) (hg : g < m)
    (C : Fin n → AuthState ψ) (hG : Good C) (hN : NIw C) (e : Fin n)
    (hout : ∀ i, (S hp κ c ring C e i).core.leader = false) (hS : SecG ring ψ g C) :
    SecG ring ψ g (S hp κ c ring C e) := by
  have hnt0 : ψ - 1 ≠ 0 := psi_sub_one_ne h2
  rcases hS with hs | ⟨hno, hpend⟩
  · exact Or.inl ((step_persist hp κ c ring h2 hd hn C hG hN e hout _).1 hs)
  · right
    obtain ⟨-, -, hoth, -, -, -, -, L7, -, -, -, -, R8, -, -, -⟩ :=
      step_ni hp κ c ring h2 hd hn C hG hN e hout
    refine ⟨fun hh => hno ((step_persist hp κ c ring h2 hd hn C hG hN e hout _).2.2.1
      (by rw [cell_label ring hmn hg hp hG.2]; exact fun h => hnt0 h.symm) hh), ?_⟩
    intro k hk hw
    by_cases h1 : cell ring ψ g k = e
    · rw [h1] at hw
      exact hpend k hk (by rw [h1]; exact L7 hw)
    · by_cases h2' : cell ring ψ g k = ring.rightNeighbor e
      · rw [← h2'] at R8
        have hlab := cell_label ring hmn hg hk hG.2
        rcases R8 hw with ⟨hz, hwa⟩ | ⟨hz, hw' | hhow⟩
        · rw [hlab] at hz
          obtain ⟨hk1, hk2⟩ := pred_lt k hk hz
          have he : e = cell ring ψ g (k - 1) := by
            apply rn_inj ring
            rw [← h2', rn_cell, hk2]
          exact hpend (k - 1) hk1 (by rw [← he]; exact hwa)
        · exact hpend k hk hw'
        · rw [hlab] at hz
          subst hz
          exact hno hhow
      · rw [step_other hp κ c ring C e _ h1 h2'] at hw
        exact hpend k hk hw

theorem secG_run (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (h2 : 2 ≤ ψ) (hd : ψ ∣ n) (hn : 1 < n) {m : Nat} (hmn : n = m * ψ) (g : Nat) (hg : g < m) :
    ∀ (w : List (Fin n)) (C : Fin n → AuthState ψ), Good C → NIw C → LLRun hp κ c ring C w →
    SecG ring ψ g C → SecG ring ψ g (authRun hp κ c ring C w) := by
  intro w
  induction w with
  | nil => intro C _ _ _ h; exact h
  | cons e es ih =>
    intro C hG hN hL hS
    obtain ⟨hG1, hN1, -⟩ := step_ni hp κ c ring h2 hd hn C hG hN e hL.1
    exact ih _ hG1 hN1 hL.2 (secG_step hp κ c ring h2 hd hn hmn g hg C hG hN e hL.1 hS)

/-- `F* = F*_0 ++ … ++ F*_(t-1)`. -/
def wFS (ring : DirectedRing n) (ψ : Nat) : Nat → List (Fin n)
  | 0 => []
  | t + 1 => wFS ring ψ t ++ fS ring ψ t (ψ - 1)

/-- The writer word `W_wr = D ++ F*`. -/
def wWr (ring : DirectedRing n) (ψ m : Nat) : List (Fin n) := wD ring ψ m ++ wFS ring ψ m

/-- **The `F*` phase.** After a leaderless run of `F*_0 ++ … ++ F*_(t-1)` from a leaderless,
perfectly labelled ring with no pending increment, groups `0 … t-1` are secured and `NoInc`. -/
theorem phaseF (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (h2 : 2 ≤ ψ) (hd : ψ ∣ n) (hn : 1 < n) {m : Nat} (hmn : n = m * ψ) :
    ∀ t, t ≤ m → ∀ Z : Fin n → AuthState ψ, Good Z → NIw Z →
    LLRun hp κ c ring Z (wFS ring ψ t) →
    Good (authRun hp κ c ring Z (wFS ring ψ t)) ∧ NIw (authRun hp κ c ring Z (wFS ring ψ t)) ∧
    (∀ g, g < t → SecG ring ψ g (authRun hp κ c ring Z (wFS ring ψ t))) ∧
    (∀ g k, g < t → k < ψ → NIc (authRun hp κ c ring Z (wFS ring ψ t) (cell ring ψ g k)).core) := by
  intro t
  induction t with
  | zero =>
    intro _ Z hZ hNZ _
    exact ⟨hZ, hNZ, fun g hg => absurd hg (Nat.not_lt_zero _),
      fun g _ hg => absurd hg (Nat.not_lt_zero _)⟩
  | succ t ih =>
    intro ht Z hZ hNZ hL
    have hLs := (LLRun_append hp κ c ring _ _ Z).1 hL
    obtain ⟨hGY, hNY, hSec, hNic⟩ := ih (by omega) Z hZ hNZ hLs.1
    show Good (authRun hp κ c ring Z (wFS ring ψ t ++ fS ring ψ t (ψ - 1))) ∧ _
    rw [show wFS ring ψ (t + 1) = wFS ring ψ t ++ fS ring ψ t (ψ - 1) from rfl, authRun_append]
    generalize authRun hp κ c ring Z (wFS ring ψ t) = Y at hGY hNY hSec hNic hLs
    obtain ⟨g1, g2, g3, g4⟩ := fStar_secures hp κ c ring h2 hd hn hmn t (by omega) Y hGY hNY hLs.2
    have hP := run_persist hp κ c ring h2 hd hn _ Y hGY hNY hLs.2
    refine ⟨g1, g2, fun g hg => ?_, fun g k hg hk => ?_⟩
    · rcases Nat.lt_or_ge g t with hgt | hgt
      · exact secG_run hp κ c ring h2 hd hn hmn g (by omega) _ Y hGY hNY hLs.2 (hSec g hgt)
      · have : g = t := by omega
        subst this; exact g3
    · rcases Nat.lt_or_ge g t with hgt | hgt
      · exact (hP.2.2 _).2.2.2 (hNic g k hgt hk)
      · have : g = t := by omega
        subst this; exact g4 k hk

theorem head_cell (ring : DirectedRing n) {m : Nat} (hp : ψ > 0) (hmn : n = m * ψ)
    (t h : Fin n) (ht : t.val % ψ = ψ - 1) (hh : h.val + (ψ - 1) = t.val) :
    h = cell ring ψ (t.val / ψ) 0 := by
  obtain ⟨hq, _, _⟩ := cell_cover ring hp hmn t
  apply Fin.ext
  rw [cell_val ring hmn hq hp]
  have e1 := Nat.div_add_mod t.val ψ
  rw [Nat.mul_comm] at e1
  omega

/-- **Part 3 (implication form).** A leaderless run of `W_wr = D ++ F*` from a leaderless ring
with perfect labels ends in `LeaderlessBitFrozen` with perfect labels. -/
theorem reach_of_LLRun (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (h2 : 2 ≤ ψ) (hd : ψ ∣ n) (hn : 1 < n) {m : Nat} (hmn : n = m * ψ)
    (C : Fin n → AuthState ψ) (hG : Good C) (hL : LLRun hp κ c ring C (wWr ring ψ m)) :
    LBF (authRun hp κ c ring C (wWr ring ψ m)) ∧ PL (authRun hp κ c ring C (wWr ring ψ m)) := by
  have hLs := (LLRun_append hp κ c ring _ _ C).1 hL
  obtain ⟨hGD, hW⟩ := phaseD hp κ c ring h2 hd hn hmn C hG hLs.1
  have hND : NIw (authRun hp κ c ring C (wD ring ψ m)) := by
    intro i h; rw [hW i] at h; cases h
  obtain ⟨hGY, -, hSec, hNic⟩ :=
    phaseF hp κ c ring h2 hd hn hmn m (Nat.le_refl _) _ hGD hND hLs.2
  unfold wWr
  rw [authRun_append]
  generalize authRun hp κ c ring (authRun hp κ c ring C (wD ring ψ m)) (wFS ring ψ m) = Y
    at hGY hSec hNic
  refine ⟨⟨fun i => ?_, fun t ht => ?_⟩, hGY.2⟩
  · obtain ⟨hq, hr, hi⟩ := cell_cover ring hp hmn i
    rw [← hi]; exact hNic _ _ hq hr
  · obtain ⟨hq, hr, hi⟩ := cell_cover ring hp hmn t
    rw [ht] at hr hi
    rcases hSec _ hq with hs | ⟨hno, hpend⟩
    · left; rw [← hi]; exact hs
    · right
      refine ⟨fun h hh => ?_, fun j hj => ?_⟩
      · rw [head_cell ring hp hmn t h ht hh]; exact hno
      · obtain ⟨hq', hr', hi'⟩ := cell_cover ring hp hmn j
        rw [← hi', hj]
        exact hpend _ hr'

/-! ### Deciding whether a prefix produced a leader -/

/-- `true` iff every intermediate configuration of the run is leaderless. -/
def llB (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n) :
    (Fin n → AuthState ψ) → List (Fin n) → Bool
  | _, [] => true
  | C, e :: es => (List.range n).all (fun k => if h : k < n then
        !(S hp κ c ring C e ⟨k, h⟩).core.leader else true) && llB hp κ c ring (S hp κ c ring C e) es

theorem all_false {α : Type} (p : α → Bool) : ∀ l : List α, l.all p = false → ∃ x ∈ l, p x = false := by
  intro l
  induction l with
  | nil => intro h; cases h
  | cons x xs ih =>
    intro h
    cases hx : p x
    · exact ⟨x, List.mem_cons_self, hx⟩
    · have : xs.all p = false := by
        have e : (x :: xs).all p = (p x && xs.all p) := rfl
        rw [e, hx] at h; exact h
      obtain ⟨y, hy, hpy⟩ := ih this
      exact ⟨y, List.mem_cons_of_mem _ hy, hpy⟩

theorem llB_true (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n) :
    ∀ (w : List (Fin n)) (C : Fin n → AuthState ψ), llB hp κ c ring C w = true →
    LLRun hp κ c ring C w := by
  intro w
  induction w with
  | nil => intro _ _; trivial
  | cons e es ih =>
    intro C h
    have e1 : llB hp κ c ring C (e :: es) = ((List.range n).all (fun k => if h : k < n then
        !(S hp κ c ring C e ⟨k, h⟩).core.leader else true) &&
        llB hp κ c ring (S hp κ c ring C e) es) := rfl
    rw [e1, Bool.and_eq_true] at h
    refine ⟨fun i => ?_, ih _ h.2⟩
    have := List.all_eq_true.1 h.1 i.val (List.mem_range.2 i.isLt)
    rw [dif_pos i.isLt] at this
    cases hx : (S hp κ c ring C e i).core.leader
    · rfl
    · rw [hx] at this; cases this

theorem llB_false (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n) :
    ∀ (w : List (Fin n)) (C : Fin n → AuthState ψ), llB hp κ c ring C w = false →
    ∃ k, k ≤ w.length ∧ ∃ i, (authRun hp κ c ring C (w.take k) i).core.leader = true := by
  intro w
  induction w with
  | nil => intro _ h; cases h
  | cons e es ih =>
    intro C h
    have e1 : llB hp κ c ring C (e :: es) = ((List.range n).all (fun k => if h : k < n then
        !(S hp κ c ring C e ⟨k, h⟩).core.leader else true) &&
        llB hp κ c ring (S hp κ c ring C e) es) := rfl
    rw [e1] at h
    cases h1 : (List.range n).all (fun k => if h : k < n then
        !(S hp κ c ring C e ⟨k, h⟩).core.leader else true)
    · obtain ⟨k, hk, hpk⟩ := all_false _ _ h1
      have hkn := List.mem_range.1 hk
      rw [dif_pos hkn] at hpk
      refine ⟨1, by simp, ⟨k, hkn⟩, ?_⟩
      show (S hp κ c ring C e ⟨k, hkn⟩).core.leader = true
      cases hx : (S hp κ c ring C e ⟨k, hkn⟩).core.leader
      · rw [hx] at hpk; cases hpk
      · rfl
    · rw [h1] at h
      obtain ⟨k, hk, i, hi⟩ := ih _ h
      exact ⟨k + 1, by simp; omega, i, hi⟩

/-- **Reaching half of stage 2 (headline).** For `2 ≤ ψ`, `ψ ∣ n`, `1 < n`, and a leaderless
AuthF ring with perfect labels, running the writer word `W_wr = D ++ F*`
(`m = n/ψ` groups) either produces a leader after some prefix, or ends in
`LeaderlessBitFrozen` with perfect labels. Holds for every `κ` and every AuthF `Cfg`
(in particular `authFplusmcc`); no reset/echo or domain hypothesis is needed. -/
theorem writer_reach (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (h2 : 2 ≤ ψ) (hd : ψ ∣ n) (hn : 1 < n) (C : Fin n → AuthState ψ)
    (hC : ∀ i, (C i).core.leader = false) (hpl : PL C) :
    (∃ k, k ≤ (wWr ring ψ (n / ψ)).length ∧
      ∃ i, (authRun hp κ c ring C ((wWr ring ψ (n / ψ)).take k) i).core.leader = true) ∨
    (LBF (authRun hp κ c ring C (wWr ring ψ (n / ψ))) ∧
      PL (authRun hp κ c ring C (wWr ring ψ (n / ψ)))) := by
  have hmn : n = n / ψ * ψ := (Nat.div_mul_cancel hd).symm
  cases h : llB hp κ c ring C (wWr ring ψ (n / ψ))
  · exact Or.inl (llB_false hp κ c ring _ C h)
  · exact Or.inr (reach_of_LLRun hp κ c ring h2 hd hn hmn C ⟨hC, hpl⟩ (llB_true hp κ c ring _ C h))

/-! ### Length of `W_wr` -/

theorem dW_length (ring : DirectedRing n) (h2 : 2 ≤ ψ) (g : Nat) :
    (dW ring ψ g 0).length = ψ := by
  unfold dW
  rw [List.length_append, List.length_map, List.length_range']
  show ψ - 1 - 0 + 1 = ψ
  omega

theorem wD_length (ring : DirectedRing n) (h2 : 2 ≤ ψ) : ∀ t, (wD ring ψ t).length = t * ψ := by
  intro t
  induction t with
  | zero => rw [Nat.zero_mul]; rfl
  | succ t ih =>
    show (wD ring ψ t ++ dW ring ψ t 0).length = _
    rw [List.length_append, ih, dW_length ring h2, Nat.succ_mul]

theorem fS_length (ring : DirectedRing n) (h2 : 2 ≤ ψ) (g : Nat) :
    ∀ r, (fS ring ψ g r).length = r * (ψ + 2) := by
  intro r
  induction r with
  | zero => rw [Nat.zero_mul]; rfl
  | succ r ih =>
    rw [fS_succ, List.length_append, ih, Nat.succ_mul,
      show (fW ring ψ g).length = (dW ring ψ g 0).length + 2 from rfl, dW_length ring h2]

theorem wFS_length (ring : DirectedRing n) (h2 : 2 ≤ ψ) :
    ∀ t, (wFS ring ψ t).length = t * ((ψ - 1) * (ψ + 2)) := by
  intro t
  induction t with
  | zero => rw [Nat.zero_mul]; rfl
  | succ t ih =>
    show (wFS ring ψ t ++ fS ring ψ t (ψ - 1)).length = _
    rw [List.length_append, ih, fS_length ring h2, Nat.succ_mul]

/-- `|W_wr| = n + (n/ψ)(ψ-1)(ψ+2)`. -/
theorem wWr_length (ring : DirectedRing n) (h2 : 2 ≤ ψ) (hd : ψ ∣ n) :
    (wWr ring ψ (n / ψ)).length = n + n / ψ * ((ψ - 1) * (ψ + 2)) := by
  unfold wWr
  rw [List.length_append, wD_length ring h2, wFS_length ring h2, Nat.div_mul_cancel hd]

#print axioms writeSeq_internal
#print axioms phaseD
#print axioms writeSeq_ni
#print axioms attemptF
#print axioms fStar_secures
#print axioms secG_step
#print axioms reach_of_LLRun
#print axioms writer_reach
#print axioms wWr_length

end Ring
end PPLLAuthWriterReach
