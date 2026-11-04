import Leader.Wu.Birth.ShortDoneWaitPassivePreCap
import Leader.Wu.Birth.ShortDoneTerminalHost
import Leader.Wu.Birth.ShortWaitTerminalEntryRepair

namespace BirthShortDoneTerminalPassiveR1

open PPLL PPLLRepair PPLLDomain
open BirthGenerationControlRepair
open BirthWaitPassive BirthShortWait
open BirthShortWaitTerminalEntryRepair

set_option autoImplicit false
set_option pp.structureInstances false

variable {psi kappa tau : Nat}

/-- Exact repaired width-two state immediately before Finish. -/
def preFinishEntry2 (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (l r : AgentState psi) : AgentState psi × AgentState psi :=
  let p := waitSaturatedPrepare hpsi l r
  let e := terminalInactiveClear (by decide : 0 < 2) h2 p.1 p.2
  let c := waitWidthCarry (by decide : 0 < 2) h2 kappa e.1 e.2
  waitWidthReset (by decide : 0 < 2) h2 c.1 c.2

/-- Minimal repaired current-row exclusion of the real width-two cap branch. -/
def PreCapEntry2 (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (l r : AgentState psi) : Prop :=
  let s := preFinishEntry2 hpsi h2 kappa l r
  ¬ (s.2.label = widthTerminal (by decide : 0 < 2) h2 ∧ s.2.count = kappa)

private theorem prepare_wait (hpsi : 0 < psi) (l r : AgentState psi) :
    let q := waitSaturatedPrepare hpsi l r
    q.1.wait = l.wait ∧ q.2.wait = r.wait := by
  unfold waitSaturatedPrepare
  split <;> try dsimp only
  all_goals split <;> try dsimp only
  all_goals first
    | exact ⟨rfl, rfl⟩
    | (split <;> exact ⟨rfl, rfl⟩)

private theorem clear_wait (h2 : 2 <= psi) (l r : AgentState psi) :
    let q := terminalInactiveClear (by decide : 0 < 2) h2 l r
    q.1.wait = l.wait ∧ q.2.wait = r.wait := by
  unfold terminalInactiveClear
  split <;> exact ⟨rfl, rfl⟩

private theorem carry_wait (h2 : 2 <= psi) (kappa : Nat)
    (l r : AgentState psi) :
    let q := waitWidthCarry (by decide : 0 < 2) h2 kappa l r
    q.1.wait = l.wait ∧ q.2.wait = r.wait := by
  unfold waitWidthCarry
  split <;> try dsimp only
  · split <;> try dsimp only
    · split <;> try dsimp only
      · split <;> exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

private theorem reset_wait (h2 : 2 <= psi) (l r : AgentState psi) :
    let q := waitWidthReset (by decide : 0 < 2) h2 l r
    q.1.wait = l.wait ∧ q.2.wait = r.wait := by
  unfold waitWidthReset
  split <;> try dsimp only
  · split <;> try dsimp only
    · split <;> exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

theorem preFinishEntry2_wait (hpsi : 0 < psi) (h2 : 2 <= psi)
    (kappa : Nat) (l r : AgentState psi) :
    let s := preFinishEntry2 hpsi h2 kappa l r
    s.1.wait = l.wait ∧ s.2.wait = r.wait := by
  let p := waitSaturatedPrepare hpsi l r
  have hp := prepare_wait hpsi l r
  let e := terminalInactiveClear (by decide : 0 < 2) h2 p.1 p.2
  have he := clear_wait h2 p.1 p.2
  let c := waitWidthCarry (by decide : 0 < 2) h2 kappa e.1 e.2
  have hc := carry_wait h2 kappa e.1 e.2
  let s := waitWidthReset (by decide : 0 < 2) h2 c.1 c.2
  have hs := reset_wait h2 c.1 c.2
  change s.1.wait = l.wait ∧ s.2.wait = r.wait
  exact ⟨hs.1.trans (hc.1.trans (he.1.trans hp.1)),
    hs.2.trans (hc.2.trans (he.2.trans hp.2))⟩

/-- Repaired pre-cap is exactly enough to keep both physical WAIT bits armed. -/
theorem waitWidthEntry2_armed_of_preCap
    (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (l r : AgentState psi) (hl : l.wait = true) (hr : r.wait = true)
    (hc : PreCapEntry2 hpsi h2 kappa l r) :
    let w := waitWidthEntry hpsi (by decide : 0 < 2) h2 kappa l r
    w.1.wait = true ∧ w.2.wait = true := by
  let s := preFinishEntry2 hpsi h2 kappa l r
  have hs := preFinishEntry2_wait hpsi h2 kappa l r
  have hsl : s.1.wait = true := hs.1.trans hl
  have hsr : s.2.wait = true := hs.2.trans hr
  change ¬ (s.2.label = widthTerminal (by decide : 0 < 2) h2 ∧
    s.2.count = kappa) at hc
  unfold waitWidthEntry
  change
    (waitWidthFinish hpsi (by decide : 0 < 2) h2 kappa s.1 s.2).1.wait = true ∧
    (waitWidthFinish hpsi (by decide : 0 < 2) h2 kappa s.1 s.2).2.wait = true
  simp [waitWidthFinish, hc, hsl, hsr]

private theorem prepare_meta (hpsi : 0 < psi) (a b : Registers psi) :
    let q := waitSaturatedPrepare hpsi (cell a) (cell b)
    Metadata q.1 ∧ Metadata q.2 := by
  unfold waitSaturatedPrepare
  split <;> try dsimp only
  all_goals split <;> try dsimp only
  all_goals first
    | exact ⟨rfl, rfl⟩
    | (split <;> exact ⟨rfl, rfl⟩)

private theorem clear_meta (h2 : 2 <= psi) (a b : Registers psi) :
    let q := terminalInactiveClear (by decide : 0 < 2) h2 (cell a) (cell b)
    Metadata q.1 ∧ Metadata q.2 := by
  unfold terminalInactiveClear
  split <;> exact ⟨rfl, rfl⟩

private theorem carry_meta (h2 : 2 <= psi) (kappa : Nat)
    (a b : Registers psi) :
    let q := waitWidthCarry (by decide : 0 < 2) h2 kappa (cell a) (cell b)
    Metadata q.1 ∧ Metadata q.2 := by
  unfold waitWidthCarry
  split <;> try dsimp only
  · split <;> try dsimp only
    · split <;> try dsimp only
      · split <;> exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

private theorem reset_meta (h2 : 2 <= psi) (a b : Registers psi) :
    let q := waitWidthReset (by decide : 0 < 2) h2 (cell a) (cell b)
    Metadata q.1 ∧ Metadata q.2 := by
  unfold waitWidthReset
  split <;> try dsimp only
  · split <;> try dsimp only
    · split <;> exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

private theorem finish_meta (hpsi : 0 < psi) (h2 : 2 <= psi)
    (kappa : Nat) (a b : Registers psi) :
    let q := waitWidthFinish hpsi (by decide : 0 < 2) h2 kappa
      (cell a) (cell b)
    Metadata q.1 ∧ Metadata q.2 := by
  unfold waitWidthFinish
  split <;> try dsimp only
  · split <;> exact ⟨rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl⟩

/-- The repaired WAIT remains a literal passive-cell image. -/
theorem waitWidthEntry2_metadata (hpsi : 0 < psi) (h2 : 2 <= psi)
    (kappa : Nat) (a b : Registers psi) :
    let w := waitWidthEntry hpsi (by decide : 0 < 2) h2 kappa
      (cell a) (cell b)
    w.1 = cell (registers w.1) ∧ w.2 = cell (registers w.2) := by
  let p := waitSaturatedPrepare hpsi (cell a) (cell b)
  have hp : Metadata p.1 ∧ Metadata p.2 := prepare_meta hpsi a b
  let e := terminalInactiveClear (by decide : 0 < 2) h2 p.1 p.2
  have he : Metadata e.1 ∧ Metadata e.2 := by
    unfold e
    rw [hp.1, hp.2]
    exact clear_meta h2 (registers p.1) (registers p.2)
  let c := waitWidthCarry (by decide : 0 < 2) h2 kappa e.1 e.2
  have hc : Metadata c.1 ∧ Metadata c.2 := by
    unfold c
    rw [he.1, he.2]
    exact carry_meta h2 kappa (registers e.1) (registers e.2)
  let s := waitWidthReset (by decide : 0 < 2) h2 c.1 c.2
  have hs : Metadata s.1 ∧ Metadata s.2 := by
    unfold s
    rw [hc.1, hc.2]
    exact reset_meta h2 (registers c.1) (registers c.2)
  change let w := waitWidthFinish hpsi (by decide : 0 < 2) h2 kappa s.1 s.2
    Metadata w.1 ∧ Metadata w.2
  rw [hs.1, hs.2]
  exact finish_meta hpsi h2 kappa (registers s.1) (registers s.2)

/-- First bridge needed by the unpublished TerminalEntryCut cell proof. -/
theorem genAfterEntry2_cell (hpsi : 0 < psi) (h2 : 2 <= psi)
    (kappa : Nat) (a b : Registers psi)
    (ha : a.wait = true) (hb : b.wait = true)
    (hc : PreCapEntry2 hpsi h2 kappa (cell a) (cell b)) :
    let w := waitWidthEntry hpsi (by decide : 0 < 2) h2 kappa
      (cell a) (cell b)
    genCleanAfterWait hpsi w.1 w.2 =
      (cell (registers w.1), cell (registers w.2)) := by
  let w := waitWidthEntry hpsi (by decide : 0 < 2) h2 kappa
    (cell a) (cell b)
  have hm := waitWidthEntry2_metadata hpsi h2 kappa a b
  have hw := waitWidthEntry2_armed_of_preCap hpsi h2 kappa
    (cell a) (cell b)
    (by change a.wait = true; exact ha)
    (by change b.wait = true; exact hb) hc
  dsimp only
  conv => lhs; rw [hm.1, hm.2]
  exact gen_after_wait_cell hpsi (registers w.1) (registers w.2) (by
    intro _
    change w.1.wait = true
    exact hw.1)

#print axioms waitWidthEntry2_armed_of_preCap
#print axioms waitWidthEntry2_metadata
#print axioms genAfterEntry2_cell

end BirthShortDoneTerminalPassiveR1
