import Leader.L4.RearTrackGeometry
import Leader.L4.RearRefill

/-!
# Phase lengths and the deterministic rear count
The lifted rear can spend only the initial allowance plus actual ghost
advances, one loss move and one preemption move. This finite-word account
names the exact local phase facts it uses.
-/

namespace L4.RearTrace
open TaggedTrace

/-- Ghost advances are counted only in the ghost phase, not on a
synchronous transition that pins the tag. -/
def ghostAdvanceCount {p c n : Nat} (s t : Observer p c n) : Nat :=
  if s.phase = .ghost ∧ t.phase ≠ .pinned then t.rearMoves - s.rearMoves else 0

def ghostAdvances {p c n : Nat} (i : Fin n) (s : Observer p c n) :
    List (Fin n) → Nat
  | [] => 0
  | e :: w =>
    let t := rearAdvance i s e
    ghostAdvanceCount s t + ghostAdvances i t w

/-- The actual initialized phase needs no wrap inequality; its move
counter is strictly below the first 2n-move cut. -/
def PhaseCost {p c n : Nat} ( _d0 X : Nat) (s : Observer p c n) : Prop :=
  match s.phase with
  | .initial => s.tag.moveCount < 2*n
  | .initialLeader => s.rearMoves ≤ 3*n
  | .ghost | .finalLeader => s.rearMoves ≤ 3*n+X+1
  | .pinned => s.rearMoves ≤ 3*n+X+2

/-- At each ordinary phase change no rear moves are hidden. A potential
loss and a potential pin are accounted separately by the upper bounds
on per-mark movement and by phase monotonicity. -/
inductive PhaseStep (r u : Phase) (dx : Nat) : Prop
  | initial : r = .initial → (u = .initial ∨ u = .initialLeader ∨ u = .ghost ∨ u = .pinned) → PhaseStep r u dx
  | leaderStay : r = .initialLeader → u = .initialLeader → dx = 0 → PhaseStep r u dx
  | leaderStop : r = .initialLeader → (u = .ghost ∨ u = .pinned) → PhaseStep r u dx
  | ghost : r = .ghost → (u = .ghost ∨ u = .finalLeader ∨ u = .pinned) → PhaseStep r u dx
  | final : r = .finalLeader → u = .finalLeader → dx = 0 → PhaseStep r u dx
  | pinned : r = .pinned → u = .pinned → dx = 0 → PhaseStep r u dx

/-- Pure arithmetic of the phase account. The last stationary mark
may be the actual loss mark and need not keep the rear fixed. -/
theorem budget_step {p c n d0 X : Nat} {s t : Observer p c n} {dx : Nat}
    (h : PhaseCost d0 X s)
    (hR : t.rearMoves = s.rearMoves+dx) (hdx : dx ≤ 1)
    (hph : PhaseStep s.phase t.phase dx)
    (hInit : t.phase = .initial → t.tag.moveCount < 2*n)
    (hCut : s.phase = .initial → t.phase ≠ .initial → t.rearMoves ≤ 3*n) :
    PhaseCost d0 (X+ghostAdvanceCount s t) t := by
  cases hph with
  | initial h₁ h₂ =>
    rcases h₂ with h₂ | h₂ | h₂ | h₂
    · simpa [PhaseCost,h₂] using hInit h₂
    · simp [PhaseCost,h₂,hCut h₁ (by rw [h₂]; decide)]
    · have hc := hCut h₁ (by rw [h₂]; decide)
      simp [PhaseCost,ghostAdvanceCount,h₁,h₂]
      omega
    · have hc := hCut h₁ (by rw [h₂]; decide)
      simp [PhaseCost,ghostAdvanceCount,h₁,h₂]
      omega
  | leaderStay h₁ h₂ dz =>
    simp [PhaseCost,h₁] at h
    simpa [PhaseCost,h₂,hR,dz] using h
  | leaderStop h₁ h₂ =>
    simp [PhaseCost,h₁] at h
    rcases h₂ with h₂ | h₂ <;> simp [PhaseCost,ghostAdvanceCount,h₁,h₂,hR] <;> omega
  | ghost h₁ h₂ =>
    simp [PhaseCost,h₁] at h
    rcases h₂ with h₂ | h₂ | h₂ <;> simp [PhaseCost,ghostAdvanceCount,h₁,h₂,hR] <;> omega
  | final h₁ h₂ dz =>
    simp [PhaseCost,h₁] at h
    simpa [PhaseCost,ghostAdvanceCount,h₁,h₂,hR,dz] using h
  | pinned h₁ h₂ dz =>
    simp [PhaseCost,h₁] at h
    simpa [PhaseCost,ghostAdvanceCount,h₁,h₂,hR,dz] using h

theorem phaseBudget_tag_unpinned {p c n d0 X : Nat} {s : Observer p c n} {b : Fin n}
    (hn : 4 ≤ n) (hp : s.phase ≠ .pinned)
    (hc : PhaseCost d0 X s) (hg : LiveGeometry d0 s b) :
    s.tag.moveCount ≤ 5*n+X := by
  cases hg with
  | pinned h => exact (hp h).elim
  | tracking h d hr hd he =>
    have hdn := hd.lt
    cases hP : s.phase <;> simp [PhaseCost,hP] at hc <;> try omega

/-- A calculated phase profile; the only extra row facts required are
the fixed final shield and that a moved rear is not a living leader. -/
theorem phase_machine {p c n : Nat} (s : Observer p c n) (t : Obs p c n)
    (r : Fin n) (m : Bool)
    (hS : s.phase = .initialLeader → phaseAfter s t r m = .initialLeader → m = false)
    (hF : s.phase = .finalLeader → m = false)
    (hP : s.phase = .pinned → m = false) :
    PhaseStep s.phase (phaseAfter s t r m) m.toNat := by
  by_cases hp : phaseAfter s t r m = .pinned
  · rw [hp]
    cases he : s.phase with
    | initial => exact .initial rfl (Or.inr (Or.inr (Or.inr rfl)))
    | initialLeader => exact .leaderStop rfl (Or.inr rfl)
    | ghost => exact .ghost rfl (Or.inr (Or.inr rfl))
    | finalLeader =>
      have hh := (phaseAfter_pinned s t r m).mp hp
      simp [he,hF he] at hh
    | pinned => exact .pinned rfl rfl (by rw [hP he]; rfl)
  · have hh : ¬ ((s.phase == Phase.pinned) || m && s.tag.carrier == s.rear) = true := by
      intro h
      apply hp
      simp [phaseAfter,h]
    have hpu : s.phase ≠ .pinned := fun he => hp ((phaseAfter_pinned _ _ _ _).mpr (Or.inl he))
    have ha : phaseAfter s t r m =
        (match s.phase with
        | .initial => if 2*n ≤ t.moveCount then
            if (t.config r).leader then .initialLeader else .ghost else .initial
        | .initialLeader => if (t.config r).leader then .initialLeader else .ghost
        | .ghost => if (t.config r).leader then .finalLeader else .ghost
        | .finalLeader => .finalLeader
        | .pinned => .pinned) := by unfold phaseAfter; rw [if_neg hh]; rfl
    rw [ha]
    cases he : s.phase with
    | initial =>
      change PhaseStep .initial (if 2*n ≤ t.moveCount then
        if (t.config r).leader then .initialLeader else .ghost else .initial) m.toNat
      split
      · split
        · exact .initial rfl (Or.inr (Or.inl rfl))
        · exact .initial rfl (Or.inr (Or.inr (Or.inl rfl)))
      · exact .initial rfl (Or.inl rfl)
    | initialLeader =>
      change PhaseStep .initialLeader (if (t.config r).leader then .initialLeader else .ghost) m.toNat
      split
      · rename_i hl
        have hphase : phaseAfter s t r m = .initialLeader := by
          rw [ha,he]
          change (if (t.config r).leader then Phase.initialLeader else .ghost) = .initialLeader
          rw [if_pos hl]
        exact .leaderStay rfl rfl (by rw [hS he hphase]; rfl)
      · exact .leaderStop rfl (Or.inl rfl)
    | ghost =>
      change PhaseStep .ghost (if (t.config r).leader then .finalLeader else .ghost) m.toNat
      split
      · exact .ghost rfl (Or.inr (Or.inl rfl))
      · exact .ghost rfl (Or.inl rfl)
    | finalLeader => exact .final rfl rfl (by rw [hF he]; rfl)
    | pinned => exact (hpu he).elim

theorem phase_initial_limit {p c n : Nat} (s : Observer p c n) (t : Obs p c n)
    (r : Fin n) (m : Bool) (h : phaseAfter s t r m = .initial) :
    t.moveCount < 2*n := by
  unfold phaseAfter at h
  split at h
  · contradiction
  · cases hs : s.phase <;> simp only [hs] at h
    case initial =>
      split at h
      · split at h <;> contradiction
      · omega
    all_goals first | contradiction | (split at h <;> contradiction)

/-- Facts on exactly those real prefixes for which the rear clock is
used. A frozen final shield makes the second premise non-probabilistic. -/
def LocalPhaseFacts {p c n : Nat} (i : Fin n) (s : Observer p c n) (e : Fin n) : Prop :=
  let t := rearAdvance i s e
  (s.phase = .initialLeader → t.phase = .initialLeader → t.rearMoves = s.rearMoves) ∧
  (s.phase = .finalLeader → t.rearMoves = s.rearMoves)

theorem phase_step_of_local {p c n : Nat} (i e : Fin n) (s : Observer p c n)
    (hf : LocalPhaseFacts i s e) :
    ∃ dx : Nat, dx ≤ 1 ∧
      (rearAdvance i s e).rearMoves = s.rearMoves+dx ∧
      PhaseStep s.phase (rearAdvance i s e).phase dx := by
  cases hr : s.rear with
  | none =>
    have he : (rearAdvance i s e).phase = s.phase := by simp [rearAdvance,hr]
    have hs : (rearAdvance i s e).rearMoves = s.rearMoves := by simp [rearAdvance,hr]
    refine ⟨0,by omega,hs,?_⟩
    rw [he]
    cases s.phase
    · exact .initial rfl (Or.inl rfl)
    · exact .leaderStay rfl rfl rfl
    · exact .ghost rfl (Or.inl rfl)
    · exact .final rfl rfl rfl
    · exact .pinned rfl rfl rfl
  | some r =>
    let m := !(s.phase == .pinned) && rearShifts s e r
    let r' := if m then rightNeighbor r else r
    have h := post_fields i e r s hr
    change _ ∧ (rearAdvance i s e).rearMoves = s.rearMoves+m.toNat ∧
      (rearAdvance i s e).phase = phaseAfter s (advance s.tag e) r' m at h
    refine ⟨m.toNat,by cases m <;> decide,h.2.1,?_⟩
    rw [h.2.2]
    apply phase_machine
    · intro hs hnext
      have he := hf.1 hs (h.2.2.trans hnext)
      rw [h.2.1] at he
      cases hm : m <;> simp [hm] at he ⊢
    · intro hs
      have he := hf.2 hs
      rw [h.2.1] at he
      cases hm : m <;> simp [hm] at he ⊢
    · intro hs
      have he : (s.phase == Phase.pinned) = true := by rw [hs]; rfl
      simp [m,he]

theorem successor_initial_limit {p c n d0 : Nat} (i e b : Fin n)
    (s : Observer p c n) (hg : LiveGeometry d0 s b)
    (hp : (rearAdvance i s e).phase = .initial) :
    (rearAdvance i s e).tag.moveCount < 2*n := by
  cases hg with
  | pinned h =>
    have he := (no_move_of_pin i e s h).symm.trans hp
    contradiction
  | tracking h d hr hf eq =>
    have hh := post_fields i e (back b d) s hr
    rw [hh.2.2] at hp
    rw [rearAdvance_tag]
    exact phase_initial_limit _ _ _ _ hp

theorem phase_account_step {p c n d0 X : Nat} (hn : 4 ≤ n) (i e b b' : Fin n)
    (s : Observer p c n) (hm : MCOV s.tag.config)
    (hb : s.tag.carrier = some b) (hb' : (rearAdvance i s e).tag.carrier = some b')
    (h0 : d0 < n) (hg : LiveGeometry d0 s b)
    (hf : LocalPhaseFacts i s e)
    (hc : PhaseCost d0 X s) (ht : s.tag.moveCount ≤ 5*n+X) :
    let t := rearAdvance i s e
    let X' := X+ghostAdvanceCount s t
    PhaseCost d0 X' t ∧ t.tag.moveCount ≤ 5*n+X' := by
  let t := rearAdvance i s e
  obtain ⟨dx,hdx,hR,hph⟩ := phase_step_of_local i e s hf
  have hCut (h₁ : s.phase = .initial) (_ : t.phase ≠ .initial) : t.rearMoves ≤ 3*n := by
    change (rearAdvance i s e).rearMoves ≤ 3*n
    have hN : s.tag.moveCount < 2*n := by simpa [PhaseCost,h₁] using hc
    cases hg with
    | pinned hp hmark => exact (by rw [h₁] at hp; contradiction)
    | tracking hp d hr hd hgap => omega
  have hC := budget_step hc hR hdx hph (successor_initial_limit i e b s hg) hCut
  refine ⟨hC,?_⟩
  by_cases hp : t.phase = .pinned
  · have hn' := pinned_moveCount i e b b' s hm hg hb hb' hp
    change t.tag.moveCount ≤ _
    change t.tag.moveCount = s.tag.moveCount at hn'
    omega
  · exact phaseBudget_tag_unpinned hn hp hC (liveGeometry_step hn i e b b' s hm hb hb' hg)

theorem phase_account_fold {p c n d0 X : Nat} (hn : 4 ≤ n) (i : Fin n)
    (s : Observer p c n) (w : List (Fin n)) (hm : MCOV s.tag.config)
    (b : Fin n) (hb : s.tag.carrier = some b) (h0 : d0 < n)
    (hg : LiveGeometry d0 s b) (hc : PhaseCost d0 X s)
    (ht : s.tag.moveCount ≤ 5*n+X)
    (hL : ∀ u e, ¬ ended (rearFold i s (u++[e])).tag →
      LocalPhaseFacts i (rearFold i s u) e)
    (ha : ¬ ended (rearFold i s w).tag) :
    let t := rearFold i s w
    PhaseCost d0 (X+ghostAdvances i s w) t ∧
      t.tag.moveCount ≤ 5*n+ (X+ghostAdvances i s w) := by
  induction w generalizing s b X with
  | nil => simpa only [rearFold,ghostAdvances,Nat.add_zero] using And.intro hc ht
  | cons e w ih =>
    let t := rearAdvance i s e
    have hs : ¬ ended t.tag := by
      intro h
      apply ha
      rw [rearFold, rearFold_tag]
      exact ended_run t.tag w h
    have hf : LocalPhaseFacts i s e := hL [] e hs
    obtain ⟨j,hj⟩ : ∃ j, t.tag.carrier = some j := by
      cases h : t.tag.carrier
      · exact (hs h).elim
      · exact ⟨_,rfl⟩
    have hm' : MCOV t.tag.config := by
      dsimp only [t]; rw [rearAdvance_tag,projection_step]
      exact mcov_step hn s.tag.config hm e
    have hlocal (u : List (Fin n)) (f : Fin n) :
        ¬ ended (rearFold i t (u++[f])).tag → LocalPhaseFacts i (rearFold i t u) f :=
      hL (e::u) f
    obtain ⟨hc',ht'⟩ := phase_account_step hn i e b j s hm hb hj h0 hg hf hc ht
    have hrec := ih t hm' j hj (liveGeometry_step hn i e b j s hm hb hj hg) hc' ht' hlocal ha
    simpa only [rearFold,ghostAdvances,Nat.add_assoc,t] using hrec

end L4.RearTrace

#print axioms L4.RearTrace.budget_step
#print axioms L4.RearTrace.phaseBudget_tag_unpinned

#print axioms L4.RearTrace.phase_account_step
#print axioms L4.RearTrace.phase_account_fold
