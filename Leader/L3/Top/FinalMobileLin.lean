import Leader.L3.Top.GhostInput
import Leader.L3.Top.OldFlags

namespace L3
namespace MarkedCells

set_option autoImplicit false
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 4

def outPair {c : Compiled} {n : Nat} (lane : DigitLane) (time : Nat) (src : Fin n)
    (x y : DigitLaneView c) (gx gy : DigitLaneGhost c n) (acc : Bool) :
    DigitOutGhost n × DigitOutGhost n :=
  if x.leader || y.leader then (.empty, .empty)
  else if (x.out.isD && y.marker) = true then
    (if acc = true then
      ((if outT x.out then
          DigitOutGhost.unread (.afterTail ({ time := time, site := src, lane := lane } : DigitStamp n) gx.out.atom)
        else DigitOutGhost.empty), gy.out)
     else (gx.out, gy.out))
  else if (x.out.isD && !y.marker && y.out.isE) = true then
    ((if outT x.out then
          DigitOutGhost.unread (.afterTail ({ time := time, site := src, lane := lane } : DigitStamp n) gx.out.atom)
        else DigitOutGhost.empty), DigitOutGhost.packet gx.out.atom)
  else if x.out.isU = true then
    (DigitOutGhost.packet (some (.sampled ({ time := time, site := src, lane := lane } : DigitStamp n))), gy.out)
  else if (x.marker && x.out.isE && !x.leader) = true then
    (DigitOutGhost.unread (.bootstrap ({ time := time, site := src, lane := lane } : DigitStamp n)), gy.out)
  else (gx.out, gy.out)

theorem replay_out_x {c : Compiled} {n : Nat} (lane : DigitLane) (time : Nat)
    (src dst : Fin n) (x y : DigitLaneView c) (gx gy : DigitLaneGhost c n) :
    (digitLaneReplay lane time src dst x y gx gy).x.out =
      (outPair lane time src x y gx gy (replayChain x y gx gy).2).1 := by
  unfold digitLaneReplay outPair
  dsimp only
  simp only [apply_ite Prod.fst]
  rfl

theorem replayChain_acc {c : Compiled} {n : Nat} (x y : DigitLaneView c)
    (gx gy : DigitLaneGhost c n) :
    (replayChain x y gx gy).2 = true →
      ((x.leader || y.leader) = false ∧ (x.out.isD && y.marker) = true) := by
  unfold replayChain
  split
  · intro hh; simp at hh
  · rename_i h
    dsimp only
    intro hh
    refine ⟨by simpa using h, ?_⟩
    simp only [Bool.and_eq_true] at hh
    simp only [Bool.and_eq_true]
    exact hh.1.1.2

theorem replay_out_y {c : Compiled} {n : Nat} (lane : DigitLane) (time : Nat)
    (src dst : Fin n) (x y : DigitLaneView c) (gx gy : DigitLaneGhost c n) :
    (digitLaneReplay lane time src dst x y gx gy).y.out =
      (outPair lane time src x y gx gy (replayChain x y gx gy).2).2 := by
  unfold digitLaneReplay outPair replayChain
  dsimp only
  simp only [apply_ite Prod.fst, apply_ite Prod.snd]
  rfl

theorem rearm_atom {n : Nat} (b : Bool) (st : DigitStamp n) (o : Option (DigitAtom n)) :
    (if b = true then DigitOutGhost.unread (.afterTail st o) else DigitOutGhost.empty).atom
      = none := by
  split <;> rfl

theorem outPair_props {c : Compiled} {n : Nat} (lane : DigitLane) (time : Nat) (src : Fin n)
    (x y : DigitLaneView c) (gx gy : DigitLaneGhost c n) (acc : Bool)
    (hacc : acc = true → ((x.leader || y.leader) = false ∧ (x.out.isD && y.marker) = true)) :
    (∀ z, (outPair lane time src x y gx gy acc).1.atom = some z →
      gx.out.atom = some z ∨
        z = DigitAtom.sampled ({ time := time, site := src, lane := lane } : DigitStamp n)) ∧
    (∀ z, (outPair lane time src x y gx gy acc).2.atom = some z →
      gy.out.atom = some z ∨ (gx.out.atom = some z ∧
        (outPair lane time src x y gx gy acc).1.atom = none)) ∧
    (acc = true → (outPair lane time src x y gx gy acc).1.atom = none ∧
      (outPair lane time src x y gx gy acc).2.atom = gy.out.atom) := by
  unfold outPair
  split
  · rename_i h1
    refine ⟨?_, ?_, ?_⟩
    · intro z hz; exact absurd hz (by simp [DigitOutGhost.atom])
    · intro z hz; exact absurd hz (by simp [DigitOutGhost.atom])
    · intro ha; rw [(hacc ha).1] at h1; exact absurd h1 (by decide)
  · rename_i h1
    split
    · rename_i h2
      split
      · rename_i h3
        refine ⟨?_, ?_, ?_⟩
        · intro z hz; rw [rearm_atom] at hz; exact absurd hz (by simp)
        · intro z hz; exact Or.inl hz
        · intro _; exact ⟨rearm_atom _ _ _, rfl⟩
      · rename_i h3
        refine ⟨?_, ?_, ?_⟩
        · intro z hz; exact Or.inl hz
        · intro z hz; exact Or.inl hz
        · intro ha; exact absurd ha h3
    · rename_i h2
      split
      · rename_i h3
        refine ⟨?_, ?_, ?_⟩
        · intro z hz; rw [rearm_atom] at hz; exact absurd hz (by simp)
        · intro z hz
          right
          refine ⟨hz, rearm_atom _ _ _⟩
        · intro ha
          have := hacc ha
          rw [this.2] at h2
          exact absurd h2 (by decide)
      · rename_i h3
        split
        · rename_i h4
          refine ⟨?_, ?_, ?_⟩
          · intro z hz
            right
            have : DigitOutGhost.atom (DigitOutGhost.packet (some (DigitAtom.sampled
              ({ time := time, site := src, lane := lane } : DigitStamp n)))) =
              some (DigitAtom.sampled ({ time := time, site := src, lane := lane } : DigitStamp n)) := rfl
            rw [this] at hz
            exact (Option.some.inj hz).symm
          · intro z hz; exact Or.inl hz
          · intro ha
            have := hacc ha
            rw [this.2] at h2
            exact absurd h2 (by decide)
        · rename_i h4
          split
          · refine ⟨?_, ?_, ?_⟩
            · intro z hz; exact absurd hz (by simp [DigitOutGhost.atom])
            · intro z hz; exact Or.inl hz
            · intro ha
              have := hacc ha
              rw [this.2] at h2
              exact absurd h2 (by decide)
          · refine ⟨?_, ?_, ?_⟩
            · intro z hz; exact Or.inl hz
            · intro z hz; exact Or.inl hz
            · intro ha
              have := hacc ha
              rw [this.2] at h2
              exact absurd h2 (by decide)

/-- **The output atoms of one lane replay.**  The new source output atom is the old one or a
fresh sample; the new responder output atom is the old one or the source's, which then leaves
the source; and an exported packet leaves the source and keeps the responder.

Consumer: `lin_step`. -/
theorem replay_out_props {c : Compiled} {n : Nat} (lane : DigitLane) (time : Nat)
    (src dst : Fin n) (x y : DigitLaneView c) (gx gy : DigitLaneGhost c n) :
    (∀ z, (digitLaneReplay lane time src dst x y gx gy).x.out.atom = some z →
      gx.out.atom = some z ∨
        z = DigitAtom.sampled ({ time := time, site := src, lane := lane } : DigitStamp n)) ∧
    (∀ z, (digitLaneReplay lane time src dst x y gx gy).y.out.atom = some z →
      gy.out.atom = some z ∨ (gx.out.atom = some z ∧
        (digitLaneReplay lane time src dst x y gx gy).x.out.atom = none)) ∧
    (∀ ex, (digitLaneReplay lane time src dst x y gx gy).exported = some ex →
      (digitLaneReplay lane time src dst x y gx gy).x.out.atom = none ∧
      (digitLaneReplay lane time src dst x y gx gy).y.out.atom = gy.out.atom ∧
      ex.operand = gx.out.atom ∧ ex.time = time) := by
  have hacc := replayChain_acc x y gx gy
  have hP := outPair_props lane time src x y gx gy (replayChain x y gx gy).2 hacc
  rw [replay_out_x, replay_out_y]
  refine ⟨hP.1, hP.2.1, ?_⟩
  intro ex hex
  rw [replay_exported_eq] at hex
  by_cases ha : (replayChain x y gx gy).2 = true
  · rw [if_pos ha] at hex
    have hex' := Option.some.inj hex
    have h3 := hP.2.2 ha
    refine ⟨h3.1, h3.2, ?_, ?_⟩
    · rw [← hex']
    · rw [← hex']
  · rw [if_neg ha] at hex
    exact absurd hex (by simp)

end MarkedCells
end L3
