import Leader.Wu.Protocol.Repairs
import Leader.Wu.Safety.SignalCoherence
import Leader.Core.FiniteUniformStoppingTree

/-!
# A single interleader gap under the sink-extended cleanup kernel

This module formalises the `2 * n * d` cleanup bound announced in prose in
`LDC_PROGRESS.md` for one interleader gap of the *sink-extended* Algorithm-15
kernel (FIRE, label-zero egress MOVE, responder-leader SIGNAL sink, dummy
bullet sink).

## Orientation (verified against `Leader/Wu/Protocol/Repairs.lean`)

For an edge `(l, r)` with `r = ring.rightNeighbor l`:

* MOVE transports `r.bullet` to `l`.  Bullets therefore travel from the
  responder to the initiator, i.e. *against* the edge direction and towards
  decreasing ring index.
* SIGNAL writes `r.signal_B := max l.signal_B r.signal_B l.leader`.  The
  absence signal therefore travels from the initiator to the responder, i.e.
  along the edge direction and towards increasing ring index.

Consequently, in a gap whose cells are `pos 0, pos 1, …, pos d` with
`pos (k+1) = rightNeighbor (pos k)`:

* the **right** endpoint `pos d` is the shooter: it fires a live bullet at
  itself on its outgoing edge and that bullet walks down `d, d-1, …, 1`;
* the **left** endpoint `pos 0` is the victim/absorber: it is deleted by a live
  bullet at `pos 1` and it is the unconditional source of the absence signal
  that walks back up `1, 2, …, d` and re-arms the shooter.

This is the mirror image of the prose in `LDC_PROGRESS.md`, whose position `0`
is the shooter `a` and whose position `d` is the absorber `b`.  The prose
`CleanReady(a,b)` (`a.signalB = 1` and no bullet at prose positions `0..d-1`)
is therefore `CleanReady` below: `signal_B (pos d) = 1` and no bullet at ring
positions `pos 1 .. pos d`.

## What is proved

* `cleanup_service_rank` — a `Nat`-valued service rank `gapW` with
  `gapW ≤ 2 * d`, zero on the stopping set, never raised by any of the `n`
  scheduled edges, and strictly lowered by at least one edge from every
  non-terminal gap configuration.
* `sinkStep_invariant_or_done` — every scheduled edge either lands in the
  stopping set or preserves the gap invariant.
* `gap_cleanup_within_two_d` — hence a scheduler word of length at most `2 d`
  reaches the stopping set.
* `cleanup_service_rank_to_2nd` / `sink_gap_cleanup_2nd` — the division-free
  `n`-weighted Bellman form `n + Σ_e V (sinkStep e) ≤ n * V` with
  `V = n * gapW ≤ 2 * n * d`.

## Two places where the kernel contradicts the proposed plan

1. **The stopping set must contain a blocked state.**  A live bullet at
   `pos 1` in front of a victim that is shielded, or that carries the absence
   signal and therefore re-shields itself by FIRE in the same interaction, is a
   fixed point of every gap edge: MOVE refuses to delete a shielded leader, the
   SIGNAL sink clamps the live bullet's signal, and the dummy sink does not fire
   on a live bullet.  Progress can then only come from the *next* gap's shield
   cycle, which is outside this frame.  Hence `GapDone` carries the third
   disjunct `GapBlocked`; without it the plan's `cleanup_service_rank` is false.
2. **`GapSignalBelowBullets` must be part of the invariant.**  With only
   endpoints/interior/alignment, take a dummy at `pos 1`, no other bullet and
   `signal_B (pos d) = 1`.  The rank is `d + 1`, but the edge
   `(pos (d-1), pos d)` fires the responder leader, parking a fresh dummy at
   `pos d` and raising the rank to `2 d`.  So "no edge raises the rank" fails.
   The one-way geometry clause is exactly what forbids that state, it is
   established when the shooter fires out of `CleanReady`, and
   `sinkStep_signalBelowBullets_at` shows the MOVE stage's signal erasure keeps
   it true.

Additionally `adjacent_gap_dummy_stuck` shows that at `d = 1` (adjacent
leaders) a dummy bullet at the responder leader is a fixed point of the only
gap edge, so no `2 n d` cleanup bound can hold there; `GapFrame` therefore
requires `2 ≤ d`.
-/

namespace LDSinkGapCleanup

set_option autoImplicit false

open PPLLRepair
open FiniteUniformStoppingTree

/-! ## Small `Fin` helpers -/

theorem fin2_cases (x : Fin 2) :
    x = ⟨0, by omega⟩ ∨ x = ⟨1, by omega⟩ := by
  have hx : x.val = 0 ∨ x.val = 1 := by omega
  rcases hx with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

theorem fin3_cases (x : Fin 3) :
    x = ⟨0, by omega⟩ ∨ x = ⟨1, by omega⟩ ∨ x = ⟨2, by omega⟩ := by
  have hx : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 := by omega
  rcases hx with h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Fin.ext h))

theorem fin2_zero_ne_one : (⟨0, by omega⟩ : Fin 2) ≠ ⟨1, by omega⟩ := by decide

theorem fin3_zero_ne_two : (⟨0, by omega⟩ : Fin 3) ≠ ⟨2, by omega⟩ := by decide

theorem fin3_one_ne_two : (⟨1, by omega⟩ : Fin 3) ≠ ⟨2, by omega⟩ := by decide

theorem fin3_one_ne_zero : (⟨1, by omega⟩ : Fin 3) ≠ ⟨0, by omega⟩ := by decide

theorem fin3_two_ne_zero : (⟨2, by omega⟩ : Fin 3) ≠ ⟨0, by omega⟩ := by decide

/-! ## Frame for one interleader gap -/

/-- Placement data for one interleader gap of clockwise length `d` on a
directed ring: a left endpoint `low`, and `d` further cells reached by
successive `rightNeighbor` steps.  `2 ≤ d` excludes the adjacent-leader gap,
which the sink kernel provably does **not** clean (see
`adjacent_gap_dummy_stuck`).  `d < n` keeps the `d + 1` gap cells distinct. -/
structure GapFrame (n : Nat) where
  ring : DirectedRing n
  low : Fin n
  d : Nat
  hd : 2 ≤ d
  hdn : d < n

namespace GapFrame

variable {n : Nat}

/-- The ring cell at clockwise offset `t` from the gap's left endpoint. -/
def pos (F : GapFrame n) (t : Nat) : Fin n :=
  ⟨(F.low.val + t) % n, Nat.mod_lt _ F.ring.hn⟩

/-- The clockwise offset of a ring cell from the gap's left endpoint. -/
def off (F : GapFrame n) (x : Fin n) : Nat :=
  (x.val + n - F.low.val) % n

theorem off_lt (F : GapFrame n) (x : Fin n) : F.off x < n :=
  Nat.mod_lt _ F.ring.hn

theorem off_pos (F : GapFrame n) (t : Nat) (ht : t < n) :
    F.off (F.pos t) = t := by
  have hlow : F.low.val < n := F.low.isLt
  show ((F.low.val + t) % n + n - F.low.val) % n = t
  by_cases h : F.low.val + t < n
  · have e1 : (F.low.val + t) % n = F.low.val + t := Nat.mod_eq_of_lt h
    rw [e1]
    have e2 : F.low.val + t + n - F.low.val = t + n := by omega
    rw [e2, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt ht
  · have h2 : n ≤ F.low.val + t := by omega
    have e1 : (F.low.val + t) % n = F.low.val + t - n := by
      rw [Nat.mod_eq_sub_mod h2]
      exact Nat.mod_eq_of_lt (by omega)
    rw [e1]
    have e2 : F.low.val + t - n + n - F.low.val = t := by omega
    rw [e2]
    exact Nat.mod_eq_of_lt ht

theorem pos_off (F : GapFrame n) (x : Fin n) : F.pos (F.off x) = x := by
  have hA : F.low.val < n := F.low.isLt
  have hX : x.val < n := x.isLt
  apply Fin.ext
  show (F.low.val + (x.val + n - F.low.val) % n) % n = x.val
  by_cases h : F.low.val ≤ x.val
  · have h1 : n ≤ x.val + n - F.low.val := by omega
    have e1 : (x.val + n - F.low.val) % n = x.val + n - F.low.val - n := by
      rw [Nat.mod_eq_sub_mod h1]
      exact Nat.mod_eq_of_lt (by omega)
    rw [e1]
    have e2 : F.low.val + (x.val + n - F.low.val - n) = x.val := by omega
    rw [e2]
    exact Nat.mod_eq_of_lt hX
  · have e1 : (x.val + n - F.low.val) % n = x.val + n - F.low.val :=
      Nat.mod_eq_of_lt (by omega)
    rw [e1]
    have e2 : F.low.val + (x.val + n - F.low.val) = x.val + n := by omega
    rw [e2, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt hX

theorem pos_inj (F : GapFrame n) {s t : Nat} (hs : s < n) (ht : t < n)
    (h : F.pos s = F.pos t) : s = t := by
  have h' := congrArg F.off h
  rwa [off_pos F s hs, off_pos F t ht] at h'

theorem pos_ne (F : GapFrame n) {s t : Nat} (hs : s < n) (ht : t < n)
    (h : s ≠ t) : F.pos s ≠ F.pos t := fun heq => h (pos_inj F hs ht heq)

theorem pos_mod (F : GapFrame n) (t : Nat) : F.pos t = F.pos (t % n) := by
  apply Fin.ext
  show (F.low.val + t) % n = (F.low.val + t % n) % n
  simp [Nat.add_mod]

theorem pos_ne_mod (F : GapFrame n) {s t : Nat} (hs : s < n)
    (h : s ≠ t % n) : F.pos s ≠ F.pos t := by
  rw [pos_mod F t]
  exact pos_ne F hs (Nat.mod_lt _ F.ring.hn) h

theorem rightNeighbor_pos (F : GapFrame n) (t : Nat) :
    F.ring.rightNeighbor (F.pos t) = F.pos (t + 1) := by
  apply Fin.ext
  show ((F.low.val + t) % n + 1) % n = (F.low.val + (t + 1)) % n
  rw [Nat.mod_add_mod, Nat.add_assoc]

/-- The `d + 1` cells of the gap are pairwise distinct. -/
theorem gap_pos_injective (F : GapFrame n) {i j : Nat} (hi : i ≤ F.d)
    (hj : j ≤ F.d) (h : F.pos i = F.pos j) : i = j :=
  F.pos_inj (by have := F.hdn; omega) (by have := F.hdn; omega) h

end GapFrame

/-! ## The sink-extended kernel

`sinkKernel` is a verbatim copy of
`PPLLCompleteMultiLeaderCleanup.eliminateLeadersNoCollisionEgressSink`
(`Leader/Wu/Elimination/MultiLeaderCleanup.lean`, line 101).  It is repeated here because
that module's transitive import closure (≈78k lines) has no compiled artifact
in this checkout; the two definitions are syntactically identical, hence
definitionally equal, so every theorem proved here transfers to the named
kernel by `rfl`. -/

/-- The label the SIGNAL/MOVE stages accept as label-consecutive. -/
def nextLabel {ψ : Nat} (hψ : ψ > 0) (l : AgentState ψ) : Fin ψ :=
  ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩

/-- Raw Algorithm-15 kernel with egress MOVE, responder-leader signal
delivery, and a post-SIGNAL dummy sink. -/
def sinkKernel {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let nl : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let q0 := eliminateLeadersNoCollisionFire hψ l r
  let q1 := eliminateLeadersNoCollisionZeroLeaderEgressMove hψ nl q0.1 q0.2
  let q2 := eliminateLeadersNoCollisionSignalLeaderSink nl q1.1 q1.2
  dummyBulletSink q2

theorem sinkKernel_staged {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    sinkKernel hψ l r =
      dummyBulletSink
        (eliminateLeadersNoCollisionSignalLeaderSink (nextLabel hψ l)
          (eliminateLeadersNoCollisionZeroLeaderEgressMove hψ (nextLabel hψ l)
            (eliminateLeadersNoCollisionFire hψ l r).1
            (eliminateLeadersNoCollisionFire hψ l r).2).1
          (eliminateLeadersNoCollisionZeroLeaderEgressMove hψ (nextLabel hψ l)
            (eliminateLeadersNoCollisionFire hψ l r).1
            (eliminateLeadersNoCollisionFire hψ l r).2).2) := rfl

/-! ## Top index of a decidable property along the gap -/

/-- `topIdx P m` is the largest `k ≤ m` with `P k`, or `0` when there is
none.  Index `0` is deliberately never inspected: in the gap frame it is the
victim endpoint, which is treated separately. -/
def topIdx (P : Nat → Bool) : Nat → Nat
  | 0 => 0
  | m + 1 => if P (m + 1) then m + 1 else topIdx P m

theorem topIdx_le (P : Nat → Bool) : ∀ m : Nat, topIdx P m ≤ m := by
  intro m
  induction m with
  | zero => exact Nat.le_refl 0
  | succ m ih =>
      simp only [topIdx]
      split
      · exact Nat.le_refl _
      · exact Nat.le_succ_of_le ih

theorem topIdx_succ_pos (P : Nat → Bool) (m : Nat) (hp : P (m + 1) = true) :
    topIdx P (m + 1) = m + 1 := by
  simp [topIdx, hp]

theorem topIdx_succ_neg (P : Nat → Bool) (m : Nat) (hp : P (m + 1) = false) :
    topIdx P (m + 1) = topIdx P m := by
  simp [topIdx, hp]

theorem topIdx_holds (P : Nat → Bool) :
    ∀ m : Nat, 0 < topIdx P m → P (topIdx P m) = true := by
  intro m
  induction m with
  | zero => intro h; exact absurd h (by simp [topIdx])
  | succ m ih =>
      intro h
      cases hp : P (m + 1) with
      | true => rw [topIdx_succ_pos P m hp]; exact hp
      | false =>
          rw [topIdx_succ_neg P m hp] at h ⊢
          exact ih h

theorem topIdx_ge (P : Nat → Bool) :
    ∀ (m k : Nat), k ≤ m → P k = true → k ≤ topIdx P m := by
  intro m
  induction m with
  | zero => intro k hk _; exact hk
  | succ m ih =>
      intro k hk hp
      cases hp1 : P (m + 1) with
      | true => rw [topIdx_succ_pos P m hp1]; exact hk
      | false =>
          rw [topIdx_succ_neg P m hp1]
          have hk' : k ≤ m := by
            rcases Nat.lt_or_ge k (m + 1) with h | h
            · omega
            · have hkeq : k = m + 1 := by omega
              rw [hkeq] at hp
              rw [hp] at hp1
              exact absurd hp1 (by simp)
          exact ih k hk' hp

theorem topIdx_above (P : Nat → Bool) {m k : Nat} (hk : topIdx P m < k)
    (hkm : k ≤ m) : P k = false := by
  cases hp : P k with
  | false => rfl
  | true => exact absurd (topIdx_ge P m k hkm hp) (by omega)

theorem topIdx_le_of (P : Nat → Bool) {m t : Nat}
    (h : ∀ k, t < k → k ≤ m → P k = false) : topIdx P m ≤ t := by
  rcases Nat.lt_or_ge t (topIdx P m) with hlt | hge
  · have hpos : 0 < topIdx P m := by omega
    have h1 := topIdx_holds P m hpos
    have h2 := h (topIdx P m) hlt (topIdx_le P m)
    rw [h1] at h2
    exact absurd h2 (by simp)
  · exact hge

theorem topIdx_congr (P Q : Nat → Bool) :
    ∀ m : Nat, (∀ k, 1 ≤ k → k ≤ m → P k = Q k) → topIdx P m = topIdx Q m := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
      intro h
      have hPQ := h (m + 1) (by omega) (Nat.le_refl _)
      cases hp : P (m + 1) with
      | true =>
          rw [topIdx_succ_pos P m hp, topIdx_succ_pos Q m (by rw [← hPQ]; exact hp)]
      | false =>
          rw [topIdx_succ_neg P m hp, topIdx_succ_neg Q m (by rw [← hPQ]; exact hp)]
          exact ih (fun k hk1 hk2 => h k hk1 (by omega))

/-! ## Stage laws

Frame and firing laws for the four stages of `sinkKernel`. -/

section Stages

variable {ψ : Nat}

theorem fire_eq_self (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = false ∨ l.signal_B = ⟨0, by omega⟩)
    (hr : r.leader = false ∨ r.signal_B = ⟨0, by omega⟩) :
    eliminateLeadersNoCollisionFire hψ l r = (l, r) := by
  rcases hl with h | h <;> rcases hr with h' | h' <;>
    simp [eliminateLeadersNoCollisionFire, h, h']

theorem fire_left_eq (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = false ∨ l.signal_B = ⟨0, by omega⟩) :
    (eliminateLeadersNoCollisionFire hψ l r).1 = l := by
  rcases hl with h | h <;> simp [eliminateLeadersNoCollisionFire, h]

theorem fire_right_eq (hψ : ψ > 0) (l r : AgentState ψ)
    (hr : r.leader = false ∨ r.signal_B = ⟨0, by omega⟩) :
    (eliminateLeadersNoCollisionFire hψ l r).2 = r := by
  rcases hr with h | h <;> simp [eliminateLeadersNoCollisionFire, h]

theorem fire_labels (hψ : ψ > 0) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionFire hψ l r).1.label = l.label ∧
      (eliminateLeadersNoCollisionFire hψ l r).2.label = r.label := by
  constructor <;>
    (simp only [eliminateLeadersNoCollisionFire]
     repeat (first | rfl | split))

theorem fire_leaders (hψ : ψ > 0) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionFire hψ l r).1.leader = l.leader ∧
      (eliminateLeadersNoCollisionFire hψ l r).2.leader = r.leader := by
  constructor <;>
    (simp only [eliminateLeadersNoCollisionFire]
     repeat (first | rfl | split))

theorem move_eq_self_of_bullet_zero (hψ : ψ > 0) (nl : Fin ψ)
    (l r : AgentState ψ) (hb : r.bullet = ⟨0, by omega⟩) :
    eliminateLeadersNoCollisionZeroLeaderEgressMove hψ nl l r = (l, r) := by
  simp [eliminateLeadersNoCollisionZeroLeaderEgressMove, hb]

theorem move_aligned_follower (hψ : ψ > 0) (nl : Fin ψ) (l r : AgentState ψ)
    (hl : l.leader = false) (hb : 0 < r.bullet.val) (ha : r.label = nl) :
    eliminateLeadersNoCollisionZeroLeaderEgressMove hψ nl l r =
      ({ l with bullet := r.bullet, signal_B := ⟨0, by omega⟩ },
       { r with bullet := ⟨0, by omega⟩ }) := by
  simp only [eliminateLeadersNoCollisionZeroLeaderEgressMove]
  rw [if_neg (by simp [hl]), if_pos ⟨hb, hl⟩, if_pos (Or.inl ha)]

theorem move_leader_cases (hψ : ψ > 0) (nl : Fin ψ) (l r : AgentState ψ)
    (hl : l.leader = true) :
    eliminateLeadersNoCollisionZeroLeaderEgressMove hψ nl l r = (l, r) ∨
      eliminateLeadersNoCollisionZeroLeaderEgressMove hψ nl l r =
        ({ l with leader := false }, { r with bullet := ⟨1, by omega⟩ }) := by
  simp only [eliminateLeadersNoCollisionZeroLeaderEgressMove]
  split
  · split
    · exact Or.inr rfl
    · exact Or.inl rfl
  · rw [if_neg (by simp [hl])]
    exact Or.inl rfl

theorem move_right_leader (hψ : ψ > 0) (nl : Fin ψ) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionZeroLeaderEgressMove hψ nl l r).2.leader =
      r.leader := by
  simp only [eliminateLeadersNoCollisionZeroLeaderEgressMove]
  repeat (first | rfl | split)

theorem move_labels (hψ : ψ > 0) (nl : Fin ψ) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionZeroLeaderEgressMove hψ nl l r).1.label =
        l.label ∧
      (eliminateLeadersNoCollisionZeroLeaderEgressMove hψ nl l r).2.label =
        r.label := by
  constructor <;>
    (simp only [eliminateLeadersNoCollisionZeroLeaderEgressMove]
     repeat (first | rfl | split))

theorem move_left_leader_of_follower (hψ : ψ > 0) (nl : Fin ψ)
    (l r : AgentState ψ) (hl : l.leader = false) :
    (eliminateLeadersNoCollisionZeroLeaderEgressMove hψ nl l r).1.leader =
      false := by
  simp [eliminateLeadersNoCollisionZeroLeaderEgressMove, hl]
  repeat (first | rfl | split)

theorem signal_left (nl : Fin ψ) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionSignalLeaderSink nl l r).1 = l := rfl

theorem signal_right_bullet (nl : Fin ψ) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionSignalLeaderSink nl l r).2.bullet =
      r.bullet := by
  simp only [eliminateLeadersNoCollisionSignalLeaderSink]
  repeat (first | rfl | split)

theorem signal_right_leader (nl : Fin ψ) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionSignalLeaderSink nl l r).2.leader =
      r.leader := by
  simp only [eliminateLeadersNoCollisionSignalLeaderSink]
  repeat (first | rfl | split)

theorem signal_right_label (nl : Fin ψ) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionSignalLeaderSink nl l r).2.label =
      r.label := by
  simp only [eliminateLeadersNoCollisionSignalLeaderSink]
  repeat (first | rfl | split)

theorem signal_right_one (nl : Fin ψ) (l r : AgentState ψ)
    (hcond : r.label = nl ∨ l.leader = true ∨ r.leader = true)
    (hnl : r.bullet ≠ ⟨2, by omega⟩)
    (hsrc : l.leader = true ∨ l.signal_B = ⟨1, by omega⟩) :
    (eliminateLeadersNoCollisionSignalLeaderSink nl l r).2.signal_B =
      ⟨1, by omega⟩ := by
  simp only [eliminateLeadersNoCollisionSignalLeaderSink]
  split
  · next =>
      rcases fin3_cases r.bullet with hb | hb | hb
      · rcases hsrc with hx | hx
        · rcases fin2_cases l.signal_B with h1 | h1 <;>
            rcases fin2_cases r.signal_B with h2 | h2 <;>
            rw [hx, h1, h2, hb] <;> repeat (first | rfl | assumption | split)
        · cases hL : l.leader <;>
            rcases fin2_cases r.signal_B with h2 | h2 <;>
            rw [hx, h2, hb] <;> repeat (first | rfl | assumption | split)
      · rcases hsrc with hx | hx
        · rcases fin2_cases l.signal_B with h1 | h1 <;>
            rcases fin2_cases r.signal_B with h2 | h2 <;>
            rw [hx, h1, h2, hb] <;> repeat (first | rfl | assumption | split)
        · cases hL : l.leader <;>
            rcases fin2_cases r.signal_B with h2 | h2 <;>
            rw [hx, h2, hb] <;> repeat (first | rfl | assumption | split)
      · exact absurd hb hnl
  · next hc => exact absurd hcond hc

theorem signal_right_eq_of_no_source (nl : Fin ψ) (l r : AgentState ψ)
    (hl : l.leader = false) (hs : l.signal_B = ⟨0, by omega⟩)
    (hnl : r.bullet ≠ ⟨2, by omega⟩) :
    (eliminateLeadersNoCollisionSignalLeaderSink nl l r).2.signal_B =
      r.signal_B := by
  simp only [eliminateLeadersNoCollisionSignalLeaderSink]
  rcases fin2_cases r.signal_B with h | h <;>
    rcases fin3_cases r.bullet with hb | hb | hb <;>
      first
        | exact absurd hb hnl
        | (rw [hl, hs, h, hb]; repeat (first | rfl | assumption | split))

theorem sink_right_signal (q : AgentState ψ × AgentState ψ) :
    (dummyBulletSink q).2.signal_B = q.2.signal_B := by
  simp only [dummyBulletSink]
  repeat (first | rfl | split)

theorem sink_right_label (q : AgentState ψ × AgentState ψ) :
    (dummyBulletSink q).2.label = q.2.label := by
  simp only [dummyBulletSink]
  repeat (first | rfl | split)

theorem sink_right_bullet_cases (q : AgentState ψ × AgentState ψ) :
    (dummyBulletSink q).2.bullet = q.2.bullet ∨
      (dummyBulletSink q).2.bullet = ⟨0, by omega⟩ := by
  simp only [dummyBulletSink]
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

end Stages

/-! ## Kernel laws for one scheduled edge

All laws are stated for `sinkKernel hψ l r` where `r` is the right neighbour
(the responder) of `l`. -/

section KernelLaws

variable {ψ : Nat}

theorem move_leader_not_live (hψ : ψ > 0) (nl : Fin ψ) (l r : AgentState ψ)
    (hl : l.leader = true) (hb : r.bullet ≠ ⟨2, by omega⟩) :
    eliminateLeadersNoCollisionZeroLeaderEgressMove hψ nl l r = (l, r) := by
  simp only [eliminateLeadersNoCollisionZeroLeaderEgressMove]
  split
  · split
    · next hc => exact absurd hc.1 hb
    · rfl
  · split
    · next hc => rw [hl] at hc; exact absurd hc.2 (by simp)
    · rfl

/-- Labels are inert under the whole kernel. -/
theorem sinkKernel_labels (hψ : ψ > 0) (l r : AgentState ψ) :
    (sinkKernel hψ l r).1.label = l.label ∧
      (sinkKernel hψ l r).2.label = r.label := by
  rw [sinkKernel_staged]
  constructor
  · rw [dummyBulletSink_left_eq, signal_left]
    exact (move_labels hψ (nextLabel hψ l) _ _).1.trans (fire_labels hψ l r).1
  · rw [sink_right_label, signal_right_label]
    exact (move_labels hψ (nextLabel hψ l) _ _).2.trans (fire_labels hψ l r).2

/-- The responder's leader bit is never changed. -/
theorem sinkKernel_right_leader (hψ : ψ > 0) (l r : AgentState ψ) :
    (sinkKernel hψ l r).2.leader = r.leader := by
  rw [sinkKernel_staged, (dummyBulletSink_leader_frame _).2,
    signal_right_leader, move_right_leader]
  exact (fire_leaders hψ l r).2

/-- A follower initiator stays a follower: no rule ever sets `leader := true`. -/
theorem sinkKernel_left_leader_false (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = false) : (sinkKernel hψ l r).1.leader = false := by
  rw [sinkKernel_staged, dummyBulletSink_left_eq, signal_left]
  apply move_left_leader_of_follower
  rw [(fire_leaders hψ l r).1]
  exact hl

/-- MOVE law in gap form: a bullet on a label-aligned follower edge steps one
cell towards the initiator, i.e. counter-clockwise, and erases the initiator's
absence signal.  The responder keeps its own signal. -/
theorem sinkKernel_move_down (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = false)
    (hrfire : r.leader = false ∨ r.signal_B = ⟨0, by omega⟩)
    (hb : 0 < r.bullet.val)
    (ha : r.label = nextLabel hψ l) :
    (sinkKernel hψ l r).1.bullet = r.bullet ∧
      (sinkKernel hψ l r).1.signal_B = ⟨0, by omega⟩ ∧
      (sinkKernel hψ l r).2.bullet = ⟨0, by omega⟩ ∧
      (sinkKernel hψ l r).2.signal_B = r.signal_B := by
  have hfire := fire_eq_self hψ l r (Or.inl hl) hrfire
  have hmove := move_aligned_follower hψ (nextLabel hψ l) l r hl hb ha
  have hq : sinkKernel hψ l r =
      dummyBulletSink (eliminateLeadersNoCollisionSignalLeaderSink
        (nextLabel hψ l)
        ({ l with bullet := r.bullet, signal_B := ⟨0, by omega⟩ })
        ({ r with bullet := ⟨0, by omega⟩ })) := by
    rw [sinkKernel_staged, hfire]
    dsimp only
    rw [hmove]
  have hrb : (eliminateLeadersNoCollisionSignalLeaderSink (nextLabel hψ l)
      ({ l with bullet := r.bullet, signal_B := ⟨0, by omega⟩ })
      ({ r with bullet := ⟨0, by omega⟩ })).2.bullet = ⟨0, by omega⟩ :=
    signal_right_bullet _ _ _
  have hsink := dummyBulletSink_eq_of_responder_bullet_zero _ hrb
  rw [hq, hsink]
  refine ⟨rfl, rfl, hrb, ?_⟩
  exact signal_right_eq_of_no_source _ _ _ hl rfl fin3_zero_ne_two

/-- Idle law: a bullet-free label-aligned follower edge only propagates the
absence signal clockwise. -/
theorem sinkKernel_idle (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = false)
    (hrfire : r.leader = false ∨ r.signal_B = ⟨0, by omega⟩)
    (hb : r.bullet = ⟨0, by omega⟩)
    (ha : r.label = nextLabel hψ l) :
    (sinkKernel hψ l r).1 = l ∧
      (sinkKernel hψ l r).2.bullet = ⟨0, by omega⟩ ∧
      (l.signal_B = ⟨1, by omega⟩ →
        (sinkKernel hψ l r).2.signal_B = ⟨1, by omega⟩) ∧
      (r.signal_B = ⟨1, by omega⟩ →
        (sinkKernel hψ l r).2.signal_B = ⟨1, by omega⟩) := by
  have hfire := fire_eq_self hψ l r (Or.inl hl) hrfire
  have hmove := move_eq_self_of_bullet_zero hψ (nextLabel hψ l) l r hb
  have hq : sinkKernel hψ l r =
      dummyBulletSink (eliminateLeadersNoCollisionSignalLeaderSink
        (nextLabel hψ l) l r) := by
    rw [sinkKernel_staged, hfire]
    dsimp only
    rw [hmove]
  have hnotlive : r.bullet ≠ ⟨2, by omega⟩ := by rw [hb]; simp
  have hrb : (eliminateLeadersNoCollisionSignalLeaderSink
      (nextLabel hψ l) l r).2.bullet = ⟨0, by omega⟩ :=
    (signal_right_bullet _ _ _).trans hb
  have hsink := dummyBulletSink_eq_of_responder_bullet_zero _ hrb
  rw [hq, hsink]
  refine ⟨rfl, hrb, ?_, ?_⟩
  · intro hls
    exact signal_right_one _ _ _ (Or.inl ha) hnotlive (Or.inr hls)
  · intro hrs
    rcases fin2_cases l.signal_B with hls | hls
    · rw [signal_right_eq_of_no_source _ _ _ hl hls hnotlive]
      exact hrs
    · exact signal_right_one _ _ _ (Or.inl ha) hnotlive (Or.inr hls)

/-- Victim law: a leader initiator absorbs every non-live responder bullet
(the post-SIGNAL dummy sink) and seeds the returning absence signal.  This is
the boundary law the base kernel lacks. -/
theorem sinkKernel_victim_absorb (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = true) (hr : r.leader = false)
    (hb : r.bullet ≠ ⟨2, by omega⟩) :
    (sinkKernel hψ l r).2.bullet = ⟨0, by omega⟩ ∧
      (sinkKernel hψ l r).2.signal_B = ⟨1, by omega⟩ ∧
      (sinkKernel hψ l r).1.leader = true := by
  have hfire2 := fire_right_eq hψ l r (Or.inl hr)
  have hfire1 : (eliminateLeadersNoCollisionFire hψ l r).1.leader = true :=
    (fire_leaders hψ l r).1.trans hl
  have hmove : eliminateLeadersNoCollisionZeroLeaderEgressMove hψ
      (nextLabel hψ l) (eliminateLeadersNoCollisionFire hψ l r).1 r =
      ((eliminateLeadersNoCollisionFire hψ l r).1, r) :=
    move_leader_not_live hψ (nextLabel hψ l) _ r hfire1 hb
  have hq : sinkKernel hψ l r =
      dummyBulletSink (eliminateLeadersNoCollisionSignalLeaderSink
        (nextLabel hψ l) (eliminateLeadersNoCollisionFire hψ l r).1 r) := by
    rw [sinkKernel_staged, hfire2, hmove]
  have hsig : (eliminateLeadersNoCollisionSignalLeaderSink
      (nextLabel hψ l) (eliminateLeadersNoCollisionFire hψ l r).1 r).2.signal_B
      = ⟨1, by omega⟩ :=
    signal_right_one _ _ _ (Or.inr (Or.inl hfire1)) hb (Or.inl hfire1)
  have hbul : (eliminateLeadersNoCollisionSignalLeaderSink
      (nextLabel hψ l) (eliminateLeadersNoCollisionFire hψ l r).1 r).2.bullet
      = r.bullet := signal_right_bullet _ _ _
  have hlead2 : (eliminateLeadersNoCollisionSignalLeaderSink
      (nextLabel hψ l) (eliminateLeadersNoCollisionFire hψ l r).1 r).2.leader
      = false := (signal_right_leader _ _ _).trans hr
  rw [hq]
  rcases fin3_cases r.bullet with h0 | h1 | h2
  · have hz : (eliminateLeadersNoCollisionSignalLeaderSink
        (nextLabel hψ l) (eliminateLeadersNoCollisionFire hψ l r).1
        r).2.bullet = ⟨0, by omega⟩ := hbul.trans h0
    rw [dummyBulletSink_eq_of_responder_bullet_zero _ hz]
    exact ⟨hz, hsig, hfire1⟩
  · have hd : (eliminateLeadersNoCollisionSignalLeaderSink
        (nextLabel hψ l) (eliminateLeadersNoCollisionFire hψ l r).1
        r).2.bullet = ⟨1, by omega⟩ := hbul.trans h1
    refine ⟨dummyBulletSink_clears _ hfire1 hlead2 hd, ?_, ?_⟩
    · rw [sink_right_signal]; exact hsig
    · rw [dummyBulletSink_left_eq]; exact hfire1
  · exact absurd h2 hb

/-- A live responder bullet at a leader initiator never disappears: either it
deletes the leader and becomes a dummy, or it stays live and blocked. -/
theorem sinkKernel_live_at_leader (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = true) (hr : r.leader = false)
    (hb : r.bullet = ⟨2, by omega⟩) :
    (sinkKernel hψ l r).2.bullet ≠ ⟨0, by omega⟩ := by
  have hfire2 := fire_right_eq hψ l r (Or.inl hr)
  have hfire1 : (eliminateLeadersNoCollisionFire hψ l r).1.leader = true :=
    (fire_leaders hψ l r).1.trans hl
  have hq : sinkKernel hψ l r =
      dummyBulletSink (eliminateLeadersNoCollisionSignalLeaderSink
        (nextLabel hψ l)
        (eliminateLeadersNoCollisionZeroLeaderEgressMove hψ
          (nextLabel hψ l) (eliminateLeadersNoCollisionFire hψ l r).1 r).1
        (eliminateLeadersNoCollisionZeroLeaderEgressMove hψ
          (nextLabel hψ l) (eliminateLeadersNoCollisionFire hψ l r).1 r).2) := by
    rw [sinkKernel_staged, hfire2]
  rw [hq]
  rcases move_leader_cases hψ (nextLabel hψ l)
      (eliminateLeadersNoCollisionFire hψ l r).1 r hfire1 with hm | hm
  · rw [hm]
    have hbul : (eliminateLeadersNoCollisionSignalLeaderSink
        (nextLabel hψ l) (eliminateLeadersNoCollisionFire hψ l r).1
        r).2.bullet = ⟨2, by omega⟩ := (signal_right_bullet _ _ _).trans hb
    rw [dummyBulletSink_eq_of_responder_bullet_two _ hbul, hbul]
    exact fin3_two_ne_zero
  · rw [hm]
    have hlead : (eliminateLeadersNoCollisionSignalLeaderSink
        (nextLabel hψ l)
        ({ (eliminateLeadersNoCollisionFire hψ l r).1 with leader := false })
        ({ r with bullet := ⟨1, by omega⟩ })).1.leader = false := rfl
    have hbul : (eliminateLeadersNoCollisionSignalLeaderSink
        (nextLabel hψ l)
        ({ (eliminateLeadersNoCollisionFire hψ l r).1 with leader := false })
        ({ r with bullet := ⟨1, by omega⟩ })).2.bullet = ⟨1, by omega⟩ :=
      signal_right_bullet _ _ _
    rw [dummyBulletSink_eq_of_initiator_follower _ hlead, hbul]
    exact fin3_one_ne_zero

/-- A leader initiator without the absence signal keeps its own bullet and
signal: it can only lose its leader bit. -/
theorem sinkKernel_left_frame (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = true) (hs : l.signal_B = ⟨0, by omega⟩) :
    (sinkKernel hψ l r).1.bullet = l.bullet ∧
      (sinkKernel hψ l r).1.signal_B = l.signal_B := by
  have hfire1 := fire_left_eq hψ l r (Or.inr hs)
  have hq : sinkKernel hψ l r =
      dummyBulletSink (eliminateLeadersNoCollisionSignalLeaderSink
        (nextLabel hψ l)
        (eliminateLeadersNoCollisionZeroLeaderEgressMove hψ
          (nextLabel hψ l) l
          (eliminateLeadersNoCollisionFire hψ l r).2).1
        (eliminateLeadersNoCollisionZeroLeaderEgressMove hψ
          (nextLabel hψ l) l
          (eliminateLeadersNoCollisionFire hψ l r).2).2) := by
    rw [sinkKernel_staged, hfire1]
  rw [hq, dummyBulletSink_left_eq, signal_left]
  rcases move_leader_cases hψ (nextLabel hψ l) l
      (eliminateLeadersNoCollisionFire hψ l r).2 hl with hm | hm <;>
    rw [hm] <;> exact ⟨rfl, rfl⟩

end KernelLaws

/-! ## Extra kernel laws: live clamp, idle clamp, and the `d = 1` obstruction -/

section MoreKernelLaws

variable {ψ : Nat}

theorem signal_right_zero_of_live (nl : Fin ψ) (l r : AgentState ψ)
    (hcond : r.label = nl ∨ l.leader = true ∨ r.leader = true)
    (hlive : r.bullet = ⟨2, by omega⟩) :
    (eliminateLeadersNoCollisionSignalLeaderSink nl l r).2.signal_B =
      ⟨0, by omega⟩ := by
  simp only [eliminateLeadersNoCollisionSignalLeaderSink]
  split
  · next =>
      rw [hlive]
      repeat (first | rfl | split)
  · next hc => exact absurd hcond hc

theorem move_no_kill_of_shield (hψ : ψ > 0) (nl : Fin ψ) (l r : AgentState ψ)
    (hl : l.leader = true) (hsh : l.shield = true) :
    eliminateLeadersNoCollisionZeroLeaderEgressMove hψ nl l r = (l, r) := by
  simp only [eliminateLeadersNoCollisionZeroLeaderEgressMove]
  split
  · split
    · next hc => rw [hsh] at hc; exact absurd hc.2 (by simp)
    · rfl
  · split
    · next hc => rw [hl] at hc; exact absurd hc.2 (by simp)
    · rfl

theorem fire_left_fires (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = true) (hs : l.signal_B = ⟨1, by omega⟩) :
    (eliminateLeadersNoCollisionFire hψ l r).1 =
      { l with bullet := ⟨2, by omega⟩, shield := true,
               signal_B := ⟨0, by omega⟩ } := by
  simp only [eliminateLeadersNoCollisionFire]
  rw [if_pos ⟨hl, hs⟩]

/-- A live responder bullet never keeps a positive absence signal at the
responder: either it is clamped by SIGNAL, or the interaction deletes the
initiator and the responder inherits only zero sources. -/
theorem sinkKernel_live_signal_zero (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = true) (hr : r.leader = false)
    (hb : r.bullet = ⟨2, by omega⟩) (hrs : r.signal_B = ⟨0, by omega⟩) :
    (sinkKernel hψ l r).2.signal_B = ⟨0, by omega⟩ := by
  have hfire2 := fire_right_eq hψ l r (Or.inl hr)
  rcases fin2_cases l.signal_B with hls | hls
  · have hfire1 := fire_left_eq hψ l r (Or.inr hls)
    rcases move_leader_cases hψ (nextLabel hψ l) l r hl with hm | hm
    · have hq : sinkKernel hψ l r =
          dummyBulletSink (eliminateLeadersNoCollisionSignalLeaderSink
            (nextLabel hψ l) l r) := by
        rw [sinkKernel_staged, hfire1, hfire2, hm]
      rw [hq, sink_right_signal]
      exact signal_right_zero_of_live _ _ _ (Or.inr (Or.inl hl)) hb
    · have hq : sinkKernel hψ l r =
          dummyBulletSink (eliminateLeadersNoCollisionSignalLeaderSink
            (nextLabel hψ l) ({ l with leader := false })
            ({ r with bullet := ⟨1, by omega⟩ })) := by
        rw [sinkKernel_staged, hfire1, hfire2, hm]
      rw [hq, sink_right_signal]
      have h := signal_right_eq_of_no_source (nextLabel hψ l)
        ({ l with leader := false }) ({ r with bullet := ⟨1, by omega⟩ })
        rfl hls fin3_one_ne_two
      rw [h]
      exact hrs
  · have hfire1 := fire_left_fires hψ l r hl hls
    have hmove := move_no_kill_of_shield hψ (nextLabel hψ l)
      ({ l with bullet := ⟨2, by omega⟩, shield := true,
                signal_B := ⟨0, by omega⟩ }) r hl rfl
    have hq : sinkKernel hψ l r =
        dummyBulletSink (eliminateLeadersNoCollisionSignalLeaderSink
          (nextLabel hψ l)
          ({ l with bullet := ⟨2, by omega⟩, shield := true,
                    signal_B := ⟨0, by omega⟩ }) r) := by
      rw [sinkKernel_staged, hfire1, hfire2, hmove]
    rw [hq, sink_right_signal]
    exact signal_right_zero_of_live _ _ _ (Or.inr (Or.inl hl)) hb

/-- Idle clamp: with no source on either side the responder's zero signal
survives. -/
theorem sinkKernel_idle_signal_zero (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = false)
    (hrfire : r.leader = false ∨ r.signal_B = ⟨0, by omega⟩)
    (hb : r.bullet = ⟨0, by omega⟩) (hls : l.signal_B = ⟨0, by omega⟩)
    (hrs : r.signal_B = ⟨0, by omega⟩) :
    (sinkKernel hψ l r).2.signal_B = ⟨0, by omega⟩ := by
  have hfire := fire_eq_self hψ l r (Or.inl hl) hrfire
  have hmove := move_eq_self_of_bullet_zero hψ (nextLabel hψ l) l r hb
  have hq : sinkKernel hψ l r =
      dummyBulletSink (eliminateLeadersNoCollisionSignalLeaderSink
        (nextLabel hψ l) l r) := by
    rw [sinkKernel_staged, hfire]
    dsimp only
    rw [hmove]
  rw [hq, sink_right_signal,
    signal_right_eq_of_no_source _ _ _ hl hls (by rw [hb]; exact fin3_zero_ne_two)]
  exact hrs

/-- **The `d = 1` obstruction (adjacent leaders).**  If both endpoints of the
scheduled edge are leaders and the responder carries a dummy bullet, the
interaction changes nothing: the dummy sink refuses to fire at a *leader*
responder, MOVE refuses to move a bullet past a leader initiator, and neither
leader is deleted.  The configuration is therefore a fixed point of the only
edge inside a gap of length `1`, so such a gap never becomes bullet-free and
never deletes an endpoint: no `2 n d` cleanup bound can hold at `d = 1`.  This
is why `GapFrame` requires `2 ≤ d`. -/
theorem adjacent_gap_dummy_stuck (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = true) (hr : r.leader = true)
    (hb : r.bullet = ⟨1, by omega⟩) :
    (sinkKernel hψ l r).1.leader = true ∧
      (sinkKernel hψ l r).2.leader = true ∧
      (sinkKernel hψ l r).2.bullet = ⟨1, by omega⟩ := by
  have hfireB : (eliminateLeadersNoCollisionFire hψ l r).2.bullet =
      ⟨1, by omega⟩ := by
    simp only [eliminateLeadersNoCollisionFire]
    split
    · rfl
    · exact hb
  have hfire1 : (eliminateLeadersNoCollisionFire hψ l r).1.leader = true :=
    (fire_leaders hψ l r).1.trans hl
  have hfire2 : (eliminateLeadersNoCollisionFire hψ l r).2.leader = true :=
    (fire_leaders hψ l r).2.trans hr
  have hmove := move_leader_not_live hψ (nextLabel hψ l)
    (eliminateLeadersNoCollisionFire hψ l r).1
    (eliminateLeadersNoCollisionFire hψ l r).2 hfire1
    (by rw [hfireB]; exact fin3_one_ne_two)
  have hq : sinkKernel hψ l r =
      dummyBulletSink (eliminateLeadersNoCollisionSignalLeaderSink
        (nextLabel hψ l) (eliminateLeadersNoCollisionFire hψ l r).1
        (eliminateLeadersNoCollisionFire hψ l r).2) := by
    rw [sinkKernel_staged, hmove]
  have hleadR : (eliminateLeadersNoCollisionSignalLeaderSink (nextLabel hψ l)
      (eliminateLeadersNoCollisionFire hψ l r).1
      (eliminateLeadersNoCollisionFire hψ l r).2).2.leader = true :=
    (signal_right_leader _ _ _).trans hfire2
  have hsink := dummyBulletSink_eq_of_responder_leader _ hleadR
  rw [hq, hsink]
  refine ⟨hfire1, hleadR, ?_⟩
  rw [signal_right_bullet]
  exact hfireB

end MoreKernelLaws

/-! ## The gap step -/

section Gap

variable {ψ n : Nat}

/-- One scheduled interaction of the sink kernel at edge `e`. -/
def sinkStep (hψ : ψ > 0) (F : GapFrame n) (C : Fin n → AgentState ψ)
    (e : Fin n) : Fin n → AgentState ψ :=
  updatePair C e (F.ring.rightNeighbor e)
    (sinkKernel hψ (C e) (C (F.ring.rightNeighbor e)))

/-- Cells not incident to the scheduled edge are framed. -/
theorem sinkStep_other (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (e k : Fin n) (h1 : k ≠ e)
    (h2 : k ≠ F.ring.rightNeighbor e) : sinkStep hψ F C e k = C k :=
  updatePair_other C e (F.ring.rightNeighbor e) k _ h1 h2

theorem sinkStep_pos_initiator (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (k : Nat) :
    sinkStep hψ F C (F.pos k) (F.pos k) =
      (sinkKernel hψ (C (F.pos k)) (C (F.pos (k + 1)))).1 := by
  simp only [sinkStep, GapFrame.rightNeighbor_pos, updatePair_initiator]

theorem sinkStep_pos_responder (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (k : Nat) (hk : k + 1 < n) :
    sinkStep hψ F C (F.pos k) (F.pos (k + 1)) =
      (sinkKernel hψ (C (F.pos k)) (C (F.pos (k + 1)))).2 := by
  have hne : F.pos (k + 1) ≠ F.pos k :=
    F.pos_ne (by omega) (by omega) (by omega)
  simp only [sinkStep, GapFrame.rightNeighbor_pos]
  exact updatePair_responder C (F.pos k) (F.pos (k + 1)) _ hne

/-- A gap cell that is neither endpoint of the scheduled edge is framed. -/
theorem sinkStep_pos_eq (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (k j : Nat) (hk : k < n) (hj1 : 1 ≤ j)
    (hjd : j ≤ F.d) (h1 : j ≠ k) (h2 : j ≠ k + 1) :
    sinkStep hψ F C (F.pos k) (F.pos j) = C (F.pos j) := by
  have hjn : j < n := by have := F.hdn; omega
  apply sinkStep_other
  · exact F.pos_ne hjn hk h1
  · rw [GapFrame.rightNeighbor_pos]
    apply F.pos_ne_mod hjn
    rcases Nat.lt_or_ge (k + 1) n with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt]; exact h2
    · have hk1 : k + 1 = n := by omega
      rw [hk1, Nat.mod_self]
      omega

/-! ## Gap predicates -/

/-- Both endpoints are still leaders. -/
def GapEndpointsPresent (F : GapFrame n) (C : Fin n → AgentState ψ) : Prop :=
  (C (F.pos 0)).leader = true ∧ (C (F.pos F.d)).leader = true

/-- The interior of the gap is leader-free. -/
def GapInteriorFollowers (F : GapFrame n) (C : Fin n → AgentState ψ) : Prop :=
  ∀ k, 1 ≤ k → k < F.d → (C (F.pos k)).leader = false

/-- Every gap edge is label-consecutive. -/
def GapLabelAligned (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) : Prop :=
  ∀ k, k < F.d → (C (F.pos (k + 1))).label = nextLabel hψ (C (F.pos k))

/-- One-way geometry: the returning absence signal is strictly below every
bullet still travelling towards the victim. -/
def GapSignalBelowBullets (F : GapFrame n)
    (C : Fin n → AgentState ψ) : Prop :=
  ∀ k j, 1 ≤ k → k ≤ F.d → (C (F.pos k)).bullet ≠ ⟨0, by omega⟩ →
    k ≤ j → j ≤ F.d → (C (F.pos j)).signal_B = ⟨0, by omega⟩

def GapInvariant (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) : Prop :=
  GapEndpointsPresent F C ∧ GapInteriorFollowers F C ∧
    GapLabelAligned hψ F C ∧ GapSignalBelowBullets F C

/-- `CleanReady`: the shooter `pos d` carries the absence signal and the whole
sector `pos 1 … pos d` is bullet-free.  (Mirror image of the prose
`CleanReady(a,b)` of `LDC_PROGRESS.md`.) -/
def CleanReady (F : GapFrame n) (C : Fin n → AgentState ψ) : Prop :=
  (C (F.pos F.d)).signal_B = ⟨1, by omega⟩ ∧
    ∀ k, 1 ≤ k → k ≤ F.d → (C (F.pos k)).bullet = ⟨0, by omega⟩

def EndpointDeleted (F : GapFrame n) (C : Fin n → AgentState ψ) : Prop :=
  (C (F.pos 0)).leader = false ∨ (C (F.pos F.d)).leader = false

/-- The shot has arrived at the victim but the victim is protected: it is
shielded, or it carries the absence signal and will therefore re-shield in the
same interaction.  No gap edge can make progress from here; only the *next*
gap's shield cycle can.  This state is genuinely reachable, so it must be part
of the stopping set. -/
def GapBlocked (F : GapFrame n) (C : Fin n → AgentState ψ) : Prop :=
  (C (F.pos 1)).bullet = ⟨2, by omega⟩ ∧
    (∀ k, 2 ≤ k → k ≤ F.d → (C (F.pos k)).bullet = ⟨0, by omega⟩) ∧
    ((C (F.pos 0)).shield = true ∨
      (C (F.pos 0)).signal_B = ⟨1, by omega⟩)

def GapDone (F : GapFrame n) (C : Fin n → AgentState ψ) : Prop :=
  CleanReady F C ∨ EndpointDeleted F C ∨ GapBlocked F C

/-! ## The service rank -/

/-- Position of the bullet nearest the shooter, `0` if the sector is
bullet-free. -/
def bulletTop (F : GapFrame n) (C : Fin n → AgentState ψ) : Nat :=
  topIdx (fun k => decide (0 < (C (F.pos k)).bullet.val)) F.d

/-- Position of the signal front nearest the shooter, `0` if the sector
carries no signal (the victim `pos 0` is an unconditional source). -/
def signalTop (F : GapFrame n) (C : Fin n → AgentState ψ) : Nat :=
  topIdx (fun k => decide ((C (F.pos k)).signal_B.val = 1)) F.d

theorem bulletTop_le (F : GapFrame n) (C : Fin n → AgentState ψ) :
    bulletTop F C ≤ F.d := topIdx_le _ _

theorem signalTop_le (F : GapFrame n) (C : Fin n → AgentState ψ) :
    signalTop F C ≤ F.d := topIdx_le _ _

theorem bulletTop_zero_at (F : GapFrame n) (C : Fin n → AgentState ψ)
    {j : Nat} (h : bulletTop F C < j) (hj : j ≤ F.d) :
    (C (F.pos j)).bullet = ⟨0, by omega⟩ := by
  have := topIdx_above (fun k => decide (0 < (C (F.pos k)).bullet.val)) h hj
  apply Fin.ext
  simp only [decide_eq_false_iff_not, Nat.not_lt, Nat.le_zero] at this
  exact this

theorem bulletTop_ge_of (F : GapFrame n) (C : Fin n → AgentState ψ)
    {j : Nat} (h2 : j ≤ F.d) (h3 : (C (F.pos j)).bullet ≠ ⟨0, by omega⟩) :
    j ≤ bulletTop F C := by
  apply topIdx_ge _ _ _ h2
  simp only [decide_eq_true_eq]
  rcases Nat.eq_zero_or_pos (C (F.pos j)).bullet.val with h | h
  · exact absurd (Fin.ext h) h3
  · exact h

theorem bulletTop_ne_zero (F : GapFrame n) (C : Fin n → AgentState ψ)
    (h : 0 < bulletTop F C) :
    (C (F.pos (bulletTop F C))).bullet ≠ ⟨0, by omega⟩ := by
  intro hcon
  have h2 := topIdx_holds (fun k => decide (0 < (C (F.pos k)).bullet.val)) F.d h
  simp only [decide_eq_true_eq] at h2
  unfold bulletTop at hcon
  rw [hcon] at h2
  simp at h2

theorem bulletTop_eq_zero_of (F : GapFrame n) (C : Fin n → AgentState ψ)
    (h : ∀ j, 1 ≤ j → j ≤ F.d → (C (F.pos j)).bullet = ⟨0, by omega⟩) :
    bulletTop F C = 0 := by
  apply Nat.le_antisymm _ (Nat.zero_le _)
  apply topIdx_le_of
  intro k hk hkd
  simp only [decide_eq_false_iff_not, Nat.not_lt, Nat.le_zero]
  rw [h k (by omega) hkd]

theorem signalTop_one_at (F : GapFrame n) (C : Fin n → AgentState ψ)
    (h : 0 < signalTop F C) :
    (C (F.pos (signalTop F C))).signal_B = ⟨1, by omega⟩ := by
  have := topIdx_holds (fun k => decide ((C (F.pos k)).signal_B.val = 1)) _ h
  simp only [decide_eq_true_eq] at this
  exact Fin.ext this

theorem signalTop_ge_of (F : GapFrame n) (C : Fin n → AgentState ψ)
    {j : Nat} (h2 : j ≤ F.d)
    (h3 : (C (F.pos j)).signal_B = ⟨1, by omega⟩) :
    j ≤ signalTop F C := by
  apply topIdx_ge _ _ _ h2
  simp only [decide_eq_true_eq, h3]

theorem signalTop_zero_at (F : GapFrame n) (C : Fin n → AgentState ψ)
    {j : Nat} (h : signalTop F C < j) (hj : j ≤ F.d) :
    (C (F.pos j)).signal_B = ⟨0, by omega⟩ := by
  have hthis :=
    topIdx_above (fun k => decide ((C (F.pos k)).signal_B.val = 1)) h hj
  simp only [decide_eq_false_iff_not] at hthis
  rcases fin2_cases (C (F.pos j)).signal_B with h0 | h1
  · exact h0
  · exact absurd (by rw [h1]) hthis

/-- Rank: `d + (distance the front bullet still has to travel)` while bullets
remain, and `d - (signal front position)` once the sector is bullet-free. -/
def gapRank (F : GapFrame n) (C : Fin n → AgentState ψ) : Nat :=
  if bulletTop F C = 0 then F.d - signalTop F C else F.d + bulletTop F C

theorem gapRank_le (F : GapFrame n) (C : Fin n → AgentState ψ) :
    gapRank F C ≤ 2 * F.d := by
  unfold gapRank
  split
  · have := signalTop_le F C
    omega
  · have := bulletTop_le F C
    omega

end Gap

/-! ## Two further kernel laws: the victim kill -/

section KillLaw

variable {ψ : Nat}

theorem move_kill (hψ : ψ > 0) (nl : Fin ψ) (l r : AgentState ψ)
    (hl : l.leader = true) (hsh : l.shield = false)
    (hb : r.bullet = ⟨2, by omega⟩) :
    eliminateLeadersNoCollisionZeroLeaderEgressMove hψ nl l r =
      ({ l with leader := false }, { r with bullet := ⟨1, by omega⟩ }) := by
  simp only [eliminateLeadersNoCollisionZeroLeaderEgressMove]
  split
  · split
    · rfl
    · next hc => exact absurd ⟨hb, hsh⟩ hc
  · next hc => exact absurd ⟨by rw [hb]; exact Nat.succ_pos 1, hl⟩ hc

/-- A live bullet deletes an unshielded, unsignalled leader initiator. -/
theorem sinkKernel_kill (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = true) (hsh : l.shield = false)
    (hs : l.signal_B = ⟨0, by omega⟩) (hr : r.leader = false)
    (hb : r.bullet = ⟨2, by omega⟩) :
    (sinkKernel hψ l r).1.leader = false := by
  have hfire1 := fire_left_eq hψ l r (Or.inr hs)
  have hfire2 := fire_right_eq hψ l r (Or.inl hr)
  have hmove := move_kill hψ (nextLabel hψ l) l r hl hsh hb
  have hq : sinkKernel hψ l r =
      dummyBulletSink (eliminateLeadersNoCollisionSignalLeaderSink
        (nextLabel hψ l) ({ l with leader := false })
        ({ r with bullet := ⟨1, by omega⟩ })) := by
    rw [sinkKernel_staged, hfire1, hfire2, hmove]
  rw [hq, dummyBulletSink_left_eq, signal_left]

end KillLaw

/-! ## Per-edge behaviour of the gap -/

section GapDynamics

variable {ψ n : Nat}

/-- Under the invariant, a non-terminal gap never has the absence signal at
the shooter: either the sector still carries a bullet (and then
`GapSignalBelowBullets` forbids it), or the sector is clean and the signal at
the shooter would be `CleanReady`. -/
theorem signal_shooter_zero (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (hinv : GapInvariant hψ F C)
    (hdone : ¬ GapDone F C) :
    (C (F.pos F.d)).signal_B = ⟨0, by omega⟩ := by
  rcases Nat.eq_zero_or_pos (bulletTop F C) with h0 | hpos
  · rcases fin2_cases (C (F.pos F.d)).signal_B with h | h
    · exact h
    · exact absurd (Or.inl ⟨h, fun k hk1 hkd =>
        bulletTop_zero_at F C (by omega) hkd⟩) hdone
  · exact hinv.2.2.2 (bulletTop F C) F.d (by omega) (bulletTop_le F C)
      (bulletTop_ne_zero F C hpos) (bulletTop_le F C) (Nat.le_refl _)

/-- Responder side of an interior gap edge never fires. -/
theorem interior_no_right_fire (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (hinv : GapInvariant hψ F C)
    (hdone : ¬ GapDone F C) (j : Nat) (hj1 : 1 ≤ j) (hjd : j ≤ F.d) :
    (C (F.pos j)).leader = false ∨
      (C (F.pos j)).signal_B = ⟨0, by omega⟩ := by
  rcases Nat.lt_or_ge j F.d with hlt | hge
  · exact Or.inl (hinv.2.1 j hj1 hlt)
  · have hjd' : j = F.d := by omega
    rw [hjd']
    exact Or.inr (signal_shooter_zero hψ F C hinv hdone)

/-- A gap cell that was bullet-free and whose scheduled edge cannot bring a
bullet stays bullet-free. -/
theorem sinkStep_keeps_bullet_zero (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (hinv : GapInvariant hψ F C)
    (hdone : ¬ GapDone F C) (k j : Nat) (hkn : k < n) (hj1 : 1 ≤ j)
    (hjd : j ≤ F.d) (hCj : (C (F.pos j)).bullet = ⟨0, by omega⟩)
    (hnext : j < F.d → (C (F.pos (j + 1))).bullet = ⟨0, by omega⟩) :
    (sinkStep hψ F C (F.pos k) (F.pos j)).bullet = ⟨0, by omega⟩ := by
  by_cases hjk : j = k
  · subst hjk
    rw [sinkStep_pos_initiator]
    rcases Nat.lt_or_ge j F.d with hlt | hge
    · have hidle := sinkKernel_idle hψ (C (F.pos j)) (C (F.pos (j + 1)))
        (hinv.2.1 j hj1 hlt)
        (interior_no_right_fire hψ F C hinv hdone (j + 1) (by omega)
          (by omega))
        (hnext hlt) (hinv.2.2.1 j hlt)
      rw [hidle.1]
      exact hCj
    · have hjd' : j = F.d := by omega
      have hlead : (C (F.pos j)).leader = true := by
        rw [hjd']; exact hinv.1.2
      have hsig : (C (F.pos j)).signal_B = ⟨0, by omega⟩ := by
        rw [hjd']; exact signal_shooter_zero hψ F C hinv hdone
      have hframe := sinkKernel_left_frame hψ (C (F.pos j))
        (C (F.pos (j + 1))) hlead hsig
      rw [hframe.1]
      exact hCj
  · by_cases hjk1 : j = k + 1
    · subst hjk1
      rw [sinkStep_pos_responder hψ F C k (by have := F.hdn; omega)]
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        exact (sinkKernel_victim_absorb hψ (C (F.pos 0)) (C (F.pos 1))
          hinv.1.1 (hinv.2.1 1 (by omega) (by have := F.hd; omega))
          (by rw [hCj]; exact fin3_zero_ne_two)).1
      · have hidle := sinkKernel_idle hψ (C (F.pos k)) (C (F.pos (k + 1)))
          (hinv.2.1 k hkpos (by omega))
          (interior_no_right_fire hψ F C hinv hdone (k + 1) (by omega) hjd)
          hCj (hinv.2.2.1 k (by omega))
        exact hidle.2.1
    · rw [sinkStep_pos_eq hψ F C k j hkn hj1 hjd hjk hjk1]
      exact hCj

/-- No scheduled edge raises the bullet front. -/
theorem bulletTop_step_le (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (hinv : GapInvariant hψ F C)
    (hdone : ¬ GapDone F C) (e : Fin n) :
    bulletTop F (sinkStep hψ F C e) ≤ bulletTop F C := by
  have hke : e = F.pos (F.off e) := (F.pos_off e).symm
  have hkn : F.off e < n := F.off_lt e
  apply topIdx_le_of
  intro j hj hjd
  simp only [decide_eq_false_iff_not, Nat.not_lt, Nat.le_zero]
  have hstep : (sinkStep hψ F C e (F.pos j)).bullet = ⟨0, by omega⟩ := by
    rw [hke]
    exact sinkStep_keeps_bullet_zero hψ F C hinv hdone (F.off e) j hkn
      (by omega) hjd (bulletTop_zero_at F C hj hjd)
      (fun _ => bulletTop_zero_at F C (by omega) (by omega))
  rw [hstep]

/-- On a bullet-free gap, no scheduled edge lowers the signal front. -/
theorem signalTop_step_ge (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (hinv : GapInvariant hψ F C)
    (hdone : ¬ GapDone F C) (hzero : bulletTop F C = 0) (e : Fin n) :
    signalTop F C ≤ signalTop F (sinkStep hψ F C e) := by
  rcases Nat.eq_zero_or_pos (signalTop F C) with h0 | hpos
  · rw [h0]; exact Nat.zero_le _
  · have hs1 : (C (F.pos (signalTop F C))).signal_B = ⟨1, by omega⟩ :=
      signalTop_one_at F C hpos
    have hsd : signalTop F C ≤ F.d := signalTop_le F C
    have hbz : ∀ i, 1 ≤ i → i ≤ F.d →
        (C (F.pos i)).bullet = ⟨0, by omega⟩ := fun i hi1 hid =>
      bulletTop_zero_at F C (by omega) hid
    apply signalTop_ge_of F _ hsd
    have hke : e = F.pos (F.off e) := (F.pos_off e).symm
    have hkn : F.off e < n := F.off_lt e
    rw [hke]
    by_cases hjk : signalTop F C = F.off e
    · rw [← hjk]
      rw [sinkStep_pos_initiator]
      rcases Nat.lt_or_ge (signalTop F C) F.d with hlt | hge
      · have hidle := sinkKernel_idle hψ (C (F.pos (signalTop F C)))
          (C (F.pos (signalTop F C + 1)))
          (hinv.2.1 (signalTop F C) hpos hlt)
          (interior_no_right_fire hψ F C hinv hdone (signalTop F C + 1)
            (by omega) (by omega))
          (hbz (signalTop F C + 1) (by omega) (by omega))
          (hinv.2.2.1 (signalTop F C) hlt)
        rw [hidle.1]
        exact hs1
      · have hsd' : signalTop F C = F.d := by omega
        rw [hsd'] at hs1
        exact absurd ((signal_shooter_zero hψ F C hinv hdone).symm.trans hs1)
          fin2_zero_ne_one
    · by_cases hjk1 : signalTop F C = F.off e + 1
      · rw [hjk1]
        rw [sinkStep_pos_responder hψ F C (F.off e) (by
          have := F.hdn; omega)]
        rcases Nat.eq_zero_or_pos (F.off e) with hk0 | hkpos
        · rw [hk0]
          have h1d : (1 : Nat) ≤ F.d := by have := F.hd; omega
          exact (sinkKernel_victim_absorb hψ (C (F.pos 0)) (C (F.pos 1))
            hinv.1.1 (hinv.2.1 1 (by omega) (by have := F.hd; omega))
            (by rw [hbz 1 (by omega) h1d]; exact fin3_zero_ne_two)).2.1
        · have hidle := sinkKernel_idle hψ (C (F.pos (F.off e)))
            (C (F.pos (F.off e + 1)))
            (hinv.2.1 (F.off e) hkpos (by omega))
            (interior_no_right_fire hψ F C hinv hdone (F.off e + 1)
              (by omega) (by omega))
            (hbz (F.off e + 1) (by omega) (by omega))
            (hinv.2.2.1 (F.off e) (by omega))
          apply hidle.2.2.2
          rw [← hjk1]
          exact hs1
      · rw [sinkStep_pos_eq hψ F C (F.off e) (signalTop F C) hkn hpos hsd
          hjk hjk1]
        exact hs1

/-- No scheduled edge raises the service rank. -/
theorem gapRank_step_le (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (hinv : GapInvariant hψ F C)
    (hdone : ¬ GapDone F C) (e : Fin n) :
    gapRank F (sinkStep hψ F C e) ≤ gapRank F C := by
  have hb := bulletTop_step_le hψ F C hinv hdone e
  unfold gapRank
  split
  · next hstep0 =>
      split
      · next hC0 =>
          have hs := signalTop_step_ge hψ F C hinv hdone hC0 e
          omega
      · next hCpos =>
          have := signalTop_le F (sinkStep hψ F C e)
          omega
  · next hsteppos =>
      split
      · next hC0 => omega
      · next hCpos => omega

end GapDynamics

/-! ## The service-rank certificate -/

section Certificate

variable {ψ n : Nat}

open Classical

/-- The service rank, cut off at the stopping set. -/
noncomputable def gapW (F : GapFrame n) (C : Fin n → AgentState ψ) : Nat :=
  if GapDone F C then 0 else gapRank F C

theorem gapW_done (F : GapFrame n) (C : Fin n → AgentState ψ)
    (h : GapDone F C) : gapW F C = 0 := by
  unfold gapW; rw [if_pos h]

theorem gapW_not_done (F : GapFrame n) (C : Fin n → AgentState ψ)
    (h : ¬ GapDone F C) : gapW F C = gapRank F C := by
  unfold gapW; rw [if_neg h]

theorem gapW_le_gapRank (F : GapFrame n) (C : Fin n → AgentState ψ) :
    gapW F C ≤ gapRank F C := by
  unfold gapW
  split
  · exact Nat.zero_le _
  · exact Nat.le_refl _

/-- `W ≤ 2 d`. -/
theorem gapW_le (F : GapFrame n) (C : Fin n → AgentState ψ) :
    gapW F C ≤ 2 * F.d :=
  Nat.le_trans (gapW_le_gapRank F C) (gapRank_le F C)

/-- No scheduled edge raises `W`. -/
theorem gapW_step_le (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (hinv : GapInvariant hψ F C)
    (hdone : ¬ GapDone F C) (e : Fin n) :
    gapW F (sinkStep hψ F C e) ≤ gapW F C := by
  rw [gapW_not_done F C hdone]
  exact Nat.le_trans (gapW_le_gapRank F _) (gapRank_step_le hψ F C hinv hdone e)

/-- Some scheduled edge strictly lowers `W`. -/
theorem gapW_drop (hψ : ψ > 0) (F : GapFrame n) (C : Fin n → AgentState ψ)
    (hinv : GapInvariant hψ F C) (hdone : ¬ GapDone F C) :
    ∃ e : Fin n, gapW F (sinkStep hψ F C e) + 1 ≤ gapW F C := by
  have hWC : gapW F C = gapRank F C := gapW_not_done F C hdone
  have hdpos : 2 ≤ F.d := F.hd
  rcases Nat.eq_zero_or_pos (bulletTop F C) with hb0 | hbpos
  · -- Bullet-free sector: the signal front advances one cell.
    have hbz : ∀ i, 1 ≤ i → i ≤ F.d →
        (C (F.pos i)).bullet = ⟨0, by omega⟩ := fun i hi1 hid =>
      bulletTop_zero_at F C (by omega) hid
    have hsltd : signalTop F C < F.d := by
      rcases Nat.lt_or_ge (signalTop F C) F.d with h | h
      · exact h
      · exfalso
        have heq : signalTop F C = F.d := Nat.le_antisymm (signalTop_le F C) h
        have hpos : 0 < signalTop F C := by omega
        have h1 := signalTop_one_at F C hpos
        rw [heq] at h1
        exact hdone (Or.inl ⟨h1, hbz⟩)
    refine ⟨F.pos (signalTop F C), ?_⟩
    have hresp : sinkStep hψ F C (F.pos (signalTop F C))
        (F.pos (signalTop F C + 1)) =
        (sinkKernel hψ (C (F.pos (signalTop F C)))
          (C (F.pos (signalTop F C + 1)))).2 :=
      sinkStep_pos_responder hψ F C (signalTop F C) (by have := F.hdn; omega)
    have hsig1 : (sinkStep hψ F C (F.pos (signalTop F C))
        (F.pos (signalTop F C + 1))).signal_B = ⟨1, by omega⟩ := by
      rw [hresp]
      rcases Nat.eq_zero_or_pos (signalTop F C) with h0 | hpos
      · have habs : (sinkKernel hψ (C (F.pos (signalTop F C)))
            (C (F.pos (signalTop F C + 1)))).2.signal_B = ⟨1, by omega⟩ := by
          rw [h0]
          exact (sinkKernel_victim_absorb hψ (C (F.pos 0)) (C (F.pos 1))
            hinv.1.1 (hinv.2.1 1 (by omega) (by omega))
            (by rw [hbz 1 (by omega) (by omega)];
                exact fin3_zero_ne_two)).2.1
        exact habs
      · have hidle := sinkKernel_idle hψ (C (F.pos (signalTop F C)))
          (C (F.pos (signalTop F C + 1))) (hinv.2.1 _ hpos hsltd)
          (interior_no_right_fire hψ F C hinv hdone (signalTop F C + 1)
            (by omega) (by omega))
          (hbz (signalTop F C + 1) (by omega) (by omega))
          (hinv.2.2.1 _ hsltd)
        exact hidle.2.2.1 (signalTop_one_at F C hpos)
    have hbstep : bulletTop F (sinkStep hψ F C (F.pos (signalTop F C))) = 0 := by
      have := bulletTop_step_le hψ F C hinv hdone (F.pos (signalTop F C))
      omega
    have hsstep : signalTop F C + 1 ≤
        signalTop F (sinkStep hψ F C (F.pos (signalTop F C))) :=
      signalTop_ge_of F _ (by omega) hsig1
    have hrank : gapRank F (sinkStep hψ F C (F.pos (signalTop F C))) ≤
        F.d - signalTop F C - 1 := by
      unfold gapRank
      rw [if_pos hbstep]
      omega
    have hrankC : gapRank F C = F.d - signalTop F C := by
      unfold gapRank; rw [if_pos hb0]
    have hle := gapW_le_gapRank F (sinkStep hψ F C (F.pos (signalTop F C)))
    omega
  · rcases Nat.lt_or_ge (bulletTop F C) 2 with h1 | h2
    · -- A single bullet, adjacent to the victim.
      have ht1 : bulletTop F C = 1 := by omega
      have hb1 : (C (F.pos 1)).bullet ≠ ⟨0, by omega⟩ := by
        have h := bulletTop_ne_zero F C hbpos; rwa [ht1] at h
      have hrest : ∀ k, 2 ≤ k → k ≤ F.d →
          (C (F.pos k)).bullet = ⟨0, by omega⟩ := fun k hk2 hkd =>
        bulletTop_zero_at F C (by omega) hkd
      have hrankC : gapRank F C = F.d + 1 := by
        unfold gapRank; rw [if_neg (by omega), ht1]
      have hfollow1 : (C (F.pos 1)).leader = false :=
        hinv.2.1 1 (by omega) (by omega)
      refine ⟨F.pos 0, ?_⟩
      rcases fin3_cases (C (F.pos 1)).bullet with h | h | h
      · exact absurd h hb1
      · -- A dummy at the victim is absorbed by the sink.
        have hab := sinkKernel_victim_absorb hψ (C (F.pos 0)) (C (F.pos 1))
          hinv.1.1 hfollow1 (by rw [h]; exact fin3_one_ne_two)
        have hbstep : bulletTop F (sinkStep hψ F C (F.pos 0)) = 0 := by
          have hle2 := bulletTop_step_le hψ F C hinv hdone (F.pos 0)
          have hzero : ∀ i, 1 ≤ i → i ≤ F.d →
              (sinkStep hψ F C (F.pos 0) (F.pos i)).bullet =
                ⟨0, by omega⟩ := by
            intro i hi1 hid
            by_cases hi : i = 1
            · have hresp : sinkStep hψ F C (F.pos 0) (F.pos 1) =
                  (sinkKernel hψ (C (F.pos 0)) (C (F.pos 1))).2 :=
                sinkStep_pos_responder hψ F C 0 (by have := F.hdn; omega)
              rw [hi, hresp]
              exact hab.1
            · rw [sinkStep_pos_eq hψ F C 0 i (by have := F.hdn; omega) hi1 hid
                (by omega) (by omega)]
              exact hrest i (by omega) hid
          exact bulletTop_eq_zero_of F _ hzero
        have hsig : (sinkStep hψ F C (F.pos 0) (F.pos 1)).signal_B =
            ⟨1, by omega⟩ := by
          have hresp : sinkStep hψ F C (F.pos 0) (F.pos 1) =
              (sinkKernel hψ (C (F.pos 0)) (C (F.pos 1))).2 :=
            sinkStep_pos_responder hψ F C 0 (by have := F.hdn; omega)
          rw [hresp]
          exact hab.2.1
        have hsstep : 1 ≤ signalTop F (sinkStep hψ F C (F.pos 0)) :=
          signalTop_ge_of F _ (by omega) hsig
        have hrank : gapRank F (sinkStep hψ F C (F.pos 0)) ≤ F.d - 1 := by
          unfold gapRank; rw [if_pos hbstep]; omega
        have hle3 := gapW_le_gapRank F (sinkStep hψ F C (F.pos 0))
        omega
      · -- A live bullet at an unprotected victim deletes it.
        have hnb : ¬ GapBlocked F C := fun hbl => hdone (Or.inr (Or.inr hbl))
        have hprot : ¬ ((C (F.pos 0)).shield = true ∨
            (C (F.pos 0)).signal_B = ⟨1, by omega⟩) := fun hp =>
          hnb ⟨h, hrest, hp⟩
        have hsh : (C (F.pos 0)).shield = false := by
          cases hshv : (C (F.pos 0)).shield
          · rfl
          · exact absurd (Or.inl hshv) hprot
        have hsg : (C (F.pos 0)).signal_B = ⟨0, by omega⟩ := by
          rcases fin2_cases (C (F.pos 0)).signal_B with hx | hx
          · exact hx
          · exact absurd (Or.inr hx) hprot
        have hkill := sinkKernel_kill hψ (C (F.pos 0)) (C (F.pos 1))
          hinv.1.1 hsh hsg hfollow1 h
        have hinit : sinkStep hψ F C (F.pos 0) (F.pos 0) =
            (sinkKernel hψ (C (F.pos 0)) (C (F.pos 1))).1 :=
          sinkStep_pos_initiator hψ F C 0
        have hstep0 : (sinkStep hψ F C (F.pos 0) (F.pos 0)).leader = false := by
          rw [hinit]; exact hkill
        rw [gapW_done F _ (Or.inr (Or.inl (Or.inl hstep0)))]
        omega
    · -- Front bullet still in the interior: it moves one cell down.
      obtain ⟨m, hm⟩ : ∃ m, bulletTop F C = m + 1 :=
        ⟨bulletTop F C - 1, by omega⟩
      have hm1 : 1 ≤ m := by omega
      have hmd : m + 1 ≤ F.d := by have := bulletTop_le F C; omega
      have hbne : (C (F.pos (m + 1))).bullet ≠ ⟨0, by omega⟩ := by
        have h := bulletTop_ne_zero F C hbpos; rwa [hm] at h
      have hbval : 0 < (C (F.pos (m + 1))).bullet.val := by
        rcases Nat.eq_zero_or_pos (C (F.pos (m + 1))).bullet.val with hz | hp
        · exact absurd (Fin.ext hz) hbne
        · exact hp
      have hmove := sinkKernel_move_down hψ (C (F.pos m)) (C (F.pos (m + 1)))
        (hinv.2.1 m hm1 (by omega))
        (interior_no_right_fire hψ F C hinv hdone (m + 1) (by omega) hmd)
        hbval (hinv.2.2.1 m (by omega))
      refine ⟨F.pos m, ?_⟩
      have hinit : sinkStep hψ F C (F.pos m) (F.pos m) =
          (sinkKernel hψ (C (F.pos m)) (C (F.pos (m + 1)))).1 :=
        sinkStep_pos_initiator hψ F C m
      have hresp : sinkStep hψ F C (F.pos m) (F.pos (m + 1)) =
          (sinkKernel hψ (C (F.pos m)) (C (F.pos (m + 1)))).2 :=
        sinkStep_pos_responder hψ F C m (by have := F.hdn; omega)
      have hstepm : (sinkStep hψ F C (F.pos m) (F.pos m)).bullet =
          (C (F.pos (m + 1))).bullet := by rw [hinit]; exact hmove.1
      have hge : m ≤ bulletTop F (sinkStep hψ F C (F.pos m)) := by
        apply bulletTop_ge_of F _ (by omega)
        rw [hstepm]; exact hbne
      have hle : bulletTop F (sinkStep hψ F C (F.pos m)) ≤ m := by
        apply topIdx_le_of
        intro i hi hid
        simp only [decide_eq_false_iff_not, Nat.not_lt, Nat.le_zero]
        have hzero : (sinkStep hψ F C (F.pos m) (F.pos i)).bullet =
            ⟨0, by omega⟩ := by
          by_cases hi1 : i = m + 1
          · rw [hi1, hresp]; exact hmove.2.2.1
          · rw [sinkStep_pos_eq hψ F C m i (by have := F.hdn; omega)
              (by omega) hid (by omega) hi1]
            exact bulletTop_zero_at F C (by omega) hid
        rw [hzero]
      have hrankC : gapRank F C = F.d + (m + 1) := by
        unfold gapRank; rw [if_neg (by omega), hm]
      have hrankstep : gapRank F (sinkStep hψ F C (F.pos m)) = F.d + m := by
        unfold gapRank; rw [if_neg (by omega)]; omega
      have hle3 := gapW_le_gapRank F (sinkStep hψ F C (F.pos m))
      omega

end Certificate

/-! ## Preservation of the gap invariant -/

section Preservation

variable {ψ n : Nat}

theorem sinkStep_cases (hψ : ψ > 0) (F : GapFrame n) (C : Fin n → AgentState ψ)
    (e k : Fin n) :
    sinkStep hψ F C e k = C k ∨
      (k = e ∧ sinkStep hψ F C e k =
        (sinkKernel hψ (C e) (C (F.ring.rightNeighbor e))).1) ∨
      (k = F.ring.rightNeighbor e ∧ sinkStep hψ F C e k =
        (sinkKernel hψ (C e) (C (F.ring.rightNeighbor e))).2) := by
  by_cases h1 : k = e
  · refine Or.inr (Or.inl ⟨h1, ?_⟩)
    rw [h1]
    exact updatePair_initiator C e (F.ring.rightNeighbor e) _
  · by_cases h2 : k = F.ring.rightNeighbor e
    · refine Or.inr (Or.inr ⟨h2, ?_⟩)
      rw [h2]
      exact updatePair_responder C e (F.ring.rightNeighbor e) _
        (fun hh => h1 (h2.trans hh))
    · exact Or.inl (sinkStep_other hψ F C e k h1 h2)

/-- Labels are inert under every scheduled edge. -/
theorem sinkStep_label (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (e k : Fin n) :
    (sinkStep hψ F C e k).label = (C k).label := by
  rcases sinkStep_cases hψ F C e k with h | ⟨hk, h⟩ | ⟨hk, h⟩
  · rw [h]
  · rw [h, hk]; exact (sinkKernel_labels hψ _ _).1
  · rw [h, hk]; exact (sinkKernel_labels hψ _ _).2

/-- No rule creates a leader. -/
theorem sinkStep_follower (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (e k : Fin n) (h : (C k).leader = false) :
    (sinkStep hψ F C e k).leader = false := by
  rcases sinkStep_cases hψ F C e k with hc | ⟨hk, hc⟩ | ⟨hk, hc⟩
  · rw [hc]; exact h
  · rw [hc]
    apply sinkKernel_left_leader_false
    rw [← hk]; exact h
  · rw [hc, sinkKernel_right_leader, ← hk]; exact h

theorem signalBelowBullets_of_agree (F : GapFrame n)
    (C D : Fin n → AgentState ψ) (hC : GapSignalBelowBullets F C)
    (hb : ∀ t, 1 ≤ t → t ≤ F.d →
      (D (F.pos t)).bullet = (C (F.pos t)).bullet)
    (hs : ∀ t, 1 ≤ t → t ≤ F.d →
      (D (F.pos t)).signal_B = (C (F.pos t)).signal_B) :
    GapSignalBelowBullets F D := by
  intro i j hi1 hid hbi hij hjd
  rw [hs j (by omega) hjd]
  exact hC i j hi1 hid (by rw [← hb i hi1 hid]; exact hbi) hij hjd

/-- One-way geometry is preserved by every scheduled edge. -/
theorem sinkStep_signalBelowBullets_at (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (hinv : GapInvariant hψ F C)
    (hdone : ¬ GapDone F C) (k : Nat) (hkn : k < n) :
    GapSignalBelowBullets F (sinkStep hψ F C (F.pos k)) := by
  have hC := hinv.2.2.2
  rcases Nat.lt_or_ge k F.d with hklt | hkge
  · -- The scheduled edge is one of the `d` gap edges.
    have halign := hinv.2.2.1 k hklt
    have hrfire := interior_no_right_fire hψ F C hinv hdone (k + 1)
      (by omega) (by omega)
    have hout : ∀ t, 1 ≤ t → t ≤ F.d → t ≠ k → t ≠ k + 1 →
        sinkStep hψ F C (F.pos k) (F.pos t) = C (F.pos t) :=
      fun t h1 h2 h3 h4 => sinkStep_pos_eq hψ F C k t hkn h1 h2 h3 h4
    have hinit : sinkStep hψ F C (F.pos k) (F.pos k) =
        (sinkKernel hψ (C (F.pos k)) (C (F.pos (k + 1)))).1 :=
      sinkStep_pos_initiator hψ F C k
    have hresp : sinkStep hψ F C (F.pos k) (F.pos (k + 1)) =
        (sinkKernel hψ (C (F.pos k)) (C (F.pos (k + 1)))).2 :=
      sinkStep_pos_responder hψ F C k (by have := F.hdn; omega)
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · -- The victim edge `(pos 0, pos 1)`.
      subst hk0
      have hd2 : 2 ≤ F.d := F.hd
      have hfollow1 : (C (F.pos 1)).leader = false :=
        hinv.2.1 1 (by omega) (by omega)
      have hresp1 : sinkStep hψ F C (F.pos 0) (F.pos 1) =
          (sinkKernel hψ (C (F.pos 0)) (C (F.pos 1))).2 := hresp
      have hout2 : ∀ t, 2 ≤ t → t ≤ F.d →
          sinkStep hψ F C (F.pos 0) (F.pos t) = C (F.pos t) :=
        fun t h2 h3 => hout t (by omega) h3 (by omega) (by omega)
      by_cases hlive : (C (F.pos 1)).bullet = ⟨2, by omega⟩
      · -- A live bullet at the victim: SIGNAL clamps the responder.
        have hCb1 : (C (F.pos 1)).bullet ≠ ⟨0, by omega⟩ := by
          rw [hlive]; exact fin3_two_ne_zero
        have hCs1 : (C (F.pos 1)).signal_B = ⟨0, by omega⟩ :=
          hC 1 1 (by omega) (by omega) hCb1 (by omega) (by omega)
        have hD1s : (sinkStep hψ F C (F.pos 0) (F.pos 1)).signal_B =
            ⟨0, by omega⟩ := by
          rw [hresp1]
          exact sinkKernel_live_signal_zero hψ (C (F.pos 0)) (C (F.pos 1))
            hinv.1.1 hfollow1 hlive hCs1
        intro i j hi1 hid hbi hij hjd
        by_cases hj1 : j = 1
        · rw [hj1]; exact hD1s
        · rw [hout2 j (by omega) hjd]
          exact hC 1 j (by omega) (by omega) hCb1 (by omega) hjd
      · -- Otherwise the dummy sink clears the victim's neighbour.
        have hab := sinkKernel_victim_absorb hψ (C (F.pos 0)) (C (F.pos 1))
          hinv.1.1 hfollow1 hlive
        have hD1 : (sinkStep hψ F C (F.pos 0) (F.pos 1)).bullet =
            ⟨0, by omega⟩ := by rw [hresp1]; exact hab.1
        intro i j hi1 hid hbi hij hjd
        have hi2 : 2 ≤ i := by
          rcases Nat.lt_or_ge i 2 with h | h
          · exfalso
            have hi : i = 1 := by omega
            rw [hi] at hbi
            exact hbi hD1
          · exact h
        rw [hout2 j (by omega) hjd]
        exact hC i j hi1 hid
          (by rw [← hout2 i hi2 hid]; exact hbi) hij hjd
    · -- An interior gap edge.
      have hfollowk : (C (F.pos k)).leader = false := hinv.2.1 k hkpos hklt
      by_cases hbz : (C (F.pos (k + 1))).bullet = ⟨0, by omega⟩
      · -- Nothing to transport: only the signal moves.
        have hidle := sinkKernel_idle hψ (C (F.pos k)) (C (F.pos (k + 1)))
          hfollowk hrfire hbz halign
        have hDk : sinkStep hψ F C (F.pos k) (F.pos k) = C (F.pos k) := by
          rw [hinit]; exact hidle.1
        have hDk1b : (sinkStep hψ F C (F.pos k) (F.pos (k + 1))).bullet =
            ⟨0, by omega⟩ := by rw [hresp]; exact hidle.2.1
        intro i j hi1 hid hbi hij hjd
        have hine : i ≠ k + 1 := by
          intro h; rw [h] at hbi; exact hbi hDk1b
        have hDi : sinkStep hψ F C (F.pos k) (F.pos i) = C (F.pos i) := by
          by_cases hik : i = k
          · rw [hik]; exact hDk
          · exact hout i hi1 hid hik hine
        have hCi : (C (F.pos i)).bullet ≠ ⟨0, by omega⟩ := by
          rw [← hDi]; exact hbi
        by_cases hjk1 : j = k + 1
        · have hik : i ≤ k := by omega
          have hsk : (C (F.pos k)).signal_B = ⟨0, by omega⟩ :=
            hC i k hi1 hid hCi hik (by omega)
          have hsk1 : (C (F.pos (k + 1))).signal_B = ⟨0, by omega⟩ :=
            hC i (k + 1) hi1 hid hCi (by omega) (by omega)
          rw [hjk1, hresp]
          exact sinkKernel_idle_signal_zero hψ (C (F.pos k))
            (C (F.pos (k + 1))) hfollowk hrfire hbz hsk hsk1
        · have hDj : sinkStep hψ F C (F.pos k) (F.pos j) = C (F.pos j) := by
            by_cases hjk : j = k
            · rw [hjk]; exact hDk
            · exact hout j (by omega) hjd hjk hjk1
          rw [hDj]
          exact hC i j hi1 hid hCi hij hjd
      · -- A bullet steps one cell towards the victim.
        have hbval : 0 < (C (F.pos (k + 1))).bullet.val := by
          rcases Nat.eq_zero_or_pos (C (F.pos (k + 1))).bullet.val with hz | hp
          · exact absurd (Fin.ext hz) hbz
          · exact hp
        have hmove := sinkKernel_move_down hψ (C (F.pos k))
          (C (F.pos (k + 1))) hfollowk hrfire hbval halign
        have hDk1b : (sinkStep hψ F C (F.pos k) (F.pos (k + 1))).bullet =
            ⟨0, by omega⟩ := by rw [hresp]; exact hmove.2.2.1
        have hCk1s : (C (F.pos (k + 1))).signal_B = ⟨0, by omega⟩ :=
          hC (k + 1) (k + 1) (by omega) (by omega) hbz (by omega) (by omega)
        intro i j hi1 hid hbi hij hjd
        have hine : i ≠ k + 1 := by
          intro h; rw [h] at hbi; exact hbi hDk1b
        by_cases hjk : j = k
        · rw [hjk, hinit]; exact hmove.2.1
        · by_cases hjk1 : j = k + 1
          · rw [hjk1, hresp, hmove.2.2.2]
            exact hCk1s
          · rw [hout j (by omega) hjd hjk hjk1]
            by_cases hik : i = k
            · exact hC (k + 1) j (by omega) (by omega) hbz (by omega) hjd
            · exact hC i j hi1 hid
                (by rw [← hout i hi1 hid hik hine]; exact hbi) hij hjd
  · -- The scheduled edge is outside the gap, or the shooter's outgoing edge.
    apply signalBelowBullets_of_agree F C _ hC
    · intro t ht1 htd
      by_cases htk : t = k
      · have hkd : k = F.d := by omega
        rw [htk, sinkStep_pos_initiator]
        have hframe := sinkKernel_left_frame hψ (C (F.pos k))
          (C (F.pos (k + 1))) (by rw [hkd]; exact hinv.1.2)
          (by rw [hkd]; exact signal_shooter_zero hψ F C hinv hdone)
        exact hframe.1
      · rw [sinkStep_pos_eq hψ F C k t hkn ht1 htd htk (by omega)]
    · intro t ht1 htd
      by_cases htk : t = k
      · have hkd : k = F.d := by omega
        rw [htk, sinkStep_pos_initiator]
        have hframe := sinkKernel_left_frame hψ (C (F.pos k))
          (C (F.pos (k + 1))) (by rw [hkd]; exact hinv.1.2)
          (by rw [hkd]; exact signal_shooter_zero hψ F C hinv hdone)
        exact hframe.2
      · rw [sinkStep_pos_eq hψ F C k t hkn ht1 htd htk (by omega)]

/-- **Invariant preservation.**  Every scheduled edge either lands in the
stopping set or preserves the gap invariant. -/
theorem sinkStep_invariant_or_done (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (hinv : GapInvariant hψ F C)
    (hdone : ¬ GapDone F C) (e : Fin n) :
    GapDone F (sinkStep hψ F C e) ∨ GapInvariant hψ F (sinkStep hψ F C e) := by
  by_cases hd : GapDone F (sinkStep hψ F C e)
  · exact Or.inl hd
  · refine Or.inr ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · have hnd : ¬ EndpointDeleted F (sinkStep hψ F C e) := fun h =>
        hd (Or.inr (Or.inl h))
      cases hx : (sinkStep hψ F C e (F.pos 0)).leader
      · exact absurd (Or.inl hx) hnd
      · rfl
    · have hnd : ¬ EndpointDeleted F (sinkStep hψ F C e) := fun h =>
        hd (Or.inr (Or.inl h))
      cases hx : (sinkStep hψ F C e (F.pos F.d)).leader
      · exact absurd (Or.inr hx) hnd
      · rfl
    · intro t ht1 htd
      exact sinkStep_follower hψ F C e _ (hinv.2.1 t ht1 htd)
    · intro t htd
      apply Fin.ext
      show (sinkStep hψ F C e (F.pos (t + 1))).label.val =
        ((sinkStep hψ F C e (F.pos t)).label.val + 1) % ψ
      rw [sinkStep_label hψ F C e (F.pos (t + 1)),
        sinkStep_label hψ F C e (F.pos t)]
      exact congrArg Fin.val (hinv.2.2.1 t htd)
    · have hke : e = F.pos (F.off e) := (F.pos_off e).symm
      rw [hke]
      exact sinkStep_signalBelowBullets_at hψ F C hinv hdone (F.off e)
        (F.off_lt e)

end Preservation

/-! ## Iterated form: `2 d` designated services -/

section Iterated

variable {ψ n : Nat}

open Classical

theorem gapW_zero_done (F : GapFrame n) (C : Fin n → AgentState ψ)
    (h : gapW F C = 0) : GapDone F C := by
  by_cases hd : GapDone F C
  · exact hd
  · exfalso
    rw [gapW_not_done F C hd] at h
    unfold gapRank at h
    split at h
    · next hb0 =>
        have hs : F.d ≤ signalTop F C := by omega
        have hsd : signalTop F C = F.d :=
          Nat.le_antisymm (signalTop_le F C) hs
        have hpos : 0 < signalTop F C := by have := F.hd; omega
        have h1 := signalTop_one_at F C hpos
        rw [hsd] at h1
        exact hd (Or.inl ⟨h1, fun k hk1 hkd =>
          bulletTop_zero_at F C (by omega) hkd⟩)
    · next hbne => have := F.hd; omega

/-- The configuration after running the scheduler word `w`. -/
def gapRun (hψ : ψ > 0) (F : GapFrame n) (C : Fin n → AgentState ψ)
    (w : List (Fin n)) : Fin n → AgentState ψ :=
  w.foldl (fun D e => sinkStep hψ F D e) C

theorem gapRun_cons (hψ : ψ > 0) (F : GapFrame n) (C : Fin n → AgentState ψ)
    (e : Fin n) (w : List (Fin n)) :
    gapRun hψ F C (e :: w) = gapRun hψ F (sinkStep hψ F C e) w := rfl

theorem gap_reaches_done (hψ : ψ > 0) (F : GapFrame n) :
    ∀ (m : Nat) (C : Fin n → AgentState ψ), GapInvariant hψ F C →
      gapW F C ≤ m →
      ∃ w : List (Fin n), w.length ≤ m ∧ GapDone F (gapRun hψ F C w) := by
  intro m
  induction m with
  | zero =>
      intro C _ h0
      exact ⟨[], Nat.le_refl 0, gapW_zero_done F C (by omega)⟩
  | succ m ih =>
      intro C hinv hle
      by_cases hd : GapDone F C
      · exact ⟨[], Nat.zero_le _, hd⟩
      · obtain ⟨e, he⟩ := gapW_drop hψ F C hinv hd
        rcases sinkStep_invariant_or_done hψ F C hinv hd e with hdone2 | hinv2
        · exact ⟨[e], by simp, hdone2⟩
        · obtain ⟨w, hw1, hw2⟩ := ih (sinkStep hψ F C e) hinv2 (by omega)
          exact ⟨e :: w, by simp only [List.length_cons]; omega, hw2⟩

/-- **`2 d` designated services.**  From every gap configuration satisfying the
invariant there is a scheduler word of length at most `2 d` after which the gap
is `CleanReady`, has lost an endpoint, or is blocked at the victim.  This is the
combinatorial core behind the `2 n d` interaction bound: each designated service
is one specific edge out of `n`. -/
theorem gap_cleanup_within_two_d (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (hinv : GapInvariant hψ F C) :
    ∃ w : List (Fin n), w.length ≤ 2 * F.d ∧ GapDone F (gapRun hψ F C w) :=
  gap_reaches_done hψ F (2 * F.d) C hinv (gapW_le F C)

end Iterated

/-! ## From a service rank to the `n`-weighted Bellman inequality

Generic, division-free: a rank bounded by `D`, nonincreasing on all `n`
scheduler edges and strictly decreasing on at least one, yields the supersolution
`V = n * W` of the uniform-scheduler Bellman inequality
`n + Σ_e V (step e) ≤ n * V`. -/

section Bellman

theorem ofFn_sum_const (c : Nat) : ∀ m : Nat,
    (List.ofFn (fun _ : Fin m => c)).sum = m * c := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons, ih, Nat.succ_mul]
      omega

theorem ofFn_sum_mul (c : Nat) : ∀ (m : Nat) (f : Fin m → Nat),
    (List.ofFn (fun i => c * f i)).sum = c * (List.ofFn f).sum := by
  intro m
  induction m with
  | zero => intro f; simp
  | succ m ih =>
      intro f
      rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons,
        ih (fun i => f i.succ), Nat.mul_add]

theorem ofFn_sum_lt : ∀ (m : Nat) (f : Fin m → Nat) (c : Nat) (e₀ : Fin m),
    (∀ e, f e ≤ c) → f e₀ + 1 ≤ c → (List.ofFn f).sum + 1 ≤ m * c := by
  intro m
  induction m with
  | zero => intro _ _ e₀ _ _; exact e₀.elim0
  | succ m ih =>
      intro f c e₀ hle hdrop
      rw [List.ofFn_succ, List.sum_cons]
      have hsum : (List.ofFn (fun i : Fin m => f i.succ)).sum ≤ m * c := by
        have h := ofFn_sum_le (fun i : Fin m => f i.succ) (fun _ => c)
          (fun i => hle i.succ)
        rw [ofFn_sum_const c m] at h
        exact h
      have h0 : f 0 ≤ c := hle 0
      cases e₀ using Fin.cases with
      | zero =>
          rw [Nat.succ_mul]
          omega
      | succ i =>
          have hd : (List.ofFn (fun j : Fin m => f j.succ)).sum + 1 ≤ m * c :=
            ih (fun j => f j.succ) c i (fun j => hle j.succ) hdrop
          rw [Nat.succ_mul]
          omega

/-- Generic conversion, stated for an arbitrary state type. -/
theorem rank_to_bellman {S : Type} {m : Nat} (step : S → Fin m → S)
    (Inv Done : S → Prop) (W : S → Nat) (D : Nat)
    (hle : ∀ x, Inv x → W x ≤ D)
    (hzero : ∀ x, Done x → W x = 0)
    (hmono : ∀ x e, Inv x → ¬ Done x → W (step x e) ≤ W x)
    (hdrop : ∀ x, Inv x → ¬ Done x → ∃ e, W (step x e) + 1 ≤ W x) :
    ∀ x, Inv x →
      (m * W x ≤ m * D) ∧ (∀ y, Done y → m * W y = 0) ∧
      ∀ y, Inv y → ¬ Done y →
        m + (List.ofFn (fun e : Fin m => m * W (step y e))).sum ≤
          m * (m * W y) := by
  intro x hx
  refine ⟨Nat.mul_le_mul_left m (hle x hx), ?_, ?_⟩
  · intro y hy
    rw [hzero y hy, Nat.mul_zero]
  · intro y hy hny
    obtain ⟨e₀, he₀⟩ := hdrop y hy hny
    have hstep : (List.ofFn (fun e : Fin m => W (step y e))).sum + 1 ≤
        m * W y :=
      ofFn_sum_lt m (fun e => W (step y e)) (W y) e₀
        (fun e => hmono y e hy hny) he₀
    rw [ofFn_sum_mul m m (fun e => W (step y e))]
    calc m + m * (List.ofFn (fun e : Fin m => W (step y e))).sum
        = m * ((List.ofFn (fun e : Fin m => W (step y e))).sum + 1) := by
          rw [Nat.mul_add, Nat.mul_one]; omega
      _ ≤ m * (m * W y) := Nat.mul_le_mul_left m hstep

end Bellman

/-! ## Packaged statements -/

section Packaged

variable {ψ n : Nat}

/-- **Service-rank certificate** for the sink-extended cleanup kernel on one
interleader gap: a `Nat`-valued rank bounded by `2 d`, zero on the stopping
set, never raised by any of the `n` scheduler edges, and strictly lowered by at
least one edge from every non-terminal gap configuration. -/
theorem cleanup_service_rank (hψ : ψ > 0) (F : GapFrame n) :
    ∃ W : (Fin n → AgentState ψ) → Nat,
      (∀ C, GapInvariant hψ F C → W C ≤ 2 * F.d) ∧
      (∀ C, GapDone F C → W C = 0) ∧
      (∀ C e, GapInvariant hψ F C → ¬ GapDone F C →
        W (sinkStep hψ F C e) ≤ W C) ∧
      (∀ C, GapInvariant hψ F C → ¬ GapDone F C →
        ∃ e, W (sinkStep hψ F C e) + 1 ≤ W C) :=
  ⟨gapW F, fun C _ => gapW_le F C, fun C h => gapW_done F C h,
    fun C e hinv hdone => gapW_step_le hψ F C hinv hdone e,
    fun C hinv hdone => gapW_drop hψ F C hinv hdone⟩

/-- Conversion of any such certificate into the division-free `n`-weighted
Bellman inequality with initial potential `2 n d`. -/
theorem cleanup_service_rank_to_2nd (hψ : ψ > 0) (F : GapFrame n) :
    (∃ W : (Fin n → AgentState ψ) → Nat,
      (∀ C, GapInvariant hψ F C → W C ≤ 2 * F.d) ∧
      (∀ C, GapDone F C → W C = 0) ∧
      (∀ C e, GapInvariant hψ F C → ¬ GapDone F C →
        W (sinkStep hψ F C e) ≤ W C) ∧
      (∀ C, GapInvariant hψ F C → ¬ GapDone F C →
        ∃ e, W (sinkStep hψ F C e) + 1 ≤ W C)) →
    ∀ C, GapInvariant hψ F C →
      ∃ V : (Fin n → AgentState ψ) → Nat,
        V C ≤ 2 * n * F.d ∧ (∀ D, GapDone F D → V D = 0) ∧
        ∀ D, GapInvariant hψ F D → ¬ GapDone F D →
          n + (List.ofFn (fun e : Fin n => V (sinkStep hψ F D e))).sum ≤
            n * V D := by
  rintro ⟨W, hle, hzero, hmono, hdrop⟩ C hC
  have h := rank_to_bellman (fun C e => sinkStep hψ F C e)
    (GapInvariant hψ F) (GapDone F) W (2 * F.d) hle hzero hmono hdrop C hC
  refine ⟨fun D => n * W D, ?_, h.2.1, h.2.2⟩
  show n * W C ≤ 2 * n * F.d
  have h1 : n * W C ≤ n * (2 * F.d) := h.1
  have h2 : n * (2 * F.d) = 2 * n * F.d := by
    rw [← Nat.mul_assoc, Nat.mul_comm n 2]
  omega

/-- **`2 n d` cleanup bound** for one interleader gap of the sink-extended
kernel: an explicit `Nat`-valued supersolution of the uniform-scheduler Bellman
inequality with initial value at most `2 n d`.  Every non-terminal gap
configuration pays `n` per interaction, so the sector reaches `CleanReady`,
endpoint deletion, or the blocked-at-victim state within `2 n d` interactions
in the killed-walk sense. -/
theorem sink_gap_cleanup_2nd (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (hInv : GapInvariant hψ F C) :
    ∃ V : (Fin n → AgentState ψ) → Nat,
      V C ≤ 2 * n * F.d ∧ (∀ D, GapDone F D → V D = 0) ∧
      ∀ D, GapInvariant hψ F D → ¬ GapDone F D →
        n + (List.ofFn (fun e : Fin n => V (sinkStep hψ F D e))).sum ≤
          n * V D :=
  cleanup_service_rank_to_2nd hψ F (cleanup_service_rank hψ F) C hInv

end Packaged

/-! ## Alignment with the proposed plan

Aliases under the plan's names, with the corrections the kernel forces. -/

section PlanAlignment

variable {ψ : Nat}

/-- Plan lemma `egressSink_labels`. -/
theorem egressSink_labels (hψ : ψ > 0) (l r : AgentState ψ) :
    (sinkKernel hψ l r).1.label = l.label ∧
      (sinkKernel hψ l r).2.label = r.label := sinkKernel_labels hψ l r

/-- Plan lemma `egressSink_dummy_consumed`, **corrected**.  The plan states it
with only `l.leader = true` and `r.bullet = 1`; that form is false, because
`dummyBulletSink` refuses to fire when the responder is itself a leader.  See
`adjacent_gap_dummy_stuck` for the counterexample.  The extra hypothesis
`r.leader = false` is exactly what the sink's guard requires. -/
theorem egressSink_dummy_consumed (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = true) (hr : r.leader = false)
    (hb : r.bullet = ⟨1, by omega⟩) :
    (sinkKernel hψ l r).2.bullet = ⟨0, by omega⟩ :=
  (sinkKernel_victim_absorb hψ l r hl hr (by rw [hb]; exact fin3_one_ne_two)).1

end PlanAlignment


/-! ## Axiom audit -/

#print axioms fin2_cases
#print axioms fin3_cases
#print axioms fin2_zero_ne_one
#print axioms fin3_zero_ne_two
#print axioms fin3_one_ne_two
#print axioms fin3_one_ne_zero
#print axioms fin3_two_ne_zero
#print axioms GapFrame.off_lt
#print axioms GapFrame.off_pos
#print axioms GapFrame.pos_off
#print axioms GapFrame.pos_inj
#print axioms GapFrame.pos_ne
#print axioms GapFrame.pos_mod
#print axioms GapFrame.pos_ne_mod
#print axioms GapFrame.rightNeighbor_pos
#print axioms GapFrame.gap_pos_injective
#print axioms sinkKernel_staged
#print axioms topIdx_le
#print axioms topIdx_succ_pos
#print axioms topIdx_succ_neg
#print axioms topIdx_holds
#print axioms topIdx_ge
#print axioms topIdx_above
#print axioms topIdx_le_of
#print axioms topIdx_congr
#print axioms fire_eq_self
#print axioms fire_left_eq
#print axioms fire_right_eq
#print axioms fire_labels
#print axioms fire_leaders
#print axioms move_eq_self_of_bullet_zero
#print axioms move_aligned_follower
#print axioms move_leader_cases
#print axioms move_right_leader
#print axioms move_labels
#print axioms move_left_leader_of_follower
#print axioms signal_left
#print axioms signal_right_bullet
#print axioms signal_right_leader
#print axioms signal_right_label
#print axioms signal_right_one
#print axioms signal_right_eq_of_no_source
#print axioms sink_right_signal
#print axioms sink_right_label
#print axioms sink_right_bullet_cases
#print axioms move_leader_not_live
#print axioms sinkKernel_labels
#print axioms sinkKernel_right_leader
#print axioms sinkKernel_left_leader_false
#print axioms sinkKernel_move_down
#print axioms sinkKernel_idle
#print axioms sinkKernel_victim_absorb
#print axioms sinkKernel_live_at_leader
#print axioms sinkKernel_left_frame
#print axioms signal_right_zero_of_live
#print axioms move_no_kill_of_shield
#print axioms fire_left_fires
#print axioms sinkKernel_live_signal_zero
#print axioms sinkKernel_idle_signal_zero
#print axioms adjacent_gap_dummy_stuck
#print axioms sinkStep_other
#print axioms sinkStep_pos_initiator
#print axioms sinkStep_pos_responder
#print axioms sinkStep_pos_eq
#print axioms bulletTop_le
#print axioms signalTop_le
#print axioms bulletTop_zero_at
#print axioms bulletTop_ge_of
#print axioms bulletTop_ne_zero
#print axioms bulletTop_eq_zero_of
#print axioms signalTop_one_at
#print axioms signalTop_ge_of
#print axioms signalTop_zero_at
#print axioms gapRank_le
#print axioms move_kill
#print axioms sinkKernel_kill
#print axioms signal_shooter_zero
#print axioms interior_no_right_fire
#print axioms sinkStep_keeps_bullet_zero
#print axioms bulletTop_step_le
#print axioms signalTop_step_ge
#print axioms gapRank_step_le
#print axioms gapW_done
#print axioms gapW_not_done
#print axioms gapW_le_gapRank
#print axioms gapW_le
#print axioms gapW_step_le
#print axioms gapW_drop
#print axioms sinkStep_cases
#print axioms sinkStep_label
#print axioms sinkStep_follower
#print axioms signalBelowBullets_of_agree
#print axioms sinkStep_signalBelowBullets_at
#print axioms sinkStep_invariant_or_done
#print axioms gapW_zero_done
#print axioms gapRun_cons
#print axioms gap_reaches_done
#print axioms gap_cleanup_within_two_d
#print axioms ofFn_sum_const
#print axioms ofFn_sum_mul
#print axioms ofFn_sum_lt
#print axioms rank_to_bellman
#print axioms cleanup_service_rank
#print axioms cleanup_service_rank_to_2nd
#print axioms sink_gap_cleanup_2nd
#print axioms egressSink_labels
#print axioms egressSink_dummy_consumed

end LDSinkGapCleanup
