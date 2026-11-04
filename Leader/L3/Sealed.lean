import Leader.L3.Native
import Leader.L3.NativeSector
import Leader.L3.Purification
import Leader.L3.ProbStages
import Leader.L3.ProbRenewal

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-!
The real birth-free nativeE owner only.
The sector phases, frame case, leader non-creation and conditional
cost interface are given. General closure and unconditional 3nd
preparation are not claimed without their row/frontier inductions.
-/

/-- Physical site clockwise from a, not a replacement protocol. -/
def sealedSite {n : Nat} (ring : DirectedRing n)
    (a : Fin n) (k : Nat) : Fin n :=
  PPL.shiftRight ring a k

def sealedAt {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (a : Fin n)
    (k : Fin n) : CertNative :=
  N (sealedSite ring a k.val)

def sealedZero {n : Nat} (ring : DirectedRing n) : Fin n :=
  ⟨0, ring.hn⟩

theorem sealedSite_zero {n : Nat}
    (ring : DirectedRing n) (a : Fin n) :
    sealedSite ring a 0 = a := by
  apply Fin.ext
  simp [sealedSite, PPL.shiftRight, Nat.mod_eq_of_lt a.isLt]

theorem sealedAt_zero {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a : Fin n) :
    sealedAt ring N a (sealedZero ring) = N a := by
  simp [sealedAt, sealedZero, sealedSite_zero]

/-- Distinct consecutive native leaders, sector [a,b), d<n. -/
def ConsecutiveNative {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (a b : Fin n)
    (d : Nat) : Prop :=
  1 ≤ d ∧ d < n ∧ b = sealedSite ring a d ∧
  (N a).l = true ∧ (N b).l = true ∧
  ∀ k : Fin n, 0 < k.val → k.val < d →
    (sealedAt ring N a k).l = false

/-! The four exact sealed types, with unrestricted ahead-of-front bits. -/

inductive SealedPhase (n : Nat) where
  | ready
  | dummy (p : Fin n)
  | live (p : Fin n)
  | returning (q : Fin n)
  deriving DecidableEq, Repr

def SealedNoBullet {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (a : Fin n) (d : Nat) : Prop :=
  ∀ k : Fin n, k.val < d →
    (sealedAt ring N a k).b = (0 : Fin 3)

def SealedUniqueBullet {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (a : Fin n) (d : Nat)
    (p : Fin n) (kind : Fin 3) : Prop :=
  p.val < d ∧ (sealedAt ring N a p).b = kind ∧
  ∀ k : Fin n, k.val < d → k ≠ p →
    (sealedAt ring N a k).b = (0 : Fin 3)

def SealedZeroTrail {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (a : Fin n)
    (p : Fin n) : Prop :=
  ∀ k : Fin n, k.val ≤ p.val →
    (sealedAt ring N a k).sg = false

def SealedFirstSignal {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (a : Fin n) (d : Nat)
    (q : Fin n) : Prop :=
  1 ≤ q.val ∧ q.val < d ∧
  (sealedAt ring N a q).sg = true ∧
  ∀ k : Fin n, 0 < k.val → k.val < q.val →
    (sealedAt ring N a k).sg = false

/-- H_a in the paper is the native sh field of leader a. -/
def SealedPhaseHolds {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (a : Fin n) (d : Nat) :
    SealedPhase n → Prop
  | .ready =>
      (sealedAt ring N a (sealedZero ring)).sg = true ∧
      SealedNoBullet ring N a d
  | .dummy p =>
      SealedUniqueBullet ring N a d p (1 : Fin 3) ∧
      (sealedAt ring N a (sealedZero ring)).sh = false ∧
      SealedZeroTrail ring N a p
  | .live p =>
      SealedUniqueBullet ring N a d p (2 : Fin 3) ∧
      (sealedAt ring N a (sealedZero ring)).sh = true ∧
      SealedZeroTrail ring N a p
  | .returning q =>
      SealedNoBullet ring N a d ∧
      (sealedAt ring N a (sealedZero ring)).sg = false ∧
      SealedFirstSignal ring N a d q

def SealedCleanReady {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (a : Fin n) (d : Nat) : Prop :=
  SealedPhaseHolds ring N a d .ready

def Sealed {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (a : Fin n) (d : Nat) : Prop :=
  ∃ phase : SealedPhase n, SealedPhaseHolds ring N a d phase

theorem sealed_of_clean_ready {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a : Fin n) (d : Nat)
    (h : SealedCleanReady ring N a d) :
    Sealed ring N a d :=
  ⟨.ready, h⟩

theorem sealedCleanReady_iff {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a : Fin n) (d : Nat) :
    SealedCleanReady ring N a d ↔
      (N a).sg = true ∧ SealedNoBullet ring N a d := by
  simp [SealedCleanReady, SealedPhaseHolds, sealedAt_zero]

/-! Exact quotas and their nominated physical scheduler edges. -/

def SealedPhaseProgress {n : Nat} (d : Nat) : SealedPhase n → Nat
  | .ready => 0
  | .dummy p => 2 * d - p.val - 1
  | .live p => 2 * d - p.val - 1
  | .returning q => q.val

def SealedPhaseEdge {n : Nat} (ring : DirectedRing n)
    (a : Fin n) : SealedPhase n → Fin n
  | .ready => a
  | .dummy p => sealedSite ring a p.val
  | .live p => sealedSite ring a p.val
  | .returning q => sealedSite ring a (q.val - 1)

theorem sealed_bullet_budget_arithmetic
    (d p : Nat) (hp : p < d) :
    (d - p) + (d - 1) = 2 * d - p - 1 := by
  omega

theorem sealed_phase_progress_bound {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a : Fin n) (d : Nat) (phase : SealedPhase n)
    (h : SealedPhaseHolds ring N a d phase) :
    SealedPhaseProgress d phase ≤ 2 * d - 1 := by
  cases phase with
  | ready => simp [SealedPhaseProgress]
  | dummy p =>
      have hp : p.val < d := h.1.1
      simp only [SealedPhaseProgress]
      omega
  | live p =>
      have hp : p.val < d := h.1.1
      simp only [SealedPhaseProgress]
      omega
  | returning q =>
      have hq : q.val < d := h.2.2.2.1
      simp only [SealedPhaseProgress]
      omega

/-! Exact phase framing when both sites of the selected edge are
outside the half-open sector. -/

def SameSealedSector {n : Nat}
    (ring : DirectedRing n) (a : Fin n) (d : Nat)
    (N M : Fin n → CertNative) : Prop :=
  ∀ k : Fin n, k.val < d →
    sealedAt ring M a k = sealedAt ring N a k

private theorem sealed_same_no_bullet {n : Nat}
    (ring : DirectedRing n) (N M : Fin n → CertNative)
    (a : Fin n) (d : Nat)
    (heq : SameSealedSector ring a d N M)
    (h : SealedNoBullet ring N a d) :
    SealedNoBullet ring M a d := by
  intro k hk
  rw [heq k hk]
  exact h k hk

private theorem sealed_same_unique {n : Nat}
    (ring : DirectedRing n) (N M : Fin n → CertNative)
    (a : Fin n) (d : Nat) (p : Fin n) (kind : Fin 3)
    (heq : SameSealedSector ring a d N M)
    (h : SealedUniqueBullet ring N a d p kind) :
    SealedUniqueBullet ring M a d p kind := by
  rcases h with ⟨hp, hb, hother⟩
  refine ⟨hp, ?_, ?_⟩
  · rw [heq p hp]
    exact hb
  · intro k hk hkp
    rw [heq k hk]
    exact hother k hk hkp

private theorem sealed_same_trail {n : Nat}
    (ring : DirectedRing n) (N M : Fin n → CertNative)
    (a : Fin n) (d : Nat) (p : Fin n)
    (hp : p.val < d)
    (heq : SameSealedSector ring a d N M)
    (h : SealedZeroTrail ring N a p) :
    SealedZeroTrail ring M a p := by
  intro k hk
  rw [heq k (by omega)]
  exact h k hk

private theorem sealed_same_front {n : Nat}
    (ring : DirectedRing n) (N M : Fin n → CertNative)
    (a : Fin n) (d : Nat) (q : Fin n)
    (heq : SameSealedSector ring a d N M)
    (h : SealedFirstSignal ring N a d q) :
    SealedFirstSignal ring M a d q := by
  rcases h with ⟨hqpos, hqlt, hsig, hzero⟩
  refine ⟨hqpos, hqlt, ?_, ?_⟩
  · rw [heq q hqlt]
    exact hsig
  · intro k hk hlt
    rw [heq k (by omega)]
    exact hzero k hk hlt

theorem sealed_phase_congr {n : Nat}
    (ring : DirectedRing n) (N M : Fin n → CertNative)
    (a : Fin n) (d : Nat) (hd : 0 < d)
    (phase : SealedPhase n)
    (heq : SameSealedSector ring a d N M)
    (h : SealedPhaseHolds ring N a d phase) :
    SealedPhaseHolds ring M a d phase := by
  have hroot :
      sealedAt ring M a (sealedZero ring) =
        sealedAt ring N a (sealedZero ring) :=
    heq (sealedZero ring) (by dsimp [sealedZero]; omega)
  cases phase with
  | ready =>
      refine ⟨?_, ?_⟩
      · rw [hroot]
        exact h.1
      · exact sealed_same_no_bullet ring N M a d heq h.2
  | dummy p =>
      have hp : p.val < d := h.1.1
      refine ⟨sealed_same_unique ring N M a d p 1 heq h.1, ?_, ?_⟩
      · rw [hroot]
        exact h.2.1
      · exact sealed_same_trail ring N M a d p hp heq h.2.2
  | live p =>
      have hp : p.val < d := h.1.1
      refine ⟨sealed_same_unique ring N M a d p 2 heq h.1, ?_, ?_⟩
      · rw [hroot]
        exact h.2.1
      · exact sealed_same_trail ring N M a d p hp heq h.2.2
  | returning q =>
      refine ⟨sealed_same_no_bullet ring N M a d heq h.1, ?_, ?_⟩
      · rw [hroot]
        exact h.2.1
      · exact sealed_same_front ring N M a d q heq h.2.2

def SealedEdgeDisjoint {n : Nat} (ring : DirectedRing n)
    (a : Fin n) (d : Nat) (e : Fin n) : Prop :=
  ∀ k : Fin n, k.val < d →
    sealedSite ring a k.val ≠ e ∧
    sealedSite ring a k.val ≠ ring.rightNeighbor e

theorem sealed_sector_frame {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a : Fin n) (d : Nat) (e : Fin n)
    (h : SealedEdgeDisjoint ring a d e) :
    SameSealedSector ring a d N (nativeE ring N e) := by
  intro k hk
  obtain ⟨hne, hnj⟩ := h k hk
  change (nativeE ring N e (sealedSite ring a k.val)) =
    N (sealedSite ring a k.val)
  simp [nativeE, hne, hnj]

theorem sealed_phase_frame {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a : Fin n) (d : Nat) (hd : 0 < d)
    (e : Fin n) (phase : SealedPhase n)
    (hdisjoint : SealedEdgeDisjoint ring a d e)
    (hphase : SealedPhaseHolds ring N a d phase) :
    SealedPhaseHolds ring (nativeE ring N e) a d phase :=
  sealed_phase_congr ring N (nativeE ring N e) a d hd phase
    (sealed_sector_frame ring N a d e hdisjoint) hphase

theorem sealed_frame {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a : Fin n) (d : Nat) (hd : 0 < d)
    (e : Fin n) (hdisjoint : SealedEdgeDisjoint ring a d e)
    (h : Sealed ring N a d) :
    Sealed ring (nativeE ring N e) a d := by
  obtain ⟨phase, hphase⟩ := h
  exact ⟨phase,
    sealed_phase_frame ring N a d hd e phase hdisjoint hphase⟩

/-! No new internal leader after pure E (independent of phases). -/

private theorem sealed_fin_cases (b : Fin 3) :
    b = (0 : Fin 3) ∨ b = (1 : Fin 3) ∨ b = (2 : Fin 3) := by
  rcases b with ⟨v, hv⟩
  rcases v with _ | _ | _ | v
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · omega

private theorem sealed_row_no_new_leader (x y : CertNative) :
    ((certLiteralEPair x y).1.l = true → x.l = true) ∧
    ((certLiteralEPair x y).2.l = true → y.l = true) := by
  rcases x with ⟨xl, xb, xsh, xsg⟩
  rcases y with ⟨yl, yb, ysh, ysg⟩
  rcases sealed_fin_cases xb with rfl | rfl | rfl <;>
  rcases sealed_fin_cases yb with rfl | rfl | rfl <;>
  cases xl <;> cases yl <;> cases xsh <;> cases ysh <;>
  cases xsg <;> cases ysg <;> decide

theorem sealed_native_no_new_leader {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (e i : Fin n) (h : (nativeE ring N e i).l = true) :
    (N i).l = true := by
  by_cases hie : i = e
  · subst i
    apply (sealed_row_no_new_leader
      (N e) (N (ring.rightNeighbor e))).1
    simpa [nativeE] using h
  · by_cases hij : i = ring.rightNeighbor e
    · subst i
      apply (sealed_row_no_new_leader
        (N e) (N (ring.rightNeighbor e))).2
      simpa [nativeE, hie] using h
    · simpa [nativeE, hie, hij] using h

theorem consecutive_native_step_of_survival {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a b : Fin n) (d : Nat) (e : Fin n)
    (h : ConsecutiveNative ring N a b d)
    (ha : (nativeE ring N e a).l = true)
    (hb : (nativeE ring N e b).l = true) :
    ConsecutiveNative ring (nativeE ring N e) a b d := by
  rcases h with ⟨hdpos, hdlt, hsite, _ha, _hb, hbetween⟩
  refine ⟨hdpos, hdlt, hsite, ha, hb, ?_⟩
  intro k hkpos hklt
  cases hh : (sealedAt ring (nativeE ring N e) a k).l with
  | false => rfl
  | true =>
      have hpre := sealed_native_no_new_leader ring N e
        (sealedSite ring a k.val) hh
      have hfalse : (N (sealedSite ring a k.val)).l = false := hbetween k hkpos hklt
      rw [hfalse] at hpre
      cases hpre

/-! Selected literal owner-row certificates. -/

theorem sealed_row_ready_out (x y : CertNative)
    (hxl : x.l = true) (hxs : x.sg = true)
    (hyl : y.l = false) (hyb : y.b = (0 : Fin 3)) :
    (certLiteralEPair x y).1.b = (0 : Fin 3) ∧
    (certLiteralEPair x y).1.sh = true ∧
    (certLiteralEPair x y).1.sg = false ∧
    (certLiteralEPair x y).2.b = (2 : Fin 3) ∧
    (certLiteralEPair x y).2.sg = false := by
  simp [certLiteralEPair, hxl, hxs, hyl, hyb, certFinThree]

theorem sealed_row_return_left (x y : CertNative)
    (hxl : x.l = false) (hxb : x.b = (0 : Fin 3))
    (hxs : x.sg = false)
    (hy : y.l = true ∨ y.sg = true) :
    (certLiteralEPair x y).1.b = (0 : Fin 3) ∧
    (certLiteralEPair x y).1.sg = true := by
  rcases hy with hyl | hys
  · simp [certLiteralEPair, hxl, hxb, hxs, hyl, certFinThree]
  · by_cases hyl : y.l = true
    · simp [certLiteralEPair, hxl, hxb, hxs, hyl, certFinThree]
    · have hylfalse : y.l = false := by
        cases hh : y.l with
        | false => rfl
        | true => exact False.elim (hyl hh)
      simp [certLiteralEPair, hxl, hxb, hxs, hylfalse, hys,
        certFinThree]

theorem sealed_row_follower_bullet (x y : CertNative)
    (hxl : x.l = false) (hxs : x.sg = false)
    (hxb : x.b ≠ (0 : Fin 3)) (hyl : y.l = false) :
    (certLiteralEPair x y).1.b = (0 : Fin 3) ∧
    (certLiteralEPair x y).1.sg = false ∧
    (certLiteralEPair x y).2.sg = false := by
  have hpos : 0 < x.b.val := by
    have hne : x.b.val ≠ 0 := by
      intro hz
      exact hxb (Fin.ext hz)
    omega
  simp [certLiteralEPair, hxl, hxs, hyl, hpos, certFinThree]

/-! The exact finite-word transfer from a bounded potential.
Its one-edge drift hypotheses remain separate obligations. -/

def SealedPrepTarget {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat)
    (N : Fin n → CertNative) : Prop :=
  (N a).l = false ∨ (N b).l = false ∨
    SealedCleanReady ring N a d

theorem sealed_prep_cost_of_rank {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat)
    (rank : (Fin n → CertNative) → Nat)
    (choose : (Fin n → CertNative) → Fin n)
    (hcap : ∀ N, rank N ≤ 3 * d)
    (hstrict : ∀ N, ¬ SealedPrepTarget ring a b d N →
      rank (nativeE ring N (choose N)) + 1 ≤ rank N)
    (hnoninc : ∀ N, ¬ SealedPrepTarget ring a b d N →
      ∀ e, rank (nativeE ring N e) ≤ rank N)
    (N : Fin n → CertNative) (T : Nat) :
    costNumerator (nativeE ring)
      (SealedPrepTarget ring a b d) N T ≤
      n ^ T * (3 * n * d) := by
  have hb := Prob.costNumerator_le_of_nominated_edge
    (nativeE ring) (SealedPrepTarget ring a b d)
    rank choose hstrict hnoninc N T
  calc
    costNumerator (nativeE ring)
        (SealedPrepTarget ring a b d) N T ≤
      n ^ T * (n * rank N) := hb
    _ ≤ n ^ T * (n * (3 * d)) :=
      Nat.mul_le_mul_left (n ^ T)
        (Nat.mul_le_mul_left n (hcap N))
    _ = n ^ T * (3 * n * d) := by ac_rfl

theorem sealed_prep_expected_of_rank {n : Nat}
    (hn : 0 < n) (ring : DirectedRing n)
    (a b : Fin n) (d : Nat)
    (rank : (Fin n → CertNative) → Nat)
    (choose : (Fin n → CertNative) → Fin n)
    (hcap : ∀ N, rank N ≤ 3 * d)
    (hstrict : ∀ N, ¬ SealedPrepTarget ring a b d N →
      rank (nativeE ring N (choose N)) + 1 ≤ rank N)
    (hnoninc : ∀ N, ¬ SealedPrepTarget ring a b d N →
      ∀ e, rank (nativeE ring N e) ≤ rank N)
    (N : Fin n → CertNative) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (nativeE ring) (SealedPrepTarget ring a b d)
      N ((3 * n * d : Nat) : Rat) := by
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (nativeE ring) (SealedPrepTarget ring a b d)
    hn N (3 * n * d)).2
  intro T
  exact sealed_prep_cost_of_rank ring a b d rank choose
    hcap hstrict hnoninc N T


/-! Finite proof-only preparation stage. This is NOT an agent field.
The modes distinguish an initial inherited-bullet sweep from the
causally launched front which is allowed to collide and inherit a
resident bullet without losing its zero-signal trail. -/

inductive SealedPrepMode (n : Nat) where
  | initialSweep (least : Fin n)
  | initialReturn (front : Fin (n + 1))
  | readyWithBullets
  | sweptFront (front : Fin n)
  | finalReturn (front : Fin (n + 1))
  | finished
  deriving DecidableEq, Repr

/-- The two signal-return modes permit front=d, a virtual signal
from the right endpoint's leader bit. No fictitious physical state
or remote read has been introduced. -/
def SealedReturnFront {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a : Fin n) (d : Nat) (q : Fin (n + 1)) : Prop :=
  1 ≤ q.val ∧ q.val ≤ d ∧
  (sealedAt ring N a (sealedZero ring)).sg = false ∧
  SealedNoBullet ring N a d ∧
  (q.val = d ∨
    ∃ k : Fin n, k.val = q.val ∧
      (sealedAt ring N a k).sg = true) ∧
  ∀ k : Fin n, 0 < k.val → k.val < q.val →
    (sealedAt ring N a k).sg = false

/-- Each stage is checked against the current physical projected
sector. The initial-sweep mode permits arbitrary bullets to the
right of its tagged leftmost bullet. -/
def SealedPrepModeHolds {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a b : Fin n) (d : Nat) :
    SealedPrepMode n → Prop
  | .initialSweep p =>
      p.val < d ∧
      (sealedAt ring N a (sealedZero ring)).sg = false ∧
      (sealedAt ring N a p).b ≠ (0 : Fin 3) ∧
      (∀ k : Fin n, k.val < p.val →
        (sealedAt ring N a k).b = (0 : Fin 3))
  | .initialReturn q =>
      SealedReturnFront ring N a d q
  | .readyWithBullets =>
      (sealedAt ring N a (sealedZero ring)).sg = true ∧
      (∃ k : Fin n, k.val < d ∧
        (sealedAt ring N a k).b ≠ (0 : Fin 3))
  | .sweptFront p =>
      p.val < d ∧
      (sealedAt ring N a (sealedZero ring)).sg = false ∧
      (sealedAt ring N a p).b ≠ (0 : Fin 3) ∧
      SealedZeroTrail ring N a p ∧
      (∀ k : Fin n, k.val < p.val →
        (sealedAt ring N a k).b = (0 : Fin 3))
  | .finalReturn q =>
      SealedReturnFront ring N a d q
  | .finished =>
      SealedPrepTarget ring a b d N

/-- Worst-case unscaled service quota for an accepted preparation
mode. The initial sweep has 3d-p credit, while after a ready-source
launch the front has 2d-p-1. -/
def SealedPrepModeQuota {n : Nat}
    (d : Nat) : SealedPrepMode n → Nat
  | .initialSweep p => 3 * d - p.val
  | .initialReturn q => q.val
  | .readyWithBullets => 2 * d
  | .sweptFront p => 2 * d - p.val - 1
  | .finalReturn q => q.val
  | .finished => 0

/-- A uniform finite potential, well-defined even at arbitrary
inconsistent proof-only tags (the row simulation must exclude
those inconsistent tags on its reached histories). -/
def SealedPrepPotential {n : Nat} (d : Nat)
    (z : (Fin n → CertNative) × SealedPrepMode n) : Nat :=
  min (SealedPrepModeQuota d z.2) (3 * d)

theorem sealed_prep_potential_cap {n : Nat}
    (d : Nat)
    (z : (Fin n → CertNative) × SealedPrepMode n) :
    SealedPrepPotential d z ≤ 3 * d :=
  Nat.min_le_right _ _

/-- A case interpreter can carry the proof-only phase and inspect
the actual OLD native pair, selected edge and full actual successor.
This adapter always executes the exact nativeE physical step. -/
def SealedGhostStep {n : Nat} (ring : DirectedRing n)
    (update : SealedPrepMode n → (Fin n → CertNative) →
      Fin n → (Fin n → CertNative) → SealedPrepMode n)
    (z : (Fin n → CertNative) × SealedPrepMode n)
    (e : Fin n) :
    (Fin n → CertNative) × SealedPrepMode n :=
  let next := nativeE ring z.1 e
  (next, update z.2 z.1 e next)

theorem sealed_ghost_projection {n : Nat}
    (ring : DirectedRing n)
    (update : SealedPrepMode n → (Fin n → CertNative) →
      Fin n → (Fin n → CertNative) → SealedPrepMode n)
    (z : (Fin n → CertNative) × SealedPrepMode n)
    (e : Fin n) :
    (SealedGhostStep ring update z e).1 = nativeE ring z.1 e :=
  rfl

/-- Same-scheduler finite-prefix 3nd transfer. The two drift
hypotheses, still pending the actual first-match native-row
controller, are visible rather than smuggled into a fake closure. -/
theorem sealed_prep_ghost_cost_of_drift {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat)
    (update : SealedPrepMode n → (Fin n → CertNative) →
      Fin n → (Fin n → CertNative) → SealedPrepMode n)
    (chosen : ((Fin n → CertNative) × SealedPrepMode n) → Fin n)
    (hdrop : ∀ z, ¬ SealedPrepTarget ring a b d z.1 →
      SealedPrepPotential d
        (SealedGhostStep ring update z (chosen z)) + 1 ≤
      SealedPrepPotential d z)
    (hnoninc : ∀ z, ¬ SealedPrepTarget ring a b d z.1 →
      ∀ e, SealedPrepPotential d
        (SealedGhostStep ring update z e) ≤
        SealedPrepPotential d z)
    (N : Fin n → CertNative) (mode : SealedPrepMode n)
    (T : Nat) :
    costNumerator (nativeE ring)
      (SealedPrepTarget ring a b d) N T ≤
      n ^ T * (3 * n * d) := by
  let next := SealedGhostStep ring update
  let target : ((Fin n → CertNative) × SealedPrepMode n) → Prop :=
    fun z => SealedPrepTarget ring a b d z.1
  have hproj :
      ∀ z e, (next z e).1 = nativeE ring z.1 e := by
    intro z e
    rfl
  have heq := Prob.costNumerator_ghost_eq
    (nativeE ring) next hproj
    (SealedPrepTarget ring a b d) (N, mode) T
  have hcost := Prob.costNumerator_le_of_nominated_edge
    next target (SealedPrepPotential d) chosen
    hdrop hnoninc (N, mode) T
  calc
    costNumerator (nativeE ring)
        (SealedPrepTarget ring a b d) N T =
      costNumerator next target (N, mode) T := heq.symm
    _ ≤ n ^ T * (n * SealedPrepPotential d (N, mode)) := hcost
    _ ≤ n ^ T * (n * (3 * d)) :=
      Nat.mul_le_mul_left (n ^ T)
        (Nat.mul_le_mul_left n
          (sealed_prep_potential_cap d (N, mode)))
    _ = n ^ T * (3 * n * d) := by ac_rfl



/-! Restricting the finite prefix clock to peaceful starting states.
The artificial extra target is unreachable along an initially
peaceful native E path by the compiled nativeE_preserves_P theorem. -/

def SealedPrepOrUnpeaceful {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat)
    (N : Fin n → CertNative) : Prop :=
  ¬ P ring N ∨ SealedPrepTarget ring a b d N

/-- Equal finite first-hit costs from an initially peaceful native
word; the non-peaceful extra target is never visited. -/
theorem sealed_cost_target_eq_on_peaceful {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (a b : Fin n) (d : Nat) :
    ∀ T : Nat, ∀ N : Fin n → CertNative, P ring N →
      costNumerator (nativeE ring)
        (SealedPrepOrUnpeaceful ring a b d) N T =
      costNumerator (nativeE ring)
        (SealedPrepTarget ring a b d) N T := by
  classical
  intro T
  induction T with
  | zero =>
      intro N _
      simp only [costNumerator_zero]
  | succ T ih =>
      intro N hP
      by_cases htarget : SealedPrepTarget ring a b d N
      · have hboth : SealedPrepOrUnpeaceful ring a b d N :=
          Or.inr htarget
        rw [costNumerator_terminal (nativeE ring)
              (SealedPrepOrUnpeaceful ring a b d)
              N hboth (T + 1),
            costNumerator_terminal (nativeE ring)
              (SealedPrepTarget ring a b d)
              N htarget (T + 1)]
      · have hnot :
            ¬ SealedPrepOrUnpeaceful ring a b d N := by
          intro h
          rcases h with hp | ht
          · exact hp hP
          · exact htarget ht
        rw [costNumerator_succ (nativeE ring)
              (SealedPrepOrUnpeaceful ring a b d)
              N hnot T,
            costNumerator_succ (nativeE ring)
              (SealedPrepTarget ring a b d)
              N htarget T]
        have hsum := ofFn_sum_eq
          (fun e : Fin n =>
            costNumerator (nativeE ring)
              (SealedPrepOrUnpeaceful ring a b d)
              (nativeE ring N e) T)
          (fun e : Fin n =>
            costNumerator (nativeE ring)
              (SealedPrepTarget ring a b d)
              (nativeE ring N e) T)
          (fun e =>
            ih (nativeE ring N e)
              (nativeE_preserves_P hn ring N e hP))
        exact congrArg (fun z : Nat => n ^ (T + 1) + z) hsum

/-- The rank contract now needs drift only on genuinely peaceful
states, matching the quantifier in lem:app-sealed. The 3nd ceiling
still depends on constructing the missing concrete rank. -/
theorem sealed_prep_cost_of_peaceful_rank {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (a b : Fin n) (d : Nat)
    (rank : (Fin n → CertNative) → Nat)
    (choose : (Fin n → CertNative) → Fin n)
    (hcap : ∀ N, rank N ≤ 3 * d)
    (hstrict : ∀ N, P ring N →
      ¬ SealedPrepTarget ring a b d N →
      rank (nativeE ring N (choose N)) + 1 ≤ rank N)
    (hnoninc : ∀ N, P ring N →
      ¬ SealedPrepTarget ring a b d N →
      ∀ e, rank (nativeE ring N e) ≤ rank N)
    (N : Fin n → CertNative) (hP : P ring N)
    (T : Nat) :
    costNumerator (nativeE ring)
      (SealedPrepTarget ring a b d) N T ≤
      n ^ T * (3 * n * d) := by
  have hdropAll :
      ∀ M, ¬ SealedPrepOrUnpeaceful ring a b d M →
        rank (nativeE ring M (choose M)) + 1 ≤ rank M := by
    intro M h
    have hp : P ring M := by
      by_cases hp : P ring M
      · exact hp
      · exact False.elim (h (Or.inl hp))
    have ht : ¬ SealedPrepTarget ring a b d M := by
      intro htarget
      exact h (Or.inr htarget)
    exact hstrict M hp ht
  have hmonoAll :
      ∀ M, ¬ SealedPrepOrUnpeaceful ring a b d M →
        ∀ e, rank (nativeE ring M e) ≤ rank M := by
    intro M h e
    have hp : P ring M := by
      by_cases hp : P ring M
      · exact hp
      · exact False.elim (h (Or.inl hp))
    have ht : ¬ SealedPrepTarget ring a b d M := by
      intro htarget
      exact h (Or.inr htarget)
    exact hnoninc M hp ht e
  have hclock := Prob.costNumerator_le_of_nominated_edge
    (nativeE ring) (SealedPrepOrUnpeaceful ring a b d)
    rank choose hdropAll hmonoAll N T
  calc
    costNumerator (nativeE ring)
        (SealedPrepTarget ring a b d) N T =
      costNumerator (nativeE ring)
        (SealedPrepOrUnpeaceful ring a b d) N T :=
      (sealed_cost_target_eq_on_peaceful
        hn ring a b d T N hP).symm
    _ ≤ n ^ T * (n * rank N) := hclock
    _ ≤ n ^ T * (n * (3 * d)) :=
      Nat.mul_le_mul_left (n ^ T)
        (Nat.mul_le_mul_left n (hcap N))
    _ = n ^ T * (3 * n * d) := by ac_rfl


end L3
