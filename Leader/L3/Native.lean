import Leader.L3.Protocol
import Leader.PPL.Safety.PeacefulScan

namespace L3

set_option autoImplicit false

/-!
Native E and safety.
The imported PPL/Safety/PeacefulScan is an existing
core Lean development, not Mathlib or Batteries. We reuse its PURE
four-field E proof only, NOT its different, pre-E birth rule.
-/

/-- purification.tex:35-41; Agent.certNative in CertRows.lean. -/
def nativeProjection {n : Nat} {c : Compiled}
    (C : Fin n → Agent c) : Fin n → CertNative :=
  fun i => (C i).certNative

/-- purification.tex:42-71, literal E; source wins if n=1. -/
def nativeE {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (e : Fin n) :
    Fin n → CertNative :=
  let j := ring.rightNeighbor e
  let out := certLiteralEPair (N e) (N j)
  fun k => if k = e then out.1
    else if k = j then out.2 else N k

/-- purification.tex:25-31,186-196; Base.lean:441-442,495-500.
    L3's post-E birth is (leader,empty,shielded,signal0). -/
def canonicalBirth {n : Nat}
    (N : Fin n → CertNative) (z : Fin n) :
    Fin n → CertNative :=
  fun i => if i = z then firedNative else N i

/-- Base.lean:321-331. FIRE tests post-E follower and empty bullet. -/
def BirthEligible {n : Nat} (N : Fin n → CertNative)
    (z : Fin n) : Prop :=
  (N z).l = false ∧ (N z).b = (0 : Fin 3)

/-- purification.tex:40-41: B=2 live, B=1 dummy. -/
def LiveBullet {n : Nat} (N : Fin n → CertNative)
    (v : Fin n) : Prop := (N v).b = (2 : Fin 3)

/-- purification.tex:40-41; repair.tex:120-122.
    Either live or dummy is present iff b != 0. -/
def HasBullet {n : Nat} (N : Fin n → CertNative)
    (v : Fin n) : Prop := (N v).b ≠ (0 : Fin 3)

/-- purification.tex:75-77. Nearest counterclockwise leader,
    including v itself when v is a leader. -/
def leaderSector {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (p v : Fin n) : Prop :=
  (N p).l = true ∧
    PPL.dLLBy ring (fun i => (N i).l) v =
      some (PPL.cyclicOffset ring p v)

/-- purification.tex:75-80: signal-zero clockwise arc p..v,
    BOTH endpoints included. -/
def signalTrail {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (p v : Fin n) : Prop :=
  ∀ k : Fin n, k.val ≤ PPL.cyclicOffset ring p v →
    (N (PPL.shiftRight ring p k.val)).sg = false

/-- purification.tex:75-86. Existing core-Lean PeacefulCore
    tests nearest leader shield and inclusive zero-signal arc;
    on a rootless ring, ALL signals must be zero. This predicate
    restricts only B=2, not a dummy B=1. -/
def PeacefulBullet {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (v : Fin n) : Prop :=
  LiveBullet N v →
    PPL.PeacefulCore ring
      (fun i => (N i).l)
      (fun i => (N i).sh)
      (fun i => (N i).sg) v

/-- purification.tex:81-86: every live bullet is peaceful.
    No live bullet imposes no condition. -/
def P {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) : Prop :=
  ∀ v : Fin n, PeacefulBullet ring N v

/-- purification.tex:81-83: P containing at least one leader. -/
def PPlus {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) : Prop :=
  (∃ p : Fin n, (N p).l = true) ∧ P ring N

/-- repair.tex:113-118: protected means PPlus; a bullet-free
    leader need not have any particular shield value. -/
def Protected {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) : Prop := PPlus ring N

/-- repair.tex:120-131: p's sector occupies offsets [0,d),
    where the next leader is at d; for a unique leader d=n. -/
def sectorLength {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (p : Fin n) (d : Fin (n + 1)) : Prop :=
  0 < d.val ∧
  (N p).l = true ∧
  (N (PPL.shiftRight ring p d.val)).l = true ∧
  ∀ k : Fin n, 0 < k.val → k.val < d.val →
    (N (PPL.shiftRight ring p k.val)).l = false

/-- repair.tex:127-131: signal word on [lo,hi) is 0*1*.
    The split point is a proof variable, not a local state. -/
def signalZeroStarOneStar {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (p : Fin n)
    (lo hi : Nat) : Prop :=
  ∃ cut : Fin (n + 1),
    lo ≤ cut.val ∧ cut.val ≤ hi ∧
    (∀ k : Fin n, lo ≤ k.val → k.val < cut.val →
      (N (PPL.shiftRight ring p k.val)).sg = false) ∧
    (∀ k : Fin n, cut.val ≤ k.val → k.val < hi →
      (N (PPL.shiftRight ring p k.val)).sg = true)

/-- repair.tex:120-123: PPlus, at most one bullet of EITHER
    kind per sector, and the full leader-to-bullet zero trail. -/
def I {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) : Prop :=
  PPlus ring N ∧
    ∀ (p : Fin n) (d : Fin (n + 1)),
      sectorLength ring N p d →
        (∀ (a b : Fin n), a.val < d.val → b.val < d.val →
          HasBullet N (PPL.shiftRight ring p a.val) →
          HasBullet N (PPL.shiftRight ring p b.val) → a = b) ∧
        (∀ a : Fin n, a.val < d.val →
          HasBullet N (PPL.shiftRight ring p a.val) →
          ∀ k : Fin n, k.val ≤ a.val →
            (N (PPL.shiftRight ring p k.val)).sg = false)

/-- repair.tex:123-134. When a bullet is at h: zero
    signals through h and suffix (h+1)..(d-1) of 0*1*.
    Otherwise followers 1..d-1 are 0*1*, and a ready
    leader (sg=1) requires every follower signal to be 1. -/
def C_native {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) : Prop :=
  I ring N ∧
    ∀ (p : Fin n) (d : Fin (n + 1)),
      sectorLength ring N p d →
        ((∃ h : Fin n, h.val < d.val ∧
            HasBullet N (PPL.shiftRight ring p h.val) ∧
            (∀ k : Fin n, k.val ≤ h.val →
              (N (PPL.shiftRight ring p k.val)).sg = false) ∧
            signalZeroStarOneStar ring N p (h.val + 1) d.val)
          ∨
          ((∀ h : Fin n, h.val < d.val →
              ¬ HasBullet N (PPL.shiftRight ring p h.val)) ∧
            signalZeroStarOneStar ring N p 1 d.val ∧
            ((N p).sg = true →
              ∀ k : Fin n, 1 ≤ k.val → k.val < d.val →
                (N (PPL.shiftRight ring p k.val)).sg = true)))

instance decidableLiveBullet {n : Nat}
    (N : Fin n → CertNative) (v : Fin n) :
    Decidable (LiveBullet N v) := by
  unfold LiveBullet
  infer_instance

instance decidableHasBullet {n : Nat}
    (N : Fin n → CertNative) (v : Fin n) :
    Decidable (HasBullet N v) := by
  unfold HasBullet
  infer_instance

instance decidableLeaderSector {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (p v : Fin n) : Decidable (leaderSector ring N p v) := by
  unfold leaderSector
  infer_instance

instance decidableSignalTrail {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (p v : Fin n) : Decidable (signalTrail ring N p v) := by
  unfold signalTrail
  infer_instance

instance decidablePeacefulBullet {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (v : Fin n) : Decidable (PeacefulBullet ring N v) := by
  unfold PeacefulBullet LiveBullet
  infer_instance

instance decidableP {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) : Decidable (P ring N) := by
  unfold P
  infer_instance

instance decidablePPlus {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) : Decidable (PPlus ring N) := by
  unfold PPlus
  infer_instance

instance decidableProtected {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) : Decidable (Protected ring N) := by
  unfold Protected
  infer_instance

instance decidableSectorLength {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (p : Fin n) (d : Fin (n + 1)) :
    Decidable (sectorLength ring N p d) := by
  unfold sectorLength
  infer_instance

instance decidableSignalSuffix {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (p : Fin n) (lo hi : Nat) :
    Decidable (signalZeroStarOneStar ring N p lo hi) := by
  unfold signalZeroStarOneStar
  infer_instance

instance decidableI {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) : Decidable (I ring N) := by
  unfold I
  infer_instance

instance decidableC_native {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) : Decidable (C_native ring N) := by
  unfold C_native
  infer_instance

/-! The native E row has the same four-field effects as the
    already proved core-Lean PPL.Elim.rowE, but not the
    same canonical-birth rule. -/

private def toCell (a : CertNative) : PPL.Elim.Cell4 :=
  { leader := a.l, bullet := a.b,
    shield := a.sh, signalB := a.sg }

private def nativeCells {n : Nat}
    (N : Fin n → CertNative) : Fin n → PPL.Elim.Cell4 :=
  fun i => toCell (N i)

private theorem fin3Cases (b : Fin 3) :
    b = (0 : Fin 3) ∨ b = (1 : Fin 3) ∨
      b = (2 : Fin 3) := by
  rcases b with ⟨v, hv⟩
  rcases v with _ | _ | _ | v
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · omega

/-- Finite 24-by-24 local-row equality; kernel decide is small. -/
private theorem cert_row_bridge (a b : CertNative) :
    (toCell (certLiteralEPair a b).1,
     toCell (certLiteralEPair a b).2) =
      PPL.Elim.rowE (toCell a) (toCell b) := by
  rcases a with ⟨al, ab, ash, asg⟩
  rcases b with ⟨bl, bb, bsh, bsg⟩
  rcases fin3Cases ab with ha | ha | ha <;>
  rcases fin3Cases bb with hb | hb | hb <;>
  rw [ha, hb] <;>
  cases al <;> cases bl <;>
  cases ash <;> cases bsh <;>
  cases asg <;> cases bsg <;>
  decide

private theorem nativeE_cells_step {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (e : Fin n) :
    nativeCells (nativeE ring N e) =
      PopulationProtocol.step PPL.Elim.protocolE ring
        (nativeCells N) e := by
  funext k
  have hp := cert_row_bridge (N e) (N (ring.rightNeighbor e))
  by_cases he : k = e
  · subst k
    simpa [nativeCells, nativeE, PopulationProtocol.step, PPL.Elim.protocolE]
      using congrArg Prod.fst hp
  · by_cases hj : k = ring.rightNeighbor e
    · have hne : ring.rightNeighbor e ≠ e := by
        intro h
        exact he (hj.trans h)
      subst k
      simpa [nativeCells, nativeE, PopulationProtocol.step, PPL.Elim.protocolE, hne]
        using congrArg Prod.snd hp
    · simp [nativeCells, nativeE, PopulationProtocol.step, he, hj]

private theorem rightNeighbor_ne_self {n : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n) (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  change (e.val + 1) % n = e.val at hv
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : e.val + 1 = n := by omega
    rw [heq, Nat.mod_self] at hv
    omega

private theorem nativeE_fourFieldCase {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (N : Fin n → CertNative) (e : Fin n) :
    PPL.Safety.PeacefulProps.FourFieldStepCase ring
      (nativeCells N) (nativeCells (nativeE ring N e)) e := by
  rw [nativeE_cells_step]
  unfold PPL.Safety.PeacefulProps.FourFieldStepCase
  dsimp only
  constructor
  · intro k hke hkj
    simp [PopulationProtocol.step, PPL.Elim.protocolE, hke, hkj]
  · left
    constructor
    · simp [PopulationProtocol.step, PPL.Elim.protocolE]
    · have hne : ring.rightNeighbor e ≠ e :=
        rightNeighbor_ne_self (by omega) ring e
      simp [PopulationProtocol.step, PPL.Elim.protocolE, hne]

/-- purification.tex:91-97, pure-E half.
    Uses the proved four-field locality theorem.
    Scope n>=3; no initial reachability assumption. -/
theorem nativeE_preserves_P {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (N : Fin n → CertNative) (e : Fin n)
    (hP : P ring N) :
    P ring (nativeE ring N e) := by
  let D := nativeCells N
  let D' := nativeCells (nativeE ring N e)
  have hcase :
      PPL.Safety.PeacefulProps.FourFieldStepCase
        ring D D' e := by
    simpa [D, D'] using nativeE_fourFieldCase hn ring N e
  have hlocal :=
    PPL.Safety.PeacefulProps.peacefulScanLocality
      hn ring D D' e hcase
  have hbefore :
      ∀ i : Fin n, (D i).bullet = (2 : Fin 3) →
        PPL.Safety.PeacefulProps.Peaceful4 ring D i := by
    intro i hi
    exact hP i hi
  change ∀ i : Fin n,
    (D' i).bullet = (2 : Fin 3) →
      PPL.Safety.PeacefulProps.Peaceful4 ring D' i
  intro i hafter
  by_cases hsame : (D i).bullet = (2 : Fin 3)
  · exact (hlocal.2.2 i hsame (hbefore i hsame)).1 hafter
  · by_cases hij : i = ring.rightNeighbor e
    · subst i
      by_cases hleft : (D e).bullet = (2 : Fin 3)
      · exact (hlocal.2.2 e hleft (hbefore e hleft)).2
          rfl hafter hsame
      · exact hlocal.2.1 _ hafter hsame (Or.inr hleft)
    · exact hlocal.2.1 i hafter hsame (Or.inl hij)

/-- purification.tex:91-97,169-183: pure-E keeps
    at least one leader and preserves P for n>=3. -/
theorem nativeE_preserves_PPlus {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (N : Fin n → CertNative) (e : Fin n)
    (h : PPlus ring N) :
    PPlus ring (nativeE ring N e) := by
  let D := nativeCells N
  let D' := nativeCells (nativeE ring N e)
  have hcase :
      PPL.Safety.PeacefulProps.FourFieldStepCase
        ring D D' e := by
    simpa [D, D'] using nativeE_fourFieldCase hn ring N e
  have hlocal :=
    PPL.Safety.PeacefulProps.peacefulScanLocality
      hn ring D D' e hcase
  have hpb : PPL.Safety.PeacefulProps.PB4 ring D := by
    exact h
  obtain ⟨i, hi⟩ := hlocal.1 hpb
  exact ⟨⟨i, hi⟩, nativeE_preserves_P hn ring N e h.2⟩

/-- A birth always establishes at least one leader.
    This does NOT assert the unfinished P-preservation claim. -/
theorem canonicalBirth_has_leader {n : Nat}
    (N : Fin n → CertNative) (z : Fin n) :
    ∃ p : Fin n, (canonicalBirth N z p).l = true := by
  refine ⟨z, ?_⟩
  simp [canonicalBirth, firedNative]

/-! n=5 non-vacuity checks; intended for kernel decide. -/

private theorem fiveRing_pos : 5 > 0 := by decide
private def fiveRing : DirectedRing 5 := ⟨by decide⟩

private def nativeZero : CertNative :=
  { l := false, b := 0, sh := false, sg := false }

def fivePeaceful : Fin 5 → CertNative :=
  fun i => if i.val = 0 then
    { l := true, b := 0, sh := true, sg := false }
  else if i.val = 2 then
    { l := false, b := 2, sh := false, sg := false }
  else nativeZero

def fiveUnpeaceful : Fin 5 → CertNative :=
  fun i => if i.val = 0 then
    { l := true, b := 0, sh := false, sg := false }
  else if i.val = 2 then
    { l := false, b := 2, sh := false, sg := false }
  else nativeZero

example : PPlus fiveRing fivePeaceful := by decide
example : ¬ P fiveRing fiveUnpeaceful := by decide

end L3
