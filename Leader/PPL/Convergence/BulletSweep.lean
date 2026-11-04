import Leader.PPL.Safety.PeacefulScan
import Leader.PPL.TokenCorrectness.Ghost
import Leader.PPL.Probability.FixedWord
import Leader.Core.LeaderCountDyadicTail

/-!
# P_PL Lemma 15: deterministic bullet sweep

This file proves the literal two-clockwise-sweep execution theorem.

The paper's random-time use of the same word is slightly stronger: its
"occurs" relation is ordered-subsequence occurrence with arbitrary scheduler
letters between the selected letters.  The repository's FixedWord asset counts
that ordered-subsequence event.  The current P_PL safety layer has no bullet
identity/lineage object with which to transport one initially nonpeaceful live
bullet through arbitrary interleavings.  Consequently the exact Nat headline
is stated below as one named Prop.  The fixed-word arithmetic, including the
constant c15 = 1, is nevertheless proved.

No transition semantics is reimplemented: every full physical step used in
the sweep is related to Algorithm 5 through
PPL.Safety.PeacefulProps.step_fourField_cases.
-/

namespace PPL.Convergence.BulletSweep

set_option autoImplicit false
set_option Elab.async false

open PPL.Probability
open PPL.Safety.PeacefulProps

abbrev Config (n psi kappa : Nat) :=
  PPL.Config n psi kappa

def step
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e : Fin n) : Config n psi kappa :=
  PopulationProtocol.step (PPL.protocol psi kappa) ring C e

def run
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (word : DetSchedule n) : Config n psi kappa :=
  runPopulationSchedule (PPL.protocol psi kappa) ring C word

def zeroSite {n : Nat} (ring : DirectedRing n) : Fin n :=
  ⟨0, ring.hn⟩

def edgeAt {n : Nat}
    (ring : DirectedRing n) (k : Nat) : Fin n :=
  PPL.shiftRight ring (zeroSite ring) k

/-- Paper (seq_R(0,n))^2. -/
def lemma15SweepWord {n : Nat}
    (ring : DirectedRing n) : DetSchedule n :=
  PPL.seqR ring (zeroSite ring) n ++
    PPL.seqR ring (zeroSite ring) n

def lemma15K (n : Nat) : Nat :=
  Nat.log2 n + 1

def lemma15Horizon (n : Nat) : Nat :=
  2 * n * (2 * n + 4 * lemma15K n)

/-- The exact constant supplied by the fixed-word arithmetic. -/
def c15 : Nat := 1

/-- Every live bullet is peaceful.  Unlike CPB, this does not require a
leader to be present. -/
def AllLivePeaceful
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) : Prop :=
  ∀ i : Fin n,
    (C i).bullet = (2 : Fin 3) →
      PPL.Peaceful ring C i

private instance instDecidableAllLivePeaceful
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) :
    Decidable (AllLivePeaceful ring C) := by
  unfold AllLivePeaceful
  infer_instance

private def BadLive4
    {n : Nat}
    (ring : DirectedRing n)
    (D : Fin n → Cell4)
    (i : Fin n) : Prop :=
  (D i).bullet = (2 : Fin 3) ∧
    ¬ Peaceful4 ring D i

private def NoBad4
    {n : Nat}
    (ring : DirectedRing n)
    (D : Fin n → Cell4) : Prop :=
  ∀ i : Fin n, ¬ BadLive4 ring D i

private theorem fin3_cases
    (b : Fin 3) :
    b = (0 : Fin 3) ∨
      b = (1 : Fin 3) ∨
      b = (2 : Fin 3) := by
  rcases b with ⟨v, hv⟩
  rcases v with _ | _ | _ | v
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · omega

private theorem rowE_left_bullet_zero
    (l r : Cell4) :
    (PPL.Elim.rowE l r).1.bullet = (0 : Fin 3) := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases lb with rfl | rfl | rfl <;>
  rcases fin3_cases rb with rfl | rfl | rfl <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp [PPL.Elim.rowE]

private theorem rowE_right_born4
    (l : Cell4) :
    (PPL.Elim.rowE l born4).2 = born4 := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases fin3_cases lb with rfl | rfl | rfl <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  simp [PPL.Elim.rowE, born4]

/-- In the ordinary row, if the responder was not already live and ends live,
then this is literal line-59 movement into a follower, and line 60 has cleared
the responder signal. -/
private theorem rowE_moved_live_right_fields
    (l r : Cell4)
    (hr : r.bullet ≠ (2 : Fin 3))
    (hout :
      (PPL.Elim.rowE l r).2.bullet = (2 : Fin 3)) :
    (PPL.Elim.rowE l r).2.leader = false ∧
      (PPL.Elim.rowE l r).2.signalB = false := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases lb with rfl | rfl | rfl <;>
  rcases fin3_cases rb with rfl | rfl | rfl <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp_all [PPL.Elim.rowE]

/-- The same movement branch also keeps a follower/signal-zero source cleared
after line 62. -/
private theorem rowE_moved_live_pair_fields
    (l r : Cell4)
    (hll : l.leader = false)
    (hls : l.signalB = false)
    (hr : r.bullet ≠ (2 : Fin 3))
    (hout :
      (PPL.Elim.rowE l r).2.bullet = (2 : Fin 3)) :
    (PPL.Elim.rowE l r).1.leader = false ∧
      (PPL.Elim.rowE l r).1.signalB = false ∧
      (PPL.Elim.rowE l r).2.leader = false ∧
      (PPL.Elim.rowE l r).2.signalB = false := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases lb with rfl | rfl | rfl <;>
  rcases fin3_cases rb with rfl | rfl | rfl <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp_all [PPL.Elim.rowE]

private theorem shiftLeft_zero_local
    {n : Nat} (ring : DirectedRing n)
    (i : Fin n) :
    PPL.shiftLeft ring i 0 = i := by
  apply Fin.ext
  simp [PPL.shiftLeft, Nat.add_mod,
    Nat.mod_eq_of_lt i.isLt]

private theorem dLLBy_self_local
    {n : Nat} (ring : DirectedRing n)
    (leader : Fin n → Bool) (i : Fin n)
    (hi : leader i = true) :
    PPL.dLLBy ring leader i = some 0 := by
  unfold PPL.dLLBy
  cases n with
  | zero =>
      exact Fin.elim0 i
  | succ m =>
      have hz :
          PPL.shiftLeft ring i 0 = i :=
        shiftLeft_zero_local ring i
      simp [PPL.scanDistance, hz, hi]

private theorem peaceful4_self_safe
    {n : Nat} (ring : DirectedRing n)
    (D : Fin n → Cell4) (i : Fin n)
    (hs : (D i).signalB = false)
    (hl : (D i).leader = true)
    (hh : (D i).shield = true) :
    Peaceful4 ring D i := by
  unfold Peaceful4 PPL.PeacefulCore
  rw [dLLBy_self_local
    ring (fun j => (D j).leader) i hl]
  constructor
  · simpa [shiftLeft_zero_local] using hh
  · intro j
    have hj : j.val = 0 := by
      omega
    have hp :
        PPL.shiftLeft ring i j.val = i := by
      rw [hj]
      exact shiftLeft_zero_local ring i
    rw [hp]
    exact hs

private theorem scanDistance_none_of_all_false
    {n : Nat}
    (site : Nat → Fin n)
    (hit : Fin n → Bool)
    (hfalse : ∀ i : Fin n, hit i = false) :
    ∀ fuel start,
      PPL.scanDistance site hit fuel start = none := by
  intro fuel
  induction fuel with
  | zero =>
      intro start
      rfl
  | succ fuel ih =>
      intro start
      simp [PPL.scanDistance, hfalse, ih]

private theorem peaceful4_of_all_follower_signal_zero
    {n : Nat} (ring : DirectedRing n)
    (D : Fin n → Cell4) (i : Fin n)
    (hleader : ∀ q : Fin n, (D q).leader = false)
    (hsignal : ∀ q : Fin n, (D q).signalB = false) :
    Peaceful4 ring D i := by
  unfold Peaceful4 PPL.PeacefulCore
  have hd :
      PPL.dLLBy ring (fun q => (D q).leader) i = none := by
    unfold PPL.dLLBy
    exact
      scanDistance_none_of_all_false
        (fun d => PPL.shiftLeft ring i d)
        (fun q => (D q).leader)
        hleader n 0
  rw [hd]
  exact hsignal

private theorem project_step_case
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e : Fin n) :
    FourFieldStepCase ring
      (project4 C)
      (project4 (step ring C e))
      e := by
  simpa [step] using
    (PPL.Safety.PeacefulProps.step_fourField_cases
      hn3 hpsi ring C e)

private theorem fourField_other
    {n : Nat} (ring : DirectedRing n)
    (D D' : Fin n → Cell4)
    (e q : Fin n)
    (hcase : FourFieldStepCase ring D D' e)
    (hqe : q ≠ e)
    (hqj : q ≠ ring.rightNeighbor e) :
    D' q = D q := by
  unfold FourFieldStepCase at hcase
  dsimp only at hcase
  exact hcase.1 q hqe hqj

private theorem source_bullet_zero4
    {n : Nat} (ring : DirectedRing n)
    (D D' : Fin n → Cell4)
    (e : Fin n)
    (hcase : FourFieldStepCase ring D D' e) :
    (D' e).bullet = (0 : Fin 3) := by
  unfold FourFieldStepCase at hcase
  dsimp only at hcase
  rcases hcase.2 with hrow | hbirth
  · rw [hrow.1]
    exact rowE_left_bullet_zero _ _
  · rw [hbirth.1]
    exact rowE_left_bullet_zero _ _

/-- A nonpeaceful live post-bullet can only descend from an old nonpeaceful
live bullet at the same site, or from the scheduled source moving right.
Fresh line-6/line-20 births and line-52 fires are excluded by the proved R6
new-fire theorem; old peaceful bullets are excluded by the proved keep theorem.
-/
private theorem bad4_origin_step
    {n : Nat}
    (hn3 : 3 ≤ n)
    (ring : DirectedRing n)
    (D D' : Fin n → Cell4)
    (e i : Fin n)
    (hcase : FourFieldStepCase ring D D' e)
    (hbad : BadLive4 ring D' i) :
    BadLive4 ring D i ∨
      (i = ring.rightNeighbor e ∧
        BadLive4 ring D e) := by
  have hs :=
    PPL.Safety.PeacefulProps.peacefulScanLocality
      hn3 ring D D' e hcase
  by_cases hilive :
      (D i).bullet = (2 : Fin 3)
  · by_cases hipeace : Peaceful4 ring D i
    · have hp :=
        (hs.2.2 i hilive hipeace).1 hbad.1
      exact False.elim (hbad.2 hp)
    · exact Or.inl ⟨hilive, hipeace⟩
  · by_cases hij : i = ring.rightNeighbor e
    · subst i
      by_cases helive :
          (D e).bullet = (2 : Fin 3)
      · by_cases hepeace : Peaceful4 ring D e
        · have hp :=
            (hs.2.2 e helive hepeace).2
              rfl hbad.1 hilive
          exact False.elim (hbad.2 hp)
        · exact
            Or.inr ⟨rfl, helive, hepeace⟩
      · have hp :=
          hs.2.1 (ring.rightNeighbor e)
            hbad.1 hilive (Or.inr helive)
        exact False.elim (hbad.2 hp)
    · have hp :=
        hs.2.1 i hbad.1 hilive (Or.inl hij)
      exact False.elim (hbad.2 hp)

private theorem bad4_destination_fields
    {n : Nat}
    (hn3 : 3 ≤ n)
    (ring : DirectedRing n)
    (D D' : Fin n → Cell4)
    (e : Fin n)
    (hcase : FourFieldStepCase ring D D' e)
    (hrnot :
      (D (ring.rightNeighbor e)).bullet ≠ (2 : Fin 3))
    (hbad :
      BadLive4 ring D' (ring.rightNeighbor e)) :
    (D' (ring.rightNeighbor e)).leader = false ∧
      (D' (ring.rightNeighbor e)).signalB = false := by
  let j := ring.rightNeighbor e
  unfold FourFieldStepCase at hcase
  dsimp only at hcase
  rcases hcase.2 with hrow | hbirth
  · have hrowLive :
        (PPL.Elim.rowE (D e) (D j)).2.bullet =
          (2 : Fin 3) := by
      rw [← hrow.2]
      simpa [j] using hbad.1
    have hf :=
      rowE_moved_live_right_fields
        (D e) (D j)
        (by simpa [j] using hrnot)
        hrowLive
    rw [hrow.2]
    exact hf
  · have hbornEq :
        D' j = born4 :=
      hbirth.2.trans (rowE_right_born4 (D e))
    have hp : Peaceful4 ring D' j := by
      apply peaceful4_self_safe ring D' j
      · rw [hbornEq]
        rfl
      · rw [hbornEq]
        rfl
      · rw [hbornEq]
        rfl
    exact False.elim
      (hbad.2 (by simpa [j] using hp))

private theorem bad4_pair_fields
    {n : Nat}
    (hn3 : 3 ≤ n)
    (ring : DirectedRing n)
    (D D' : Fin n → Cell4)
    (e : Fin n)
    (hcase : FourFieldStepCase ring D D' e)
    (hleftLeader : (D e).leader = false)
    (hleftSignal : (D e).signalB = false)
    (hrnot :
      (D (ring.rightNeighbor e)).bullet ≠ (2 : Fin 3))
    (hbad :
      BadLive4 ring D' (ring.rightNeighbor e)) :
    (D' e).leader = false ∧
      (D' e).signalB = false ∧
      (D' (ring.rightNeighbor e)).leader = false ∧
      (D' (ring.rightNeighbor e)).signalB = false := by
  let j := ring.rightNeighbor e
  unfold FourFieldStepCase at hcase
  dsimp only at hcase
  rcases hcase.2 with hrow | hbirth
  · have hrowLive :
        (PPL.Elim.rowE (D e) (D j)).2.bullet =
          (2 : Fin 3) := by
      rw [← hrow.2]
      simpa [j] using hbad.1
    have hf :=
      rowE_moved_live_pair_fields
        (D e) (D j)
        hleftLeader hleftSignal
        (by simpa [j] using hrnot)
        hrowLive
    rw [hrow.1, hrow.2]
    exact hf
  · have hbornEq :
        D' j = born4 :=
      hbirth.2.trans (rowE_right_born4 (D e))
    have hp : Peaceful4 ring D' j := by
      apply peaceful4_self_safe ring D' j
      · rw [hbornEq]
        rfl
      · rw [hbornEq]
        rfl
      · rw [hbornEq]
        rfl
    exact False.elim
      (hbad.2 (by simpa [j] using hp))

private theorem edgeAt_val_mod
    {n : Nat} (ring : DirectedRing n)
    (k : Nat) :
    (edgeAt ring k).val = k % n := by
  simp [edgeAt, zeroSite, PPL.shiftRight]

private theorem edgeAt_val_of_lt
    {n : Nat} (ring : DirectedRing n)
    (k : Nat) (hk : k < n) :
    (edgeAt ring k).val = k := by
  rw [edgeAt_val_mod, Nat.mod_eq_of_lt hk]

private theorem rightNeighbor_edgeAt
    {n : Nat} (ring : DirectedRing n)
    (k : Nat) :
    ring.rightNeighbor (edgeAt ring k) =
      edgeAt ring (k + 1) := by
  apply Fin.ext
  simp only [edgeAt, zeroSite, PPL.shiftRight,
    DirectedRing.rightNeighbor]
  rw [Nat.zero_add, Nat.zero_add, Nat.mod_add_mod]

private theorem edgeAt_n_eq_zero
    {n : Nat} (ring : DirectedRing n) :
    edgeAt ring n = zeroSite ring := by
  apply Fin.ext
  rw [edgeAt_val_mod, Nat.mod_self]
  rfl

private theorem seqR_succ_local
    {n : Nat} (ring : DirectedRing n)
    (k : Nat) :
    PPL.seqR ring (zeroSite ring) (k + 1) =
      PPL.seqR ring (zeroSite ring) k ++
        [edgeAt ring k] := by
  unfold PPL.seqR edgeAt
  rw [List.ofFn_succ_last]
  rfl

private theorem run_append_local
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (u v : DetSchedule n) :
    run ring C (u ++ v) =
      run ring (run ring C u) v := by
  induction u generalizing C with
  | nil =>
      rfl
  | cons e rest ih =>
      simp only [List.cons_append, run,
        runPopulationSchedule]
      simpa only [run, step] using
        (ih (C := step ring C e))

private theorem run_seqR_succ_local
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (k : Nat) :
    run ring C
        (PPL.seqR ring (zeroSite ring) (k + 1)) =
      step ring
        (run ring C
          (PPL.seqR ring (zeroSite ring) k))
        (edgeAt ring k) := by
  rw [seqR_succ_local, run_append_local]
  rfl

private def BadAbove
    {n : Nat}
    (ring : DirectedRing n)
    (k : Nat)
    (D : Fin n → Cell4) : Prop :=
  ∀ i : Fin n,
    BadLive4 ring D i →
      i.val = 0 ∨ k ≤ i.val

private theorem badAbove_step
    {n : Nat}
    (hn3 : 3 ≤ n)
    (ring : DirectedRing n)
    (D D' : Fin n → Cell4)
    (k : Nat) (hk : k < n)
    (hcase :
      FourFieldStepCase ring D D' (edgeAt ring k))
    (h : BadAbove ring k D) :
    BadAbove ring (k + 1) D' := by
  intro i hbad
  have horigin :=
    bad4_origin_step
      hn3 ring D D' (edgeAt ring k) i hcase hbad
  rcases horigin with hsame | hmoved
  · rcases h i hsame with hzero | hge
    · exact Or.inl hzero
    · by_cases hik : i.val = k
      · have hie : i = edgeAt ring k := by
          apply Fin.ext
          rw [edgeAt_val_of_lt ring k hk]
          exact hik
        subst i
        have hz :=
          source_bullet_zero4
            ring D D' (edgeAt ring k) hcase
        have hb := hbad.1
        rw [hz] at hb
        have hv := congrArg Fin.val hb
        omega
      · exact Or.inr (by omega)
  · rcases hmoved with ⟨hij, hsrc⟩
    subst i
    rw [rightNeighbor_edgeAt]
    by_cases hnext : k + 1 < n
    · exact
        Or.inr
          (by
            rw [edgeAt_val_of_lt ring (k + 1) hnext]
            exact Nat.le_refl _)
    · have heq : k + 1 = n := by
        omega
      left
      rw [heq, edgeAt_val_mod, Nat.mod_self]

private theorem badAbove_firstSweep
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa) :
    ∀ k : Nat, k ≤ n →
      BadAbove ring k
        (project4
          (run ring C
            (PPL.seqR ring (zeroSite ring) k))) := by
  intro k
  induction k with
  | zero =>
      intro hk i hbad
      exact Or.inr (Nat.zero_le _)
  | succ k ih =>
      intro hk
      have hklt : k < n := by
        omega
      let Ck :=
        run ring C
          (PPL.seqR ring (zeroSite ring) k)
      have hprev :
          BadAbove ring k (project4 Ck) := by
        simpa [Ck] using ih (by omega)
      have hcase :=
        project_step_case
          hn3 hpsi ring Ck (edgeAt ring k)
      have hnext :=
        badAbove_step
          hn3 ring
          (project4 Ck)
          (project4 (step ring Ck (edgeAt ring k)))
          k hklt hcase hprev
      have hrun :=
        run_seqR_succ_local ring C k
      rw [hrun]
      exact hnext

private theorem firstSweep_bad_only_zero
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa) :
    ∀ i : Fin n,
      BadLive4 ring
          (project4
            (run ring C
              (PPL.seqR ring (zeroSite ring) n)))
          i →
        i.val = 0 := by
  intro i hbad
  have h :=
    badAbove_firstSweep
      hn3 hpsi ring C n (Nat.le_refl n) i hbad
  rcases h with hzero | hlarge
  · exact hzero
  · omega

private def ClearedThrough
    {n : Nat}
    (k : Nat)
    (D : Fin n → Cell4) : Prop :=
  ∀ q : Fin n,
    1 ≤ q.val →
    q.val ≤ k →
      (D q).leader = false ∧
        (D q).signalB = false

private def BadFront
    {n : Nat}
    (ring : DirectedRing n)
    (k : Nat)
    (D : Fin n → Cell4) : Prop :=
  (∀ i : Fin n,
    BadLive4 ring D i → i.val = k) ∧
  (∀ i : Fin n,
    BadLive4 ring D i →
      ClearedThrough k D)

private theorem bad_post_moved_of_front
    {n : Nat}
    (hn3 : 3 ≤ n)
    (ring : DirectedRing n)
    (D D' : Fin n → Cell4)
    (e : Fin n) (k : Nat)
    (heval : e.val = k)
    (hcase : FourFieldStepCase ring D D' e)
    (hfront : BadFront ring k D)
    (i : Fin n)
    (hbad : BadLive4 ring D' i) :
    i = ring.rightNeighbor e ∧
      BadLive4 ring D e := by
  have horigin :=
    bad4_origin_step
      hn3 ring D D' e i hcase hbad
  rcases horigin with hsame | hmoved
  · have hiv := hfront.1 i hsame
    have hie : i = e := by
      apply Fin.ext
      omega
    subst i
    have hz :=
      source_bullet_zero4 ring D D' e hcase
    have hb := hbad.1
    rw [hz] at hb
    have hv := congrArg Fin.val hb
    omega
  · exact hmoved

private theorem responder_not_live_of_front
    {n : Nat}
    (hn3 : 3 ≤ n)
    (ring : DirectedRing n)
    (D D' : Fin n → Cell4)
    (e : Fin n) (k : Nat)
    (hcase : FourFieldStepCase ring D D' e)
    (hfront : BadFront ring k D)
    (hjne :
      (ring.rightNeighbor e).val ≠ k)
    (hpost :
      BadLive4 ring D' (ring.rightNeighbor e)) :
    (D (ring.rightNeighbor e)).bullet ≠ (2 : Fin 3) := by
  intro hlive
  by_cases hpeace :
      Peaceful4 ring D (ring.rightNeighbor e)
  · have hs :=
      PPL.Safety.PeacefulProps.peacefulScanLocality
        hn3 ring D D' e hcase
    have hp :=
      (hs.2.2 (ring.rightNeighbor e)
        hlive hpeace).1 hpost.1
    exact hpost.2 hp
  · have hv :=
      hfront.1
        (ring.rightNeighbor e)
        ⟨hlive, hpeace⟩
    exact hjne hv

private theorem badFront_step
    {n : Nat}
    (hn3 : 3 ≤ n)
    (ring : DirectedRing n)
    (D D' : Fin n → Cell4)
    (k : Nat)
    (hnext : k + 1 < n)
    (hcase :
      FourFieldStepCase ring D D' (edgeAt ring k))
    (hfront : BadFront ring k D) :
    BadFront ring (k + 1) D' := by
  have hk : k < n := by
    omega
  have heval :
      (edgeAt ring k).val = k :=
    edgeAt_val_of_lt ring k hk
  have hjval :
      (ring.rightNeighbor (edgeAt ring k)).val =
        k + 1 := by
    rw [rightNeighbor_edgeAt,
      edgeAt_val_of_lt ring (k + 1) hnext]
  constructor
  · intro i hbad
    obtain ⟨hij, hsrcBad⟩ :=
      bad_post_moved_of_front
        hn3 ring D D' (edgeAt ring k)
        k heval hcase hfront i hbad
    rw [hij]
    exact hjval
  · intro i hbad
    obtain ⟨hij, hsrcBad⟩ :=
      bad_post_moved_of_front
        hn3 ring D D' (edgeAt ring k)
        k heval hcase hfront i hbad
    subst i
    let j := ring.rightNeighbor (edgeAt ring k)
    have hbadJ : BadLive4 ring D' j := by
      simpa [j] using hbad
    have hrnot :
        (D j).bullet ≠ (2 : Fin 3) := by
      apply
        responder_not_live_of_front
          hn3 ring D D'
          (edgeAt ring k) k
          hcase hfront
      · simpa [j] using (show j.val ≠ k by omega)
      · simpa [j] using hbadJ
    have hdest :
        (D' j).leader = false ∧
          (D' j).signalB = false := by
      simpa [j] using
        (bad4_destination_fields
          hn3 ring D D' (edgeAt ring k)
          hcase
          (by simpa [j] using hrnot)
          (by simpa [j] using hbadJ))
    have hpreTrail :
        ClearedThrough k D :=
      hfront.2 (edgeAt ring k) hsrcBad
    intro q hq1 hqle
    by_cases hqdest : q.val = k + 1
    · have hqj : q = j := by
        apply Fin.ext
        dsimp [j]
        omega
      subst q
      exact hdest
    · have hqk : q.val ≤ k := by
        omega
      by_cases hk0 : k = 0
      · omega
      · by_cases hqsrc : q.val = k
        · have hqe : q = edgeAt ring k := by
            apply Fin.ext
            rw [edgeAt_val_of_lt ring k hk]
            exact hqsrc
          have hsrcPre :
              (D (edgeAt ring k)).leader = false ∧
                (D (edgeAt ring k)).signalB = false :=
            hpreTrail
              (edgeAt ring k)
              (by rw [heval]; omega)
              (by
                rw [heval]
                exact Nat.le_refl _)
          have hpair :=
            bad4_pair_fields
              hn3 ring D D' (edgeAt ring k)
              hcase hsrcPre.1 hsrcPre.2
              (by simpa [j] using hrnot)
              (by simpa [j] using hbadJ)
          subst q
          exact ⟨hpair.1, hpair.2.1⟩
        · have hpre :=
            hpreTrail q hq1 hqk
          have hqe : q ≠ edgeAt ring k := by
            intro h
            have hv := congrArg Fin.val h
            rw [edgeAt_val_of_lt ring k hk] at hv
            exact hqsrc hv
          have hqj : q ≠ j := by
            intro h
            have hv := congrArg Fin.val h
            dsimp [j] at hv
            omega
          have hsame :=
            fourField_other
              ring D D' (edgeAt ring k) q
              hcase hqe
              (by simpa [j] using hqj)
          rw [hsame]
          exact hpre

private theorem badFront_secondSweep
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C0 : Config n psi kappa)
    (h0 : BadFront ring 0 (project4 C0)) :
    ∀ k : Nat, k < n →
      BadFront ring k
        (project4
          (run ring C0
            (PPL.seqR ring (zeroSite ring) k))) := by
  intro k
  induction k with
  | zero =>
      intro hk
      simpa [PPL.seqR, run,
        runPopulationSchedule] using h0
  | succ k ih =>
      intro hk
      have hprevK : k < n := by
        omega
      let Ck :=
        run ring C0
          (PPL.seqR ring (zeroSite ring) k)
      have hprev :
          BadFront ring k (project4 Ck) := by
        simpa [Ck] using ih hprevK
      have hcase :=
        project_step_case
          hn3 hpsi ring Ck (edgeAt ring k)
      have hnext :=
        badFront_step
          hn3 ring
          (project4 Ck)
          (project4 (step ring Ck (edgeAt ring k)))
          k hk hcase hprev
      have hrun :=
        run_seqR_succ_local ring C0 k
      rw [hrun]
      exact hnext

private theorem last_edge_no_bad
    {n : Nat}
    (hn3 : 3 ≤ n)
    (ring : DirectedRing n)
    (D D' : Fin n → Cell4)
    (hcase :
      FourFieldStepCase ring D D'
        (edgeAt ring (n - 1)))
    (hfront :
      BadFront ring (n - 1) D) :
    NoBad4 ring D' := by
  let e := edgeAt ring (n - 1)
  let j := ring.rightNeighbor e
  have heval : e.val = n - 1 := by
    dsimp [e]
    apply edgeAt_val_of_lt
    omega
  have hjeq : j = zeroSite ring := by
    dsimp [j, e]
    rw [rightNeighbor_edgeAt]
    have hn : n - 1 + 1 = n := by
      omega
    rw [hn, edgeAt_n_eq_zero]
  have hjval : j.val = 0 := by
    rw [hjeq]
    rfl
  intro i hbad
  obtain ⟨hij, hsrcBad⟩ :=
    bad_post_moved_of_front
      hn3 ring D D' e (n - 1)
      heval
      (by simpa [e] using hcase)
      hfront i hbad
  subst i
  have hbadJ : BadLive4 ring D' j := by
    simpa [j] using hbad
  have hrnot :
      (D j).bullet ≠ (2 : Fin 3) := by
    apply
      responder_not_live_of_front
        hn3 ring D D' e (n - 1)
        (by simpa [e] using hcase)
        hfront
    · rw [hjval]
      omega
    · simpa [j] using hbadJ
  have hsrcTrail :
      ClearedThrough (n - 1) D :=
    hfront.2 e hsrcBad
  have hsrcPre :
      (D e).leader = false ∧
        (D e).signalB = false :=
    hsrcTrail e
      (by rw [heval]; omega)
      (by
        rw [heval]
        exact Nat.le_refl _)
  have hpair :=
    bad4_pair_fields
      hn3 ring D D' e
      (by simpa [e] using hcase)
      hsrcPre.1 hsrcPre.2
      (by simpa [j] using hrnot)
      (by simpa [j] using hbadJ)
  have hall :
      ∀ q : Fin n,
        (D' q).leader = false ∧
          (D' q).signalB = false := by
    intro q
    by_cases hqe : q = e
    · subst q
      exact ⟨hpair.1, hpair.2.1⟩
    · by_cases hqj : q = j
      · subst q
        exact ⟨hpair.2.2.1, hpair.2.2.2⟩
      · have hqpos : 1 ≤ q.val := by
          by_cases hz : q.val = 0
          · have hEq : q = j := by
              apply Fin.ext
              rw [hjval]
              exact hz
            exact False.elim (hqj hEq)
          · omega
        have hqle : q.val ≤ n - 1 := by
          omega
        have hpre :=
          hsrcTrail q hqpos hqle
        have hsame :=
          fourField_other
            ring D D' e q
            (by simpa [e] using hcase)
            hqe
            (by simpa [j] using hqj)
        rw [hsame]
        exact hpre
  have hp :=
    peaceful4_of_all_follower_signal_zero
      ring D' j
      (fun q => (hall q).1)
      (fun q => (hall q).2)
  exact hbadJ.2 hp

private theorem allLivePeaceful_of_noBad4
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (h : NoBad4 ring (project4 C)) :
    AllLivePeaceful ring C := by
  intro i hlive
  by_cases hp : PPL.Peaceful ring C i
  · exact hp
  · have hlive4 :
        (project4 C i).bullet = (2 : Fin 3) := by
      simpa [project4, PPL.Elim.viewConfig,
        PPL.Elim.view4] using hlive
    have hnot4 :
        ¬ Peaceful4 ring (project4 C) i := by
      intro hp4
      apply hp
      simpa [Peaceful4, project4,
        PPL.Elim.viewConfig, PPL.Elim.view4,
        PPL.Peaceful] using hp4
    exact False.elim
      (h i ⟨hlive4, hnot4⟩)

/-- Once every live bullet is peaceful, the R6 one-step facts show that
arbitrary later P_PL steps cannot create a nonpeaceful live bullet. -/
theorem allLivePeaceful_step
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e : Fin n)
    (hC : AllLivePeaceful ring C) :
    AllLivePeaceful ring (step ring C e) := by
  let C' := step ring C e
  have hnew : PPL.NewFirePeacefulProp :=
    PPL.Safety.PeacefulProps.newFirePeaceful
      PPL.Safety.PeacefulProps.peacefulScanLocality
  have hkeep : PPL.PeacefulKeepPhysicalProp :=
    PPL.Safety.PeacefulProps.peacefulKeepPhysical
      PPL.Safety.PeacefulProps.peacefulScanLocality
  intro i hi
  by_cases hold :
      (C i).bullet = (2 : Fin 3)
  · exact
      (hkeep hn3 hpsi ring C e i
        hold (hC i hold)).1
        (by simpa [C', step] using hi)
  · by_cases hir :
        i = ring.rightNeighbor e
    · subst i
      by_cases hleft :
          (C e).bullet = (2 : Fin 3)
      · exact
          (hkeep hn3 hpsi ring C e e
            hleft (hC e hleft)).2
            rfl
            (by simpa [C', step] using hi)
            hold
      · exact
          hnew hn3 hpsi ring C e
            (ring.rightNeighbor e)
            (by simpa [C', step] using hi)
            hold (Or.inr hleft)
    · exact
        hnew hn3 hpsi ring C e i
          (by simpa [C', step] using hi)
          hold (Or.inl hir)

/-- The paper word has literal length 2n. -/
theorem lemma15SweepWord_length
    {n : Nat} (ring : DirectedRing n) :
    (lemma15SweepWord ring).length = 2 * n := by
  simp [lemma15SweepWord, PPL.seqR]
  omega

/-- Deterministic Lemma-15 forcing execution.

No condition is placed on the initial bullets, shields, signalB bits, leaders,
tokens, clocks, or modes.  The proof runs the exact full P_PL transition.
After the first clockwise sweep every still-bad live bullet is at physical
site 0.  During the second sweep a still-bad bullet must move at every
scheduled edge; line 60 clears each destination.  If it survived the final
wrap as bad, every site would be a follower with signalB=false, which makes
that bullet peaceful, contradiction. -/
theorem lemma15_forcingWord
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa) :
    AllLivePeaceful ring
      (run ring C (lemma15SweepWord ring)) := by
  let z := zeroSite ring
  let C1 :=
    run ring C (PPL.seqR ring z n)
  have hfirst :
      ∀ i : Fin n,
        BadLive4 ring (project4 C1) i →
          i.val = 0 := by
    intro i hbad
    simpa [C1, z] using
      (firstSweep_bad_only_zero
        hn3 hpsi ring C i hbad)
  have hfront0 :
      BadFront ring 0 (project4 C1) := by
    constructor
    · exact hfirst
    · intro i hbad q hq1 hq0
      omega
  let Cpre :=
    run ring C1
      (PPL.seqR ring z (n - 1))
  have hfrontPre :
      BadFront ring (n - 1) (project4 Cpre) := by
    have h :=
      badFront_secondSweep
        hn3 hpsi ring C1 hfront0
        (n - 1) (by omega)
    simpa [Cpre, z] using h
  let e := edgeAt ring (n - 1)
  let C2 := step ring Cpre e
  have hcase :
      FourFieldStepCase ring
        (project4 Cpre) (project4 C2) e := by
    simpa [C2, e] using
      (project_step_case
        hn3 hpsi ring Cpre (edgeAt ring (n - 1)))
  have hnobad :
      NoBad4 ring (project4 C2) := by
    exact
      last_edge_no_bad
        hn3 ring
        (project4 Cpre) (project4 C2)
        (by simpa [e] using hcase)
        hfrontPre
  have hgood2 :
      AllLivePeaceful ring C2 :=
    allLivePeaceful_of_noBad4 ring C2 hnobad
  have hsecond :
      run ring C1
          (PPL.seqR ring z n) =
        C2 := by
    have hn :
        (n - 1) + 1 = n :=
      Nat.sub_add_cancel (by omega)
    have hseq :
        PPL.seqR ring z ((n - 1) + 1) =
          PPL.seqR ring z n :=
      congrArg (fun m => PPL.seqR ring z m) hn
    rw [← hseq]
    simpa [Cpre, C2, e, z] using
      (run_seqR_succ_local
        ring C1 (n - 1))
  have hwhole :
      run ring C (lemma15SweepWord ring) =
        run ring C1
          (PPL.seqR ring z n) := by
    simpa [lemma15SweepWord, C1, z] using
      (run_append_local
        ring C
        (PPL.seqR ring (zeroSite ring) n)
        (PPL.seqR ring (zeroSite ring) n))
  rw [hwhole, hsecond]
  exact hgood2

/-- Semantic endpoint-failure numerator at the frozen Lemma-15 horizon. -/
def lemma15FailureCount
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) : Nat :=
  (allSchedules n (lemma15Horizon n)).countP
    (fun word =>
      decide
        (¬ AllLivePeaceful ring
          (run ring C word)))

/-- Frozen finite-word headline.

This is deliberately a named Prop on current main.  The only absent bridge is
the identity-sensitive statement that ordered-subsequence occurrence of the
two-sweep word, with arbitrary interleaving scheduler letters, eliminates or
peacefully retires every initial bad-live lineage.  FixedWord counts exactly
that ordered-subsequence event, whereas lemma15_forcingWord above is the exact
literal execution. -/
def Lemma15FiniteWordBound : Prop :=
  ∀ {n psi kappa : Nat}
      (hn3 : 3 ≤ n)
      (hpsi : 2 ≤ psi)
      (ring : DirectedRing n)
      (C : Config n psi kappa),
    n * lemma15FailureCount ring C ≤
      c15 * n ^ lemma15Horizon n

/-- The repository's Lemma-1 asset gives the desired one-over-n budget for
missing the two-sweep ordered word.  This proves that c15=1 is sufficient once
the semantic failure event is dominated by the fixed-word miss event. -/
theorem lemma15_fixedWordMiss_one_over_n
    {n : Nat}
    (hn3 : 3 ≤ n)
    (ring : DirectedRing n) :
    n *
        fixedWordMissCount
          (lemma15SweepWord ring)
          (lemma15Horizon n) ≤
      n ^ lemma15Horizon n := by
  let K4 := 4 * lemma15K n
  have hscaled :
      fixedWordMissCount
            (lemma15SweepWord ring)
            (lemma15Horizon n) *
          2 ^ K4 ≤
        n ^ lemma15Horizon n := by
    have h :=
      fixedWordMissCount_mul_twoPow_le_of_length
        (lemma15SweepWord ring)
        (2 * n) K4
        (lemma15SweepWord_length ring)
    simpa [lemma15Horizon, K4] using h
  have hnK :
      n ≤ 2 ^ lemma15K n := by
    have h :=
      (LeaderCountDyadicTail.log_parameters
        n (by omega)).2.2.2
    simpa [lemma15K] using h
  have hpow :
      2 ^ lemma15K n ≤ 2 ^ K4 := by
    apply Nat.pow_le_pow_right
    · decide
    · dsimp [K4]
      omega
  have hnK4 :
      n ≤ 2 ^ K4 :=
    Nat.le_trans hnK hpow
  calc
    n *
        fixedWordMissCount
          (lemma15SweepWord ring)
          (lemma15Horizon n) ≤
      2 ^ K4 *
        fixedWordMissCount
          (lemma15SweepWord ring)
          (lemma15Horizon n) :=
      Nat.mul_le_mul_right _ hnK4
    _ =
      fixedWordMissCount
          (lemma15SweepWord ring)
          (lemma15Horizon n) *
        2 ^ K4 := by
      ac_rfl
    _ ≤ n ^ lemma15Horizon n :=
      hscaled

/-- Exact final arithmetic reduction.  A future bullet-lineage/subsequence
theorem only has to provide hdom; no further probability argument remains. -/
theorem lemma15FiniteWordBound_of_miss_domination
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (hdom :
      lemma15FailureCount ring C ≤
        fixedWordMissCount
          (lemma15SweepWord ring)
          (lemma15Horizon n)) :
    n * lemma15FailureCount ring C ≤
      c15 * n ^ lemma15Horizon n := by
  unfold c15
  simp only [Nat.one_mul]
  calc
    n * lemma15FailureCount ring C ≤
        n *
          fixedWordMissCount
            (lemma15SweepWord ring)
            (lemma15Horizon n) :=
      Nat.mul_le_mul_left n hdom
    _ ≤ n ^ lemma15Horizon n :=
      lemma15_fixedWordMiss_one_over_n
        hn3 ring

/-! ## Ordered-subsequence semantic bridge

The exact execution theorem above is not yet enough for the fixed-word
probability wrapper: FixedWord counts ordered-subsequence occurrence, so
arbitrary scheduler letters may be interleaved between the selected sweep
edges.

A direct identity proof would use a proof-only bullet tag, analogous to
PPL.Modes.SignalLineage.SignalTag: initial live bullets receive stable tags,
line-59 movement transfers the tag to the responder, absorption/collision
terminates it, and fresh firings receive new tags.  No cloning is needed.

The obvious identity-free scalar potentials are insufficient here.
The number of nonpeaceful live bullets is only nonincreasing, not strictly
decreasing when a bad bullet moves.  A cyclic position/distance potential
wraps at edge n-1, and the exact second-sweep ClearedThrough certificate is
not invariant under arbitrary gaps because an unrelated Algorithm-5 line-62
interaction can write signalB=true again at a previously swept initiator.
A successful potential therefore has to remember, for each surviving bad
descendant, how much clockwise traversal/cleared arc it has accumulated;
that is essentially the same historical information as a bullet lineage.
Accordingly this file states the required sublist theorem as one precise Prop
rather than claiming an unproved potential argument.
-/

/-- Ordered-subsequence form of paper Lemma 15.

Equivalently, every nonpeaceful live bullet present at the beginning is
absorbed or has become peaceful by the time the selected two-sweep word has
occurred; new live bullets and descendants of already-peaceful bullets cannot
supply a counterexample by allLivePeaceful_step / the R6 new-fire and keep
theorems.  The endpoint form is identity-free and is exactly what the
finite-word failure count needs. -/
def Lemma15SublistSweep : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (schedule : DetSchedule n),
    (lemma15SweepWord ring).Sublist schedule →
      AllLivePeaceful ring (run ring C schedule)


end PPL.Convergence.BulletSweep

#print axioms PPL.Convergence.BulletSweep.allLivePeaceful_step
#print axioms PPL.Convergence.BulletSweep.lemma15SweepWord_length
#print axioms PPL.Convergence.BulletSweep.lemma15_forcingWord
#print axioms PPL.Convergence.BulletSweep.lemma15_fixedWordMiss_one_over_n
#print axioms PPL.Convergence.BulletSweep.lemma15FiniteWordBound_of_miss_domination


#check PPL.Convergence.BulletSweep.Lemma15SublistSweep

