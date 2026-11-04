import Leader.AAFJ.OneBarrier.TwoHitBullet


set_option autoImplicit false


namespace AAFJPK.OriginalOneBarrierSweep


open BarrierAlgebra
open SingleBarrierSanitation
open OriginalNonbarrierWord
open TwoHitBullet


private theorem nonbarrier_bullet_leader_fields
    {k : Nat} (hk : 0 < k) (u v : State k)
    (hnb : ¬ IsBarrier hk u v) (hbullet : v.bullet = true) :
    (transition hk u v).1.leader = u.leader ∧
      (transition hk u v).2.leader = false := by
  rw [transition_of_nonbarrier hk u v hnb]
  cases hv : v.leader <;> cases hp : u.probe <;>
    simp [nonBarrierStep, hv, hbullet, hp]


private theorem nonbarrier_follower_leader_fields
    {k : Nat} (hk : 0 < k) (u v : State k)
    (hnb : ¬ IsBarrier hk u v) (hleader : v.leader = false) :
    (transition hk u v).1.leader = u.leader ∧
      (transition hk u v).2.leader = false := by
  rw [transition_of_nonbarrier hk u v hnb]
  cases hb : v.bullet <;> cases hp : u.probe <;>
    simp [nonBarrierStep, hleader, hb, hp]


/-- A two-hit bullet transfer kills the responder leader, if any, and never
changes the initiator leader bit. -/
theorem doubleHit_kills
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (C : Fin n → State k) (b p : Fin n)
    (hB : OneBarrierAt hk ring C b)
    (hbullet : (C p).bullet = true)
    (hpos : 0 < (cutCoord ring b p).val) :
    let e := ring.leftNeighbor p
    let D := rawRun hk ring C [e, e]
    (D p).leader = false ∧ (D e).leader = (C e).leader := by
  let e := ring.leftNeighbor p
  let C1 := (protocol k hk).step ring C e
  let D := (protocol k hk).step ring C1 e
  have hword : CurrentNonbarrierWord hk ring C [e, e] := by
    have hf := twoHit_fields hk ring hn3 C b p hB hbullet hpos
    dsimp only at hf
    simpa [e] using hf.1
  have hw := hword
  simp only [CurrentNonbarrierWord] at hw
  rcases hw with ⟨hnb0, hnb1, _⟩
  have her : ring.rightNeighbor e = p := by
    simpa [e] using rightNeighbor_leftNeighbor_clean ring p
  have hn2 : 1 < n := by omega
  have hep : e ≠ p := by
    intro h
    have hself := BarrierAlgebra.rightNeighbor_ne_self ring hn2 e
    exact hself (her.trans h.symm)
  have hnb0' : ¬ IsBarrier hk (C e) (C p) := by
    simpa [her] using hnb0
  have hlocal0 :=
    nonbarrier_bullet_leader_fields hk (C e) (C p) hnb0' hbullet
  have hp1 : (C1 p).leader = false := by
    simpa [C1, PopulationProtocol.step, protocol, her, hep.symm] using
      hlocal0.2
  have he1 : (C1 e).leader = (C e).leader := by
    simpa [C1, PopulationProtocol.step, protocol, her] using hlocal0.1
  have hnb1' : ¬ IsBarrier hk (C1 e) (C1 p) := by
    simpa [C1, her] using hnb1
  have hlocal1 :=
    nonbarrier_follower_leader_fields hk (C1 e) (C1 p) hnb1' hp1
  have hpD : (D p).leader = false := by
    simpa [D, PopulationProtocol.step, protocol, her, hep.symm] using
      hlocal1.2
  have heD : (D e).leader = (C e).leader := by
    calc
      (D e).leader = (C1 e).leader := by
        simpa [D, PopulationProtocol.step, protocol, her] using hlocal1.1
      _ = (C e).leader := he1
  change (D p).leader = false ∧ (D e).leader = (C e).leader
  exact ⟨hpD, heD⟩


/-- Double-hit the bullet site at cut coordinate m, then m-1, and so on,
stopping just before coordinate zero.  On an out-of-range input the word is
empty; the sweep theorems only use m < n. -/
def sweepWord {n : Nat} (ring : DirectedRing n) (b : Fin n) :
    Nat → List (Fin n)
  | 0 => []
  | m + 1 =>
      if h : m + 1 < n then
        let p := cutPos ring b (⟨m + 1, h⟩ : Fin n)
        let e := ring.leftNeighbor p
        e :: e :: sweepWord ring b m
      else
        []


private theorem sweepWord_succ_of_lt
    {n : Nat} (ring : DirectedRing n) (b : Fin n)
    (m : Nat) (hm : m + 1 < n) :
    sweepWord ring b (m + 1) =
      let p := cutPos ring b (⟨m + 1, hm⟩ : Fin n)
      let e := ring.leftNeighbor p
      e :: e :: sweepWord ring b m := by
  simp [sweepWord, hm]


private theorem eq_cutPos_of_cutCoord_val_eq
    {n : Nat} (ring : DirectedRing n) (b i j : Fin n)
    (h : (cutCoord ring b i).val = j.val) :
    i = cutPos ring b j := by
  have hc : cutCoord ring b i = j := by
    apply Fin.ext
    exact h
  calc
    i = cutPos ring b (cutCoord ring b i) :=
      (cutPos_cutCoord ring b i).symm
    _ = cutPos ring b j := by rw [hc]


private theorem leftNeighbor_cutPos_succ
    {n : Nat} (ring : DirectedRing n) (b : Fin n)
    (m : Nat) (hm : m + 1 < n) :
    ring.leftNeighbor
        (cutPos ring b (⟨m + 1, hm⟩ : Fin n)) =
      cutPos ring b (⟨m, by omega⟩ : Fin n) := by
  let p := cutPos ring b (⟨m + 1, hm⟩ : Fin n)
  have hpval : (cutCoord ring b p).val = m + 1 := by
    simp [p]
  have hpos : 0 < (cutCoord ring b p).val := by
    omega
  have hdec := cutCoord_leftNeighbor_of_pos ring b p hpos
  have heval :
      (cutCoord ring b (ring.leftNeighbor p)).val = m := by
    omega
  change ring.leftNeighbor p =
    cutPos ring b (⟨m, by omega⟩ : Fin n)
  exact eq_cutPos_of_cutCoord_val_eq ring b
    (ring.leftNeighbor p) (⟨m, by omega⟩ : Fin n) heval


private theorem sweep_spec_aux
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (b : Fin n) :
    ∀ (m : Nat) (C : Fin n → State k) (hm : m < n),
      OneBarrierAt hk ring C b →
      (C (cutPos ring b (⟨m, hm⟩ : Fin n))).bullet = true →
      let D := rawRun hk ring C (sweepWord ring b m)
      CurrentNonbarrierWord hk ring C (sweepWord ring b m) ∧
        OneBarrierAt hk ring D b ∧
        (∀ i : Fin n,
          1 ≤ (cutCoord ring b i).val →
          (cutCoord ring b i).val ≤ m →
          (D i).leader = false) ∧
        (∀ i : Fin n,
          ((cutCoord ring b i).val = 0 ∨
            m < (cutCoord ring b i).val) →
          (D i).leader = (C i).leader) ∧
        (∀ i : Fin n,
          m < (cutCoord ring b i).val →
          D i = C i) ∧
        (D (ring.rightNeighbor b)).bullet = true := by
  intro m
  induction m with
  | zero =>
      intro C hm hB hbul
      dsimp only [sweepWord, rawRun, CurrentNonbarrierWord]
      refine ⟨True.intro, hB, ?_, ?_, ?_, ?_⟩
      · intro i hlow hhigh
        omega
      · intro i hi
        rfl
      · intro i hi
        rfl
      · simpa using hbul
  | succ m ih =>
      intro C hm hB hbul
      have hm1 : m + 1 < n := by omega
      have hm0 : m < n := by omega
      let q : Fin n := ⟨m + 1, hm1⟩
      let p := cutPos ring b q
      let e := ring.leftNeighbor p
      let r : Fin n := ⟨m, hm0⟩
      have hpval : (cutCoord ring b p).val = m + 1 := by
        simp [p, q]
      have hpos : 0 < (cutCoord ring b p).val := by
        omega
      have hbulletP : (C p).bullet = true := by
        simpa [p, q] using hbul
      have heq : e = cutPos ring b r := by
        simpa [e, p, q, r] using
          (leftNeighbor_cutPos_succ ring b m hm1)
      have heval : (cutCoord ring b e).val = m := by
        rw [heq]
        simp [r]
      have hsw :
          sweepWord ring b (m + 1) =
            e :: e :: sweepWord ring b m := by
        have hs := sweepWord_succ_of_lt ring b m hm1
        dsimp only at hs
        simpa [e, p, q] using hs
      let A := rawRun hk ring C [e, e]
      have hf := twoHit_fields hk ring hn3 C b p hB hbulletP hpos
      dsimp only at hf
      change CurrentNonbarrierWord hk ring C [e, e] ∧
        OneBarrierAt hk ring A b ∧
        (A p).bullet = false ∧
        (A e).bullet = true ∧
        (∀ i : Fin n, i ≠ e → i ≠ p → A i = C i) at hf
      rcases hf with ⟨hwordA, hBA, _, hebulletA, hframeA⟩
      have hkillA :=
        doubleHit_kills hk ring hn3 C b p hB hbulletP hpos
      dsimp only at hkillA
      change (A p).leader = false ∧
        (A e).leader = (C e).leader at hkillA
      have hbulA :
          (A (cutPos ring b r)).bullet = true := by
        rw [← heq]
        exact hebulletA
      have htail := ih A hm0 hBA hbulA
      dsimp only at htail
      let E := rawRun hk ring A (sweepWord ring b m)
      change CurrentNonbarrierWord hk ring A (sweepWord ring b m) ∧
        OneBarrierAt hk ring E b ∧
        (∀ i : Fin n,
          1 ≤ (cutCoord ring b i).val →
          (cutCoord ring b i).val ≤ m →
          (E i).leader = false) ∧
        (∀ i : Fin n,
          ((cutCoord ring b i).val = 0 ∨
            m < (cutCoord ring b i).val) →
          (E i).leader = (A i).leader) ∧
        (∀ i : Fin n,
          m < (cutCoord ring b i).val →
          E i = A i) ∧
        (E (ring.rightNeighbor b)).bullet = true at htail
      rcases htail with
        ⟨hwordTail, hBTail, hclearTail, hkeepTail, hframeTail, hheadTail⟩
      let D := rawRun hk ring C (sweepWord ring b (m + 1))
      have hDE : D = E := by
        dsimp only [D, E]
        rw [hsw]
        rfl
      have hwordFull :
          CurrentNonbarrierWord hk ring C
            (sweepWord ring b (m + 1)) := by
        rw [hsw]
        have hw := hwordA
        simp only [CurrentNonbarrierWord] at hw ⊢
        rcases hw with ⟨hnb0, hnb1, _⟩
        refine ⟨hnb0, hnb1, ?_⟩
        change CurrentNonbarrierWord hk ring A (sweepWord ring b m)
        exact hwordTail
      have hBFinal : OneBarrierAt hk ring D b := by
        rw [hDE]
        exact hBTail
      have hclearFinal :
          ∀ i : Fin n,
            1 ≤ (cutCoord ring b i).val →
            (cutCoord ring b i).val ≤ m + 1 →
            (D i).leader = false := by
        intro i hlow hhigh
        rw [hDE]
        by_cases hle : (cutCoord ring b i).val ≤ m
        · exact hclearTail i hlow hle
        · have hci : (cutCoord ring b i).val = m + 1 := by
            omega
          have hip : i = p := by
            exact eq_cutPos_of_cutCoord_val_eq ring b i q
              (by simpa [q] using hci)
          subst i
          have hmp : m < (cutCoord ring b p).val := by
            omega
          rw [hframeTail p hmp]
          exact hkillA.1
      have hkeepFinal :
          ∀ i : Fin n,
            ((cutCoord ring b i).val = 0 ∨
              m + 1 < (cutCoord ring b i).val) →
            (D i).leader = (C i).leader := by
        intro i hi
        rw [hDE]
        have htailCond :
            (cutCoord ring b i).val = 0 ∨
              m < (cutCoord ring b i).val := by
          rcases hi with hzero | hhigh
          · exact Or.inl hzero
          · exact Or.inr (by omega)
        have hEA := hkeepTail i htailCond
        calc
          (E i).leader = (A i).leader := hEA
          _ = (C i).leader := by
            have hip : i ≠ p := by
              intro hip
              subst i
              rcases hi with hzero | hhigh
              · rw [hpval] at hzero
                omega
              · rw [hpval] at hhigh
                omega
            by_cases hie : i = e
            · subst i
              exact hkillA.2
            · exact congrArg State.leader (hframeA i hie hip)
      have hframeFinal :
          ∀ i : Fin n,
            m + 1 < (cutCoord ring b i).val →
            D i = C i := by
        intro i hhigh
        rw [hDE]
        have htailFrame : E i = A i :=
          hframeTail i (by omega)
        have hie : i ≠ e := by
          intro hie
          subst i
          rw [heval] at hhigh
          omega
        have hip : i ≠ p := by
          intro hip
          subst i
          rw [hpval] at hhigh
          omega
        calc
          E i = A i := htailFrame
          _ = C i := hframeA i hie hip
      have hheadFinal :
          (D (ring.rightNeighbor b)).bullet = true := by
        rw [hDE]
        exact hheadTail
      change CurrentNonbarrierWord hk ring C
          (sweepWord ring b (m + 1)) ∧
        OneBarrierAt hk ring D b ∧
        (∀ i : Fin n,
          1 ≤ (cutCoord ring b i).val →
          (cutCoord ring b i).val ≤ m + 1 →
          (D i).leader = false) ∧
        (∀ i : Fin n,
          ((cutCoord ring b i).val = 0 ∨
            m + 1 < (cutCoord ring b i).val) →
          (D i).leader = (C i).leader) ∧
        (∀ i : Fin n,
          m + 1 < (cutCoord ring b i).val →
          D i = C i) ∧
        (D (ring.rightNeighbor b)).bullet = true
      exact ⟨hwordFull, hBFinal, hclearFinal, hkeepFinal,
        hframeFinal, hheadFinal⟩


/-- Sweeping from cut coordinate m down to one transports the bullet to the
head, kills every leader it passes, preserves the unique barrier, and leaves
the strict suffix literally unchanged. -/
theorem sweep_spec
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (C : Fin n → State k) (b : Fin n)
    (hB : OneBarrierAt hk ring C b)
    (m : Nat) (hm : m < n)
    (hbul : (C (cutPos ring b (⟨m, hm⟩ : Fin n))).bullet = true) :
    let D := rawRun hk ring C (sweepWord ring b m)
    CurrentNonbarrierWord hk ring C (sweepWord ring b m) ∧
      OneBarrierAt hk ring D b ∧
      (∀ i : Fin n,
        1 ≤ (cutCoord ring b i).val →
        (cutCoord ring b i).val ≤ m →
        (D i).leader = false) ∧
      (∀ i : Fin n,
        ((cutCoord ring b i).val = 0 ∨
          m < (cutCoord ring b i).val) →
        (D i).leader = (C i).leader) ∧
      (∀ i : Fin n,
        m < (cutCoord ring b i).val →
        D i = C i) ∧
      (D (ring.rightNeighbor b)).bullet = true := by
  exact sweep_spec_aux hk ring hn3 b m C hm hB hbul


private theorem bitCount_le_of_true_imp_local
    {n : Nat} (a b : Fin n → Bool)
    (himp : ∀ i, b i = true → a i = true) :
    bitCount b ≤ bitCount a := by
  induction n with
  | zero =>
      simp [bitCount]
  | succ n ih =>
      rw [bitCount_succ, bitCount_succ]
      have htail :
          bitCount (fun i : Fin n => b i.succ) ≤
            bitCount (fun i : Fin n => a i.succ) := by
        apply ih
        intro i hi
        exact himp i.succ hi
      have hhead :
          (if b 0 then 1 else 0) ≤
            (if a 0 then 1 else 0) := by
        cases hb : b 0 with
        | false =>
            simp [hb]
        | true =>
            have ha : a 0 = true := himp 0 hb
            simp [hb, ha]
      omega


/-- The sweep never creates a leader; consequently leader count is
nonincreasing. -/
theorem sweep_leaderCount_le
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (C : Fin n → State k) (b : Fin n)
    (hB : OneBarrierAt hk ring C b)
    (m : Nat) (hm : m < n)
    (hbul : (C (cutPos ring b (⟨m, hm⟩ : Fin n))).bullet = true) :
    let D := rawRun hk ring C (sweepWord ring b m)
    leaderCount D ≤ leaderCount C ∧
      (∀ i : Fin n, (D i).leader = true → (C i).leader = true) := by
  let D := rawRun hk ring C (sweepWord ring b m)
  have hs := sweep_spec hk ring hn3 C b hB m hm hbul
  dsimp only at hs
  change CurrentNonbarrierWord hk ring C (sweepWord ring b m) ∧
    OneBarrierAt hk ring D b ∧
    (∀ i : Fin n,
      1 ≤ (cutCoord ring b i).val →
      (cutCoord ring b i).val ≤ m →
      (D i).leader = false) ∧
    (∀ i : Fin n,
      ((cutCoord ring b i).val = 0 ∨
        m < (cutCoord ring b i).val) →
      (D i).leader = (C i).leader) ∧
    (∀ i : Fin n,
      m < (cutCoord ring b i).val →
      D i = C i) ∧
    (D (ring.rightNeighbor b)).bullet = true at hs
  rcases hs with ⟨_, _, hclear, hkeep, _, _⟩
  have hnoBirth :
      ∀ i : Fin n, (D i).leader = true → (C i).leader = true := by
    intro i hi
    by_cases hz : (cutCoord ring b i).val = 0
    · have hsame := hkeep i (Or.inl hz)
      rw [hsame] at hi
      exact hi
    · by_cases hle : (cutCoord ring b i).val ≤ m
      · have hfalse := hclear i (by omega) hle
        simp [hfalse] at hi
      · have hsame := hkeep i (Or.inr (by omega))
        rw [hsame] at hi
        exact hi
  have hcount : leaderCount D ≤ leaderCount C := by
    unfold leaderCount
    exact bitCount_le_of_true_imp_local
      (fun i => (C i).leader) (fun i => (D i).leader) hnoBirth
  change leaderCount D ≤ leaderCount C ∧
    (∀ i : Fin n, (D i).leader = true → (C i).leader = true)
  exact ⟨hcount, hnoBirth⟩


#print axioms doubleHit_kills
#print axioms sweep_spec
#print axioms sweep_leaderCount_le


end AAFJPK.OriginalOneBarrierSweep
