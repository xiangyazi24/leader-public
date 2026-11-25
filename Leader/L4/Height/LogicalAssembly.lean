import Leader.L4.Height.LogicalA
import Leader.L4.Height.LogicalVec
import Leader.L4.Height.LogicalBAlt

namespace L4.Height

open Classical
open L4.Height.Couple
open L4.Compiler.Native

set_option maxRecDepth 8192
set_option maxHeartbeats 30000000

theorem phaseIndex_value {Q m : Nat} (r : Fin Q) (i : Fin m) :
    (phaseIndex r i).val = r.val * m + i.val := rfl

theorem phaseIndex_surjective {Q m : Nat} (hm : 0 < m)
    (k : Fin (Q * m)) :
    ∃ r : Fin Q, ∃ i : Fin m, phaseIndex r i = k := by
  let r : Fin Q :=
    ⟨k.val / m,
      Nat.div_lt_of_lt_mul
        (Nat.lt_of_lt_of_eq k.isLt (Nat.mul_comm Q m))⟩
  let i : Fin m := ⟨k.val % m, Nat.mod_lt _ hm⟩
  refine ⟨r, i, ?_⟩
  apply Fin.ext
  change r.val * m + i.val = k.val
  dsimp [r, i]
  calc
    (k.val / m) * m + k.val % m =
        m * (k.val / m) + k.val % m := by rw [Nat.mul_comm]
    _ = k.val := Nat.div_add_mod k.val m

private theorem roundBits_length (m : Nat)
    (choices : Nat → Fin m → Bool) (ellzero : Nat) :
    ∀ k, (roundBits choices ellzero k).length = k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [roundBits_succ]
      simp [ih]

private theorem roundBits_getElem (m : Nat)
    (choices : Nat → Fin m → Bool) (ellzero : Nat) :
    ∀ {Q r : Nat} (hr : r < Q),
      (roundBits choices ellzero Q)[r]'(by
        have hlen := roundBits_length m choices ellzero Q
        simpa only [hlen] using hr) =
        choices (ellzero + 32 * r + 1) := by
  intro Q
  induction Q with
  | zero =>
      intro r hr
      omega
  | succ Q ih =>
      intro r hr
      simp only [roundBits_succ]
      by_cases hlt : r < Q
      · have hprefix : r < (roundBits choices ellzero Q).length := by
          have hlen := roundBits_length m choices ellzero Q
          simpa only [hlen] using hlt
        rw [List.getElem_append_left hprefix]
        exact ih hlt
      · have heq : r = Q := by omega
        subst r
        simp [roundBits_length]

/-- The recursive list of phase choices is the list of read-vector
blocks. The phase index and LogicalVec's block index have the same
flattened value r*m+i. This equality does not need coverage:
physicalChoices_target identifies each phase bit with readVector. -/
theorem roundBits_readVector {m Q : Nat}
    (B M ellzero : Nat) (hm : 0 < m)
    (s0 : WordState m) (u : List (Fin (2 * m))) :
    roundBits (physicalChoices B M ellzero Q hm s0 u) ellzero Q =
      vecRounds Q m
        (Couple.readVector (physSource B M ellzero Q hm) s0 u) := by
  apply List.ext_getElem
  · simp [roundBits_length, vecRounds]
  · intro r hleft hright
    have hr : r < Q := by
      simpa [vecRounds_length] using hright
    have hround :
        (roundBits (physicalChoices B M ellzero Q hm s0 u)
          ellzero Q)[r]'(by
            have hlen := roundBits_length m
              (physicalChoices B M ellzero Q hm s0 u) ellzero Q
            simpa only [hlen] using hr) =
          physicalChoices B M ellzero Q hm s0 u
            (ellzero + 32 * r + 1) :=
      roundBits_getElem m _ ellzero hr
    rw [hround]
    simp only [vecRounds, List.getElem_ofFn]
    apply funext
    intro i
    let rf : Fin Q := ⟨r, hr⟩
    change
      physicalChoices B M ellzero Q hm s0 u
          (ellzero + 32 * rf.val + 1) i =
        Couple.readVector (physSource B M ellzero Q hm) s0 u
          (phaseIndex rf i)
    rw [physicalChoices_target]

private theorem nodup_filter_bool {α : Type}
    (xs : List α) (p : α → Bool) (hxs : xs.Nodup) :
    (xs.filter p).Nodup := by
  induction xs with
  | nil => simp
  | cons a as ih =>
      have hcons := List.nodup_cons.mp hxs
      simp only [List.filter_cons]
      cases hp : p a with
      | false => exact ih hcons.2
      | true =>
          apply List.nodup_cons.mpr
          constructor
          · intro ha
            exact hcons.1 (List.mem_filter.mp ha).1
          · exact ih hcons.2

/-- The quarter bound transferred to the physical paired alphabet.
The logical bad vectors are exactly the filter of allVectors by the
failure of the synchronous anchor-count condition. -/
theorem logical_physical_quarter
    {m B : Nat} (hm : 0 < m) (hmb : m < B)
    (start : Fin m → L4.Compiler.Native.Snapshot)
    (hs : Bounded B start)
    (M ellzero : Nat) (s0 : WordState m)
    (t : Nat) (E : List (Fin (2 * m)) → Prop)
    [DecidablePred E]
    (hlogical : ∀ u, u.length = t → E u →
      (∀ k, Couple.firstReveal
        (physSource B M ellzero (2 ^ 19 * m) hm) k s0 u ≠ none) ∧
      anchorCount hm
        (runRounds B hm
          (vecRounds (2 ^ 19 * m) m
            (Couple.readVector
              (physSource B M ellzero (2 ^ 19 * m) hm) s0 u))
          start) ≠ 1) :
    4 * wordSum (fun u => if E u then 1 else 0) t ≤ (2 * m) ^ t := by
  let Q := 2 ^ 19 * m
  let S : Couple.PairedSource (WordState m) (Fin (Q * m)) (2 * m) :=
    physSource B M ellzero Q hm
  let F : (Fin (Q * m) → Bool) → Prop :=
    fun a => anchorCount hm
      (runRounds B hm (vecRounds Q m a) start) ≠ 1
  let bad : List (Fin (Q * m) → Bool) :=
    (allVectors (Q * m)).filter (fun a => decide (F a))
  have hbadDistinct : bad.Nodup := by
    change ((allVectors (Q * m)).filter (fun a => decide (F a))).Nodup
    exact nodup_filter_bool (allVectors (Q * m))
      (fun a => decide (F a)) (allVectors_nodup (Q * m))
  have hbad : ∀ a, a ∈ bad ↔ F a := by
    intro a
    change a ∈
        (allVectors (Q * m)).filter (fun b => decide (F b)) ↔ F a
    rw [List.mem_filter]
    constructor
    · rintro ⟨_, ha⟩
      exact of_decide_eq_true ha
    · intro ha
      exact ⟨mem_allVectors a, decide_eq_true ha⟩
  have hquarter : 4 * bad.length ≤ 2 ^ (Q * m) := by
    change 4 *
        ((allVectors (Q * m)).filter (fun a => decide (F a))).length
        ≤ 2 ^ (Q * m)
    simpa [F, Q] using logical_quarter_vectors hm hmb start hs
  have hlogical' : ∀ u, u.length = t → E u →
      (∀ k, Couple.firstReveal S k s0 u ≠ none) ∧
      F (Couple.readVector S s0 u) := by
    intro u hu he
    have hp := hlogical u hu he
    constructor
    · exact hp.1
    · simpa [F, S, Q] using hp.2
  have htransfer := adaptive_quarter_transfer_partial
    S s0 t E F bad hbadDistinct hbad hquarter hlogical'
  have hsum :
      wordSum (fun u => if E u then 1 else 0) t =
      wordSum
        (fun u => @ite Nat (E u)
          (Classical.propDecidable (E u)) 1 0) t := by
    apply wordSum_congr
    intro u
    by_cases he : E u <;> simp [he]
  rw [hsum]
  exact htransfer

/-- The existential observed-snapshot event. Each word may have its own
observed snapshot, which must be its actual level-current readout. -/
theorem logical_physical_event_exists
    {m B : Nat} (hm : 0 < m) (hmb : m < B)
    (start : Fin m → L4.Compiler.Native.Snapshot)
    (hs : Bounded B start)
    (M ellzero : Nat) (s0 : WordState m)
    (hM : ClockParams M)
    (hdiv : 32 ∣ M / 2) (hzero : ellzero % 32 = 0)
    (hleg : Legit M hm s0)
    (t : Nat) :
    4 * wordSum
      (fun u =>
        if
          StartConsistent B M ellzero hm
            (physicalChoices B M ellzero (2 ^ 19 * m) hm s0 u)
            start s0 ∧
          (∀ i, (physicalRun B M hm s0 u).lift i =
            ellzero + 32 * (2 ^ 19 * m)) ∧
          (∃ observed : Fin m → L4.Compiler.Native.Snapshot,
            (∀ i, levelCurr B M hm (u.map physicalActivation)
              s0 i (ellzero + 32 * (2 ^ 19 * m)) =
                some (observed i)) ∧
            anchorCount hm observed ≠ 1)
        then 1 else 0)
      t ≤ (2 * m) ^ t := by
  let E : List (Fin (2 * m)) → Prop :=
    fun u =>
      StartConsistent B M ellzero hm
        (physicalChoices B M ellzero (2 ^ 19 * m) hm s0 u)
        start s0 ∧
      (∀ i, (physicalRun B M hm s0 u).lift i =
        ellzero + 32 * (2 ^ 19 * m)) ∧
      (∃ observed : Fin m → L4.Compiler.Native.Snapshot,
        (∀ i, levelCurr B M hm (u.map physicalActivation)
          s0 i (ellzero + 32 * (2 ^ 19 * m)) =
            some (observed i)) ∧
        anchorCount hm observed ≠ 1)
  have hlogical : ∀ u, u.length = t → E u →
      (∀ k, Couple.firstReveal
        (physSource B M ellzero (2 ^ 19 * m) hm) k s0 u ≠ none) ∧
      anchorCount hm
        (runRounds B hm
          (vecRounds (2 ^ 19 * m) m
            (Couple.readVector
              (physSource B M ellzero (2 ^ 19 * m) hm) s0 u))
          start) ≠ 1 := by
    intro u hu he
    rcases he with ⟨hstart, hfinish, hexists⟩
    rcases hexists with ⟨observed, hobserved, hbad⟩
    have hsnap := physical_snapshot_eq
      B M ellzero (2 ^ 19 * m) hm hM hdiv hzero
      start s0 u hleg hstart hfinish
    constructor
    · intro k
      obtain ⟨r, i, hki⟩ :=
        phaseIndex_surjective (Q := 2 ^ 19 * m) hm k
      subst k
      rcases hsnap.2 r i with ⟨v, hv⟩
      simp [hv]
    · have hround :
        ∀ i, observed i =
          runRounds B hm
            (vecRounds (2 ^ 19 * m) m
              (Couple.readVector
                (physSource B M ellzero (2 ^ 19 * m) hm) s0 u))
            start i := by
        intro i
        have h1 := hsnap.1 i
        rw [roundBits_readVector B M ellzero hm s0 u] at h1
        have h2 := hobserved i
        exact Option.some.inj (h2.symm.trans h1)
      have hfun :
        observed =
          runRounds B hm
            (vecRounds (2 ^ 19 * m) m
              (Couple.readVector
                (physSource B M ellzero (2 ^ 19 * m) hm) s0 u))
            start := by
        funext i
        exact hround i
      simpa [hfun] using hbad
  have hbound :=
    logical_physical_quarter hm hmb start hs M ellzero s0 t E hlogical
  change
    4 * wordSum
      (fun u =>
        if
          StartConsistent B M ellzero hm
            (physicalChoices B M ellzero (2 ^ 19 * m) hm s0 u)
            start s0 ∧
          (∀ i, (physicalRun B M hm s0 u).lift i =
            ellzero + 32 * (2 ^ 19 * m)) ∧
          (∃ observed : Fin m → L4.Compiler.Native.Snapshot,
            (∀ i, levelCurr B M hm (u.map physicalActivation)
              s0 i (ellzero + 32 * (2 ^ 19 * m)) =
                some (observed i)) ∧
            anchorCount hm observed ≠ 1)
        then 1 else 0)
      t ≤ (2 * m) ^ t
  exact hbound

/-- The physical event version. The observed level snapshot is represented
by a total site-indexed Native snapshot function; the premise states that
the level-current readout at the completed clock is exactly that function. -/
theorem logical_physical_event
    {m B : Nat} (hm : 0 < m) (hmb : m < B)
    (start : Fin m → L4.Compiler.Native.Snapshot)
    (hs : Bounded B start)
    (M ellzero : Nat) (s0 : WordState m)
    (hM : ClockParams M)
    (hdiv : 32 ∣ M / 2) (hzero : ellzero % 32 = 0)
    (hleg : Legit M hm s0)
    (observed : Fin m → L4.Compiler.Native.Snapshot)
    (t : Nat) :
    4 * wordSum
      (fun u =>
        if
          StartConsistent B M ellzero hm
            (physicalChoices B M ellzero (2 ^ 19 * m) hm s0 u)
            start s0 ∧
          (∀ i, (physicalRun B M hm s0 u).lift i =
            ellzero + 32 * (2 ^ 19 * m)) ∧
          (∀ i, levelCurr B M hm (u.map physicalActivation)
            s0 i (ellzero + 32 * (2 ^ 19 * m)) =
              some (observed i)) ∧
          anchorCount hm observed ≠ 1
        then 1 else 0)
      t ≤ (2 * m) ^ t := by
  have hlogical : ∀ u, u.length = t →
      StartConsistent B M ellzero hm
        (physicalChoices B M ellzero (2 ^ 19 * m) hm s0 u)
        start s0 ∧
      (∀ i, (physicalRun B M hm s0 u).lift i =
        ellzero + 32 * (2 ^ 19 * m)) ∧
      (∀ i, levelCurr B M hm (u.map physicalActivation)
        s0 i (ellzero + 32 * (2 ^ 19 * m)) =
          some (observed i)) ∧
      anchorCount hm observed ≠ 1 →
      (∀ k, Couple.firstReveal
        (physSource B M ellzero (2 ^ 19 * m) hm) k s0 u ≠ none) ∧
      anchorCount hm
        (runRounds B hm
          (vecRounds (2 ^ 19 * m) m
            (Couple.readVector
              (physSource B M ellzero (2 ^ 19 * m) hm) s0 u))
          start) ≠ 1 := by
    intro u hu he
    rcases he with ⟨hstart, hfinish, hobserved, hbad⟩
    have hsnap := physical_snapshot_eq
      B M ellzero (2 ^ 19 * m) hm hM hdiv hzero
      start s0 u hleg hstart hfinish
    constructor
    · intro k
      obtain ⟨r, i, hki⟩ :=
        phaseIndex_surjective (Q := 2 ^ 19 * m) hm k
      subst k
      rcases hsnap.2 r i with ⟨v, hv⟩
      simp [hv]
    · have hround :
        ∀ i, observed i =
          runRounds B hm
            (vecRounds (2 ^ 19 * m) m
              (Couple.readVector
                (physSource B M ellzero (2 ^ 19 * m) hm) s0 u))
            start i := by
        intro i
        have h1 := hsnap.1 i
        rw [roundBits_readVector B M ellzero hm s0 u] at h1
        have h2 := hobserved i
        exact Option.some.inj (h2.symm.trans h1)
      have hfun :
        observed =
          runRounds B hm
            (vecRounds (2 ^ 19 * m) m
              (Couple.readVector
                (physSource B M ellzero (2 ^ 19 * m) hm) s0 u))
            start := by
        funext i
        exact hround i
      simpa [hfun] using hbad
  have hbound :=
    logical_physical_quarter hm hmb start hs M ellzero s0 t
      (fun u =>
        StartConsistent B M ellzero hm
          (physicalChoices B M ellzero (2 ^ 19 * m) hm s0 u)
          start s0 ∧
        (∀ i, (physicalRun B M hm s0 u).lift i =
          ellzero + 32 * (2 ^ 19 * m)) ∧
        (∀ i, levelCurr B M hm (u.map physicalActivation)
          s0 i (ellzero + 32 * (2 ^ 19 * m)) =
            some (observed i)) ∧
        anchorCount hm observed ≠ 1)
      hlogical
  exact hbound

end L4.Height

