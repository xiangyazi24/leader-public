import Leader.L3.NativeBirth
import Leader.L3.ProbStages

/-!
# Purification for the real L3 protocol

The two-sweep certificate is compressed into a configuration-only
credit. A bad live bullet at v receives credit n + v.val if the
ordinary prefix 0,...,v consists of signal-zero followers, and v.val
otherwise. Bad successors have bad predecessors with nondecreasing
credit; selecting the predecessor's outgoing edge increases credit.

Let m be the minimum bad credit, defaulting to 2*n. The remaining
count is 2*n - m, the nominated edge is m mod n, and the scaled
potential is n * (2*n - m). This skips requests already certified by
the current configuration and needs at most the paper's 2*n requests.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

open K2ArbitraryElimination.FiniteAccounting

/-- The real step preserves P: native E, then an optional eligible birth. -/
theorem real_step_preserves_P {n q : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (C : (protocol q).Configuration n) (e : Fin n)
    (hP : P ring (nativeProjection C)) :
    P ring (nativeProjection ((protocol q).step ring C e)) := by
  obtain ⟨z, hz, hstep⟩ := native_step_eq hn ring C e
  cases z with
  | none =>
      rw [hstep]
      exact nativeE_preserves_P hn ring (nativeProjection C) e hP
  | some v =>
      have hv := hz v rfl
      rw [hstep]
      exact birth_preserves_P hn ring
        (nativeProjection C) e v hP hv.1 hv.2

namespace PurificationProof


def Cleared (x : CertNative) : Prop :=
  x.l = false ∧ x.sg = false

def ClearedPrefix {n : Nat}
    (N : Fin n → CertNative) (v : Fin n) : Prop :=
  ∀ i : Fin n, i.val ≤ v.val → Cleared (N i)

def CorePeace {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (v : Fin n) : Prop :=
  PPL.PeacefulCore ring
    (fun i => (N i).l)
    (fun i => (N i).sh)
    (fun i => (N i).sg) v

def Bad {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (v : Fin n) : Prop :=
  LiveBullet N v ∧ ¬ CorePeace ring N v

private theorem scan_first {n : Nat}
    (site : Nat → Fin n) (hit : Fin n → Bool) :
    ∀ fuel start target,
      start ≤ target →
      target < start + fuel →
      hit (site target) = true →
      (∀ j, start ≤ j → j < target →
        hit (site j) = false) →
      PPL.scanDistance site hit fuel start = some target := by
  intro fuel
  induction fuel with
  | zero =>
      intro start target hst htf hh hz
      omega
  | succ fuel ih =>
      intro start target hst htf hh hz
      by_cases he : start = target
      · subst target
        simp [PPL.scanDistance, hh]
      · have hs : start < target := by omega
        have hzero := hz start (Nat.le_refl _) hs
        have ht := ih (start + 1) target
          (by omega) (by omega) hh
          (fun j hj hjt => hz j (by omega) hjt)
        simpa [PPL.scanDistance, hzero] using ht

private theorem scan_none {n : Nat}
    (site : Nat → Fin n) (hit : Fin n → Bool)
    (hz : ∀ i : Fin n, hit i = false) :
    ∀ fuel start,
      PPL.scanDistance site hit fuel start = none := by
  intro fuel
  induction fuel with
  | zero =>
      intro start
      rfl
  | succ fuel ih =>
      intro start
      simp [PPL.scanDistance, hz, ih]

private theorem shiftLeft_val {n : Nat}
    (ring : DirectedRing n) (v : Fin n) (d : Nat)
    (hd : d ≤ v.val) :
    (PPL.shiftLeft ring v d).val = v.val - d := by
  change (v.val + n - d % n) % n = v.val - d
  have hdlt : d < n := by omega
  rw [Nat.mod_eq_of_lt hdlt]
  have he : v.val + n - d = n + (v.val - d) := by
    omega
  rw [he, Nat.add_mod_left,
    Nat.mod_eq_of_lt (by omega : v.val - d < n)]

private theorem core_of_safe_self {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (v : Fin n)
    (hl : (N v).l = true)
    (hh : (N v).sh = true)
    (hs : (N v).sg = false) :
    CorePeace ring N v := by
  have hz : PPL.shiftLeft ring v 0 = v := by
    apply Fin.ext
    simpa only [Nat.sub_zero] using
      shiftLeft_val ring v 0 (Nat.zero_le _)
  have hscan :
      PPL.dLLBy ring (fun i => (N i).l) v = some 0 := by
    unfold PPL.dLLBy
    apply scan_first (fun d => PPL.shiftLeft ring v d)
      (fun i => (N i).l) n 0 0
    · exact Nat.zero_le 0
    · have hv := v.isLt
      omega
    · simpa [hz] using hl
    · intro j hj0 hjlt
      omega
  unfold CorePeace PPL.PeacefulCore
  rw [hscan]
  constructor
  · simpa [hz] using hh
  · intro j
    have hj : j.val = 0 := by omega
    simpa [hj, hz] using hs

/-- The leaderless, globally signal-zero clause of peacefulness. -/
theorem cleared_all_core {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (v : Fin n)
    (hc : ∀ i : Fin n, Cleared (N i)) :
    CorePeace ring N v := by
  have hscan :
      PPL.dLLBy ring (fun i => (N i).l) v = none := by
    unfold PPL.dLLBy
    exact scan_none
      (fun d => PPL.shiftLeft ring v d)
      (fun i => (N i).l)
      (fun i => (hc i).1) n 0
  unfold CorePeace PPL.PeacefulCore
  rw [hscan]
  exact fun i => (hc i).2

/--
A birth anywhere in a cleared prefix ending at v makes v peaceful:
the new shielded leader is the first leader in the leftward scan.
-/
theorem birth_inside_prefix {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (v z : Fin n)
    (hzv : z.val ≤ v.val)
    (hc : ClearedPrefix N v) :
    CorePeace ring (canonicalBirth N z) v := by
  let d := v.val - z.val
  have hdv : d ≤ v.val := by
    dsimp [d]
    omega
  have hdn : d < n :=
    Nat.lt_of_le_of_lt hdv v.isLt
  have hlast : PPL.shiftLeft ring v d = z := by
    apply Fin.ext
    rw [shiftLeft_val ring v d hdv]
    dsimp [d]
    omega
  have hhead :
      (canonicalBirth N z (PPL.shiftLeft ring v d)).l = true := by
    simp [hlast, canonicalBirth, firedNative]
  have hbefore :
      ∀ j : Nat, j < d →
        (canonicalBirth N z (PPL.shiftLeft ring v j)).l =
          false := by
    intro j hj
    have hjv : j ≤ v.val := by omega
    have hval := shiftLeft_val ring v j hjv
    have hne : PPL.shiftLeft ring v j ≠ z := by
      intro he
      have hev := congrArg Fin.val he
      rw [hval] at hev
      dsimp [d] at hj
      omega
    have hcleared :=
      hc (PPL.shiftLeft ring v j) (by rw [hval]; omega)
    simpa [canonicalBirth, hne] using hcleared.1
  have hsignals :
      ∀ j : Nat, j ≤ d →
        (canonicalBirth N z (PPL.shiftLeft ring v j)).sg =
          false := by
    intro j hj
    have hjv : j ≤ v.val := by omega
    have hval := shiftLeft_val ring v j hjv
    by_cases he : PPL.shiftLeft ring v j = z
    · simp [canonicalBirth, he, firedNative]
    · have hcleared :=
        hc (PPL.shiftLeft ring v j) (by rw [hval]; omega)
      simpa [canonicalBirth, he] using hcleared.2
  have hscan :
      PPL.dLLBy ring
        (fun i => (canonicalBirth N z i).l) v = some d := by
    unfold PPL.dLLBy
    exact scan_first _ _ n 0 d
      (Nat.zero_le _) (by omega)
      hhead (fun j _ hj => hbefore j hj)
  unfold CorePeace PPL.PeacefulCore
  rw [hscan]
  constructor
  · simp [hlast, canonicalBirth, firedNative]
  · intro j
    exact hsignals j.val (by omega)

/--
Individual peacefulness survives a birth even when other bullets
are bad. Masking the other bullet fields permits use of the existing
whole-configuration canonicalBirth_preserves_P theorem.
-/
theorem birth_core {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (v z : Fin n)
    (hc : CorePeace ring N v) :
    CorePeace ring (canonicalBirth N z) v := by
  by_cases hvz : v = z
  · subst v
    exact core_of_safe_self ring (canonicalBirth N z) z
      (by simp [canonicalBirth, firedNative])
      (by simp [canonicalBirth, firedNative])
      (by simp [canonicalBirth, firedNative])
  · let M : Fin n → CertNative :=
      fun i =>
        { (N i) with
          b := if i = v then (2 : Fin 3) else 0 }
    have hPM : P ring M := by
      intro i hi
      by_cases hiv : i = v
      · subst i
        exact hc
      · simp [LiveBullet, M, hiv] at hi
    have hvLive : LiveBullet (canonicalBirth M z) v := by
      simp [LiveBullet, canonicalBirth, M, hvz]
    have hout :=
      (canonicalBirth_preserves_P ring M z hPM) v hvLive
    have hl :
        (fun i => (canonicalBirth M z i).l) =
          (fun i => (canonicalBirth N z i).l) := by
      funext i
      by_cases hiz : i = z <;>
        simp [canonicalBirth, M, hiz]
    have hh :
        (fun i => (canonicalBirth M z i).sh) =
          (fun i => (canonicalBirth N z i).sh) := by
      funext i
      by_cases hiz : i = z <;>
        simp [canonicalBirth, M, hiz]
    have hs :
        (fun i => (canonicalBirth M z i).sg) =
          (fun i => (canonicalBirth N z i).sg) := by
      funext i
      by_cases hiz : i = z <;>
        simp [canonicalBirth, M, hiz]
    change CorePeace ring (canonicalBirth M z) v at hout
    unfold CorePeace at hout ⊢
    rw [hl, hh, hs] at hout
    exact hout


private theorem fin3_cases (b : Fin 3) :
    b = (0 : Fin 3) ∨ b = (1 : Fin 3) ∨ b = (2 : Fin 3) := by
  rcases b with ⟨v, hv⟩
  rcases v with _ | _ | _ | v
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · omega

/-- Finite, exact native-row facts used by the prefix induction. -/
private theorem rowFacts (a b : CertNative) :
    (certLiteralEPair a b).1.b = (0 : Fin 3) ∧
    (Cleared b → Cleared (certLiteralEPair a b).2) ∧
    (Cleared a → Cleared b →
      Cleared (certLiteralEPair a b).1) ∧
    ((certLiteralEPair a b).2.b = (2 : Fin 3) →
      b.b ≠ (2 : Fin 3) →
      Cleared (certLiteralEPair a b).2 ∧
        (Cleared a → Cleared (certLiteralEPair a b).1)) := by
  unfold Cleared
  rcases a with ⟨al, ab, ash, asg⟩
  rcases b with ⟨bl, bb, bsh, bsg⟩
  rcases fin3_cases ab with ha | ha | ha <;>
  rcases fin3_cases bb with hb | hb | hb <;>
  rw [ha, hb] <;>
  cases al <;> cases bl <;>
  cases ash <;> cases bsh <;>
  cases asg <;> cases bsg <;>
  decide

private theorem neighbor_ne {n : Nat}
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

theorem nativeE_source_bullet_zero {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative) (e : Fin n) :
    (nativeE ring N e e).b = (0 : Fin 3) := by
  simpa [nativeE] using
    (rowFacts (N e) (N (ring.rightNeighbor e))).1

theorem nativeE_responder_cleared {n : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n)
    (N : Fin n → CertNative) (e : Fin n)
    (hclear : Cleared (N (ring.rightNeighbor e))) :
    Cleared (nativeE ring N e (ring.rightNeighbor e)) := by
  have hne := neighbor_ne hn ring e
  simpa [nativeE, hne] using
    (rowFacts (N e) (N (ring.rightNeighbor e))).2.1 hclear

theorem nativeE_source_cleared_of_pair {n : Nat}
    (ring : DirectedRing n)
    (N : Fin n → CertNative) (e : Fin n)
    (hx : Cleared (N e))
    (hy : Cleared (N (ring.rightNeighbor e))) :
    Cleared (nativeE ring N e e) := by
  simpa [nativeE] using
    (rowFacts (N e) (N (ring.rightNeighbor e))).2.2.1 hx hy

private def toCell (a : CertNative) : PPL.Elim.Cell4 :=
  { leader := a.l
    bullet := a.b
    shield := a.sh
    signalB := a.sg }

private def cells {n : Nat}
    (N : Fin n → CertNative) : Fin n → PPL.Elim.Cell4 :=
  fun i => toCell (N i)

/-- Kernel finite-case equality with the existing pure-E row. -/
private theorem rowBridge (a b : CertNative) :
    (toCell (certLiteralEPair a b).1,
      toCell (certLiteralEPair a b).2) =
        PPL.Elim.rowE (toCell a) (toCell b) := by
  rcases a with ⟨al, ab, ash, asg⟩
  rcases b with ⟨bl, bb, bsh, bsg⟩
  rcases fin3_cases ab with ha | ha | ha <;>
  rcases fin3_cases bb with hb | hb | hb <;>
  rw [ha, hb] <;>
  cases al <;> cases bl <;>
  cases ash <;> cases bsh <;>
  cases asg <;> cases bsg <;>
  decide

private theorem cellsCase {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (N : Fin n → CertNative) (e : Fin n) :
    PPL.Safety.PeacefulProps.FourFieldStepCase ring
      (cells N) (cells (nativeE ring N e)) e := by
  unfold PPL.Safety.PeacefulProps.FourFieldStepCase
  dsimp only
  constructor
  · intro k hke hkj
    simp [cells, nativeE, hke, hkj]
  · left
    constructor
    · simpa [cells, nativeE] using
        congrArg Prod.fst
          (rowBridge (N e) (N (ring.rightNeighbor e)))
    · have hne := neighbor_ne (by omega : 2 ≤ n) ring e
      simpa [cells, nativeE, hne] using
        congrArg Prod.snd
          (rowBridge (N e) (N (ring.rightNeighbor e)))

/--
A bad successor is an old bad resident away from the selected source,
or an arrival from an old bad source. Fresh firings are peaceful.
The arrival destination is cleared, and a cleared source stays cleared.
-/
theorem nativeE_bad_predecessor {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (N : Fin n → CertNative) (e v : Fin n)
    (hbad : Bad ring (nativeE ring N e) v) :
    (v ≠ e ∧ Bad ring N v) ∨
      (v = ring.rightNeighbor e ∧
        Bad ring N e ∧
        Cleared (nativeE ring N e v) ∧
        (Cleared (N e) → Cleared (nativeE ring N e e))) := by
  classical
  have hlocal :=
    PPL.Safety.PeacefulProps.peacefulScanLocality
      hn ring (cells N) (cells (nativeE ring N e)) e
      (cellsCase hn ring N e)
  have hvne : v ≠ e := by
    intro heq
    subst v
    have hz := nativeE_source_bullet_zero ring N e
    have hlive : (nativeE ring N e e).b = (2 : Fin 3) :=
      hbad.1
    rw [hz] at hlive
    have hv := congrArg Fin.val hlive
    omega
  by_cases hold : (N v).b = (2 : Fin 3)
  · left
    refine ⟨hvne, hold, ?_⟩
    intro hpeace
    exact hbad.2 ((hlocal.2.2 v hold hpeace).1 hbad.1)
  · by_cases hj : v = ring.rightNeighbor e
    · subst v
      by_cases hleft : (N e).b = (2 : Fin 3)
      · have hjne :=
          neighbor_ne (by omega : 2 ≤ n) ring e
        have hrowlive :
            (certLiteralEPair (N e)
              (N (ring.rightNeighbor e))).2.b = (2 : Fin 3) := by
          simpa [nativeE, LiveBullet, hjne, Ne.symm hjne] using hbad.1
        have hmoved :=
          (rowFacts (N e) (N (ring.rightNeighbor e))).2.2.2
            hrowlive hold
        right
        refine ⟨rfl, ⟨hleft, ?_⟩, ?_, ?_⟩
        · intro hpeace
          exact hbad.2
            ((hlocal.2.2 e hleft hpeace).2 rfl hbad.1 hold)
        · simpa [nativeE, hjne] using hmoved.1
        · intro hclear
          simpa [nativeE] using hmoved.2 hclear
      · exact False.elim
          (hbad.2
            (hlocal.2.1 _ hbad.1 hold (Or.inr hleft)))
    · exact False.elim
        (hbad.2
          (hlocal.2.1 v hbad.1 hold (Or.inl hj)))


/-- A cleared prefix certifies that a bad bullet has passed index zero. -/
noncomputable def credit {n : Nat}
    (N : Fin n → CertNative) (v : Fin n) : Nat := by
  classical
  exact if ClearedPrefix N v then n + v.val else v.val

theorem credit_ge {n : Nat}
    (N : Fin n → CertNative) (v : Fin n) :
    v.val ≤ credit N v := by
  classical
  unfold credit
  split <;> omega

theorem credit_lt {n : Nat}
    (N : Fin n → CertNative) (v : Fin n) :
    credit N v < 2 * n := by
  classical
  have hv := v.isLt
  unfold credit
  split <;> omega

theorem credit_mod {n : Nat}
    (N : Fin n → CertNative) (v : Fin n) :
    credit N v % n = v.val := by
  classical
  unfold credit
  split <;> simp [Nat.add_mod, Nat.mod_eq_of_lt v.isLt]

theorem prefix_stationary {n : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n)
    (N : Fin n → CertNative) (e v : Fin n)
    (hve : v ≠ e) (hc : ClearedPrefix N v) :
    ClearedPrefix (nativeE ring N e) v := by
  intro i hi
  by_cases hie : i = e
  · subst i
    have hne : e.val ≠ v.val := by
      intro h
      exact hve (Fin.ext h.symm)
    have hev : e.val < v.val := by omega
    have hj :
        (ring.rightNeighbor e).val = e.val + 1 := by
      change (e.val + 1) % n = e.val + 1
      exact Nat.mod_eq_of_lt (by have hv := v.isLt; omega)
    exact nativeE_source_cleared_of_pair ring N e
      (hc e hi)
      (hc (ring.rightNeighbor e) (by rw [hj]; omega))
  · by_cases hij : i = ring.rightNeighbor e
    · subst i
      exact nativeE_responder_cleared hn ring N e
        (hc (ring.rightNeighbor e) hi)
    · simpa [nativeE, hie, hij] using hc i hi

theorem prefix_moved {n : Nat}
    (ring : DirectedRing n)
    (N : Fin n → CertNative) (e : Fin n)
    (he : e.val + 1 < n)
    (hc : ClearedPrefix N e)
    (hs : Cleared (nativeE ring N e e))
    (ht : Cleared (nativeE ring N e (ring.rightNeighbor e))) :
    ClearedPrefix (nativeE ring N e) (ring.rightNeighbor e) := by
  have hj :
      (ring.rightNeighbor e).val = e.val + 1 :=
    Nat.mod_eq_of_lt he
  intro i hi
  by_cases hij : i = ring.rightNeighbor e
  · subst i
    exact ht
  · have hine : i.val ≠ (ring.rightNeighbor e).val := by
      intro h
      exact hij (Fin.ext h)
    have hie_le : i.val ≤ e.val := by omega
    by_cases hie : i = e
    · subst i
      exact hs
    · simpa [nativeE, hie, hij] using hc i hie_le

/--
A bad successor has an old bad predecessor whose credit does not
decrease. If that predecessor occupied the selected source, the credit
increases by at least one. Resident bullets and incoming bullets are
distinguished by nativeE_bad_predecessor.
-/
theorem nativeE_bad_credit {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (N : Fin n → CertNative) (e v : Fin n)
    (hbad : Bad ring (nativeE ring N e) v) :
    ∃ u : Fin n, Bad ring N u ∧
      credit N u ≤ credit (nativeE ring N e) v ∧
      (u = e → credit N u + 1 ≤ credit (nativeE ring N e) v) := by
  classical
  rcases nativeE_bad_predecessor hn ring N e v hbad with
      ⟨hne, hold⟩ | ⟨hv, hold, ht, hs⟩
  · refine ⟨v, hold, ?_, ?_⟩
    · by_cases hc : ClearedPrefix N v
      · have hc' := prefix_stationary (by omega : 2 ≤ n)
          ring N e v hne hc
        simp only [credit, if_pos hc, if_pos hc'] <;> omega
      · simpa only [credit, if_neg hc] using
          credit_ge (nativeE ring N e) v
    · intro he
      exact False.elim (hne he)
  · subst v
    have hstrict :
        credit N e + 1 ≤
          credit (nativeE ring N e) (ring.rightNeighbor e) := by
      by_cases hc : ClearedPrefix N e
      · have he : e.val + 1 < n := by
          by_cases hlt : e.val + 1 < n
          · exact hlt
          · have hall : ∀ i : Fin n, Cleared (N i) := by
              intro i
              exact hc i (by have hi := i.isLt; have hi' := e.isLt; omega)
            exact False.elim (hold.2 (cleared_all_core ring N e hall))
        have hc' := prefix_moved ring N e he hc
          (hs (hc e (Nat.le_refl _))) ht
        have hj :
            (ring.rightNeighbor e).val = e.val + 1 :=
          Nat.mod_eq_of_lt he
        simp only [credit, if_pos hc, if_pos hc', hj] <;> omega
      · by_cases he : e.val + 1 < n
        · have hj :
              (ring.rightNeighbor e).val = e.val + 1 :=
            Nat.mod_eq_of_lt he
          have hge := credit_ge (nativeE ring N e) (ring.rightNeighbor e)
          rw [hj] at hge
          simpa only [credit, if_neg hc] using hge
        · have heq : e.val + 1 = n := by
            have hi := e.isLt
            omega
          have hj : (ring.rightNeighbor e).val = 0 := by
            change (e.val + 1) % n = 0
            rw [heq, Nat.mod_self]
          have hc' :
              ClearedPrefix (nativeE ring N e) (ring.rightNeighbor e) := by
            intro i hi
            have hiv : i = ring.rightNeighbor e := by
              apply Fin.ext
              omega
            simpa only [hiv] using ht
          simp only [credit, if_neg hc, if_pos hc', hj] <;> omega
    exact ⟨e, hold, by omega, fun _ => hstrict⟩

/--
A canonical birth either removes/purifies a bad bullet or preserves
its credit. A birth inside a cleared prefix purifies the bullet.
-/
theorem birth_bad_credit {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (z v : Fin n)
    (hbad : Bad ring (canonicalBirth N z) v) :
    Bad ring N v ∧ credit N v ≤ credit (canonicalBirth N z) v := by
  classical
  have hvz : v ≠ z := by
    intro he
    subst v
    have hlive := hbad.1
    simp [LiveBullet, canonicalBirth, firedNative] at hlive
  have hbefore : Bad ring N v := by
    constructor
    · simpa [LiveBullet, canonicalBirth, hvz] using hbad.1
    · intro hc
      exact hbad.2 (birth_core ring N v z hc)
  refine ⟨hbefore, ?_⟩
  by_cases hc : ClearedPrefix N v
  · have hzv : v.val < z.val := by
      by_cases hz : z.val ≤ v.val
      · exact False.elim
          (hbad.2 (birth_inside_prefix ring N v z hz hc))
      · omega
    have hc' : ClearedPrefix (canonicalBirth N z) v := by
      intro i hi
      have hiz : i ≠ z := by
        intro he
        subst i
        omega
      simpa [canonicalBirth, hiz] using hc i hi
    simp only [credit, if_pos hc, if_pos hc'] <;> omega
  · simpa only [credit, if_neg hc] using
      credit_ge (canonicalBirth N z) v

/--
"Thus identities neither split nor migrate leftward; a surviving identity
either stays at its site or moves exactly one site clockwise on an
interaction."

For the two-sweep certificate, this identity-sensitive alternative
has the following observable consequence: every bad successor has an
old bad predecessor with nondecreasing credit, and service at that
predecessor's outgoing edge strictly increases its credit.
The finite native-row classification treats resident priority and
fresh firing separately; optional post-E births are handled afterward.
-/
theorem identity_sensitive_deterministic_assertion {n q : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (C : (protocol q).Configuration n) (e v : Fin n)
    (hbad : Bad ring
      (nativeProjection ((protocol q).step ring C e)) v) :
    ∃ u : Fin n, Bad ring (nativeProjection C) u ∧
      credit (nativeProjection C) u ≤
        credit (nativeProjection ((protocol q).step ring C e)) v ∧
      (u = e →
        credit (nativeProjection C) u + 1 ≤
          credit (nativeProjection ((protocol q).step ring C e)) v) := by
  obtain ⟨z, hz, hstep⟩ := native_step_eq hn ring C e
  cases z with
  | none =>
      rw [hstep] at hbad ⊢
      exact nativeE_bad_credit hn ring (nativeProjection C) e v hbad
  | some z =>
      rw [hstep] at hbad ⊢
      obtain ⟨hE, hbirth⟩ :=
        birth_bad_credit ring (nativeE ring (nativeProjection C) e) z v hbad
      obtain ⟨u, hu, hle, hstrict⟩ :=
        nativeE_bad_credit hn ring (nativeProjection C) e v hE
      exact ⟨u, hu, Nat.le_trans hle hbirth,
        fun he => Nat.le_trans (hstrict he) hbirth⟩


/-- Minimum of finitely many values, capped above by quota. -/
private def cappedFinMin (quota : Nat) :
    {m : Nat} → (Fin m → Nat) → Nat
  | 0, _ => quota
  | m + 1, f =>
      Nat.min (f 0)
        (cappedFinMin quota (fun i : Fin m => f i.succ))

private theorem cappedFinMin_le_cap (quota : Nat) :
    ∀ (m : Nat) (f : Fin m → Nat),
      cappedFinMin quota f ≤ quota := by
  intro m
  induction m with
  | zero =>
      intro f
      exact Nat.le_refl quota
  | succ m ih =>
      intro f
      exact Nat.le_trans (Nat.min_le_right _ _)
        (ih (fun i : Fin m => f i.succ))

private theorem cappedFinMin_le_each (quota : Nat) :
    ∀ (m : Nat) (f : Fin m → Nat) (i : Fin m),
      cappedFinMin quota f ≤ f i := by
  intro m
  induction m with
  | zero =>
      intro f i
      exact Fin.elim0 i
  | succ m ih =>
      intro f i
      refine Fin.cases ?_ ?_ i
      · exact Nat.min_le_left _ _
      · intro j
        exact Nat.le_trans (Nat.min_le_right _ _)
          (ih (fun k : Fin m => f k.succ) j)

private theorem le_cappedFinMin (quota k : Nat) :
    ∀ (m : Nat) (f : Fin m → Nat),
      k ≤ quota →
      (∀ i : Fin m, k ≤ f i) →
      k ≤ cappedFinMin quota f := by
  intro m
  induction m with
  | zero =>
      intro f hcap _
      exact hcap
  | succ m ih =>
      intro f hcap hall
      exact Nat.le_min_of_le_of_le (hall 0)
        (ih (fun i : Fin m => f i.succ) hcap
          (fun i => hall i.succ))

/--
A finite bad-object credit certificate gives a nominated-edge clock.

Each bad object's credit is below quota, with its host as its residue
modulo n. A bad successor has a bad predecessor with nondecreasing
credit; credit increases strictly at the selected source.

The remaining request count is quota minus the minimum bad credit,
with the minimum set to quota when no bad object remains.
-/
theorem cost_le_of_bad_credit
    {S : Type} {n : Nat}
    (hn : 0 < n) (quota : Nat)
    (next : S → Fin n → S)
    (target : S → Prop)
    (Bad : S → Fin n → Prop)
    (credit : S → Fin n → Nat)
    (htarget : ∀ x, (∀ v, ¬ Bad x v) → target x)
    (hcap : ∀ x v, Bad x v → credit x v < quota)
    (hmod : ∀ x v, Bad x v → credit x v % n = v.val)
    (hpred : ∀ x e v, Bad (next x e) v →
      ∃ u : Fin n,
        Bad x u ∧
        credit x u ≤ credit (next x e) v ∧
        (u = e → credit x u + 1 ≤ credit (next x e) v))
    (x₀ : S) (T : Nat) :
    costNumerator next target x₀ T ≤
      n ^ T * (n * quota) := by
  classical
  let m : S → Nat := fun x =>
    cappedFinMin quota
      (fun v => if Bad x v then credit x v else quota)
  let remaining : S → Nat := fun x => quota - m x
  let chosen : S → Fin n := fun x =>
    ⟨m x % n, Nat.mod_lt _ hn⟩

  have m_cap : ∀ x, m x ≤ quota := by
    intro x
    exact cappedFinMin_le_cap quota n
      (fun v => if Bad x v then credit x v else quota)

  have m_le : ∀ x v, Bad x v → m x ≤ credit x v := by
    intro x v hv
    have h :=
      cappedFinMin_le_each quota n
        (fun w => if Bad x w then credit x w else quota) v
    simpa only [m, if_pos hv] using h

  have lower :
      ∀ x k, k ≤ quota →
        (∀ v, Bad x v → k ≤ credit x v) →
        k ≤ m x := by
    intro x k hk hall
    change k ≤ cappedFinMin quota
      (fun v => if Bad x v then credit x v else quota)
    apply le_cappedFinMin quota k n _ hk
    intro v
    by_cases hv : Bad x v
    · simpa only [if_pos hv] using hall v hv
    · simpa only [if_neg hv] using hk

  have m_lt : ∀ x, ¬ target x → m x < quota := by
    intro x hx
    by_cases hex : ∃ v, Bad x v
    · obtain ⟨v, hv⟩ := hex
      exact Nat.lt_of_le_of_lt (m_le x v hv) (hcap x v hv)
    · have hp : target x := htarget x (by
        intro v hv
        exact hex ⟨v, hv⟩)
      exact False.elim (hx hp)

  have hdrop :
      ∀ x, ¬ target x →
        remaining (next x (chosen x)) + 1 ≤ remaining x := by
    intro x hx
    have hsmall : m x < quota := m_lt x hx
    have hrise : m x + 1 ≤ m (next x (chosen x)) := by
      apply lower (next x (chosen x)) (m x + 1) (by omega)
      intro v hv
      obtain ⟨u, hu, hnondec, hstrict⟩ :=
        hpred x (chosen x) v hv
      have hprior : m x ≤ credit x u := m_le x u hu
      by_cases heq : m x = credit x u
      · have hue : u = chosen x := by
          apply Fin.ext
          calc
            u.val = credit x u % n := (hmod x u hu).symm
            _ = m x % n := by rw [heq]
            _ = (chosen x).val := rfl
        have hd := hstrict hue
        omega
      · omega
    have hafter : m (next x (chosen x)) ≤ quota :=
      m_cap (next x (chosen x))
    change quota - m (next x (chosen x)) + 1 ≤ quota - m x
    omega

  have hnoninc :
      ∀ x, ¬ target x → ∀ e,
        remaining (next x e) ≤ remaining x := by
    intro x _ e
    have hrise : m x ≤ m (next x e) := by
      apply lower (next x e) (m x) (m_cap x)
      intro v hv
      obtain ⟨u, hu, hnondec, _⟩ := hpred x e v hv
      exact Nat.le_trans (m_le x u hu) hnondec
    change quota - m (next x e) ≤ quota - m x
    omega

  have hb :=
    Prob.costNumerator_le_of_nominated_edge
      next target remaining chosen hdrop hnoninc x₀ T
  have hpotential : remaining x₀ ≤ quota :=
    Nat.sub_le quota (m x₀)
  exact Nat.le_trans hb
    (Nat.mul_le_mul_left (n ^ T)
      (Nat.mul_le_mul_left n hpotential))


end PurificationProof

/--
Purification from every Cartesian configuration of the real protocol.
The minimum-credit certificate supplies at most 2*n nominated requests;
the existing nominated-edge theorem charges n per request.
-/
theorem purification_cost {n q : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (C : (protocol q).Configuration n) (T : Nat) :
    costNumerator
        (fun D e => (protocol q).step ring D e)
        (fun D => P ring (nativeProjection D)) C T ≤
      n ^ T * (2 * n ^ 2) := by
  classical
  have htarget :
      ∀ D : (protocol q).Configuration n,
        (∀ v : Fin n,
          ¬ PurificationProof.Bad ring (nativeProjection D) v) →
        P ring (nativeProjection D) := by
    intro D h v hlive
    by_cases hc :
        PurificationProof.CorePeace ring (nativeProjection D) v
    · exact hc
    · exact False.elim (h v ⟨hlive, hc⟩)
  have hb :=
    PurificationProof.cost_le_of_bad_credit
      (by omega : 0 < n) (2 * n)
      (fun D e => (protocol q).step ring D e)
      (fun D => P ring (nativeProjection D))
      (fun D v => PurificationProof.Bad ring (nativeProjection D) v)
      (fun D v => PurificationProof.credit (nativeProjection D) v)
      htarget
      (fun D v _ => PurificationProof.credit_lt (nativeProjection D) v)
      (fun D v _ => PurificationProof.credit_mod (nativeProjection D) v)
      (fun D e v hbad =>
        PurificationProof.identity_sensitive_deterministic_assertion
          (by omega : 3 ≤ n) ring D e v hbad)
      C T
  have hscale : n * (2 * n) = 2 * n ^ 2 := by
    rw [Nat.pow_succ, Nat.pow_one]
    ac_rfl
  simpa only [hscale] using hb

/-- Expected first entrance into P under the uniform IID edge scheduler. -/
theorem purification_expected {n q : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (C : (protocol q).Configuration n) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (fun D e => (protocol q).step ring D e)
      (fun D => P ring (nativeProjection D))
      C ((2 * n ^ 2 : Nat) : Rat) := by
  apply
    (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      (fun D e => (protocol q).step ring D e)
      (fun D => P ring (nativeProjection D))
      (by omega : 0 < n) C (2 * n ^ 2)).2
  intro T
  exact purification_cost hn ring C T

end L3
