import Leader.L3.CandidateClosure

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-!
# Singleton native clean-sector closure (repair.tex, lem:singleton-generated-closure, native part)

For n >= 5, a one-leader configuration in the
native clean sector `C_native` stays a one-leader configuration in `C_native` after every
`nativeE` edge, and with `H_cand` the singleton generated class is closed under the birth-free
Phi step. The first-credit invariant (no second entry before retirement) is not proved here.
-/

/-! ## Singleton native clean-sector closure -/

namespace CandidateNativeProof

private theorem finThreeCases (b : Fin 3) :
    b = (0 : Fin 3) ∨ b = (1 : Fin 3) ∨ b = (2 : Fin 3) := by
  rcases b with ⟨v, hv⟩
  rcases v with _ | _ | _ | v
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · omega

private theorem row_no_new_leader (a b : CertNative) :
    ((certLiteralEPair a b).1.l = true → a.l = true) ∧
    ((certLiteralEPair a b).2.l = true → b.l = true) := by
  rcases a with ⟨al, ab, ash, asg⟩
  rcases b with ⟨bl, bb, bsh, bsg⟩
  rcases finThreeCases ab with rfl | rfl | rfl <;>
  rcases finThreeCases bb with rfl | rfl | rfl <;>
  cases al <;> cases bl <;> cases ash <;> cases bsh <;>
  cases asg <;> cases bsg <;> decide

private theorem native_no_new_leader {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (e i : Fin n) (hi : (nativeE ring N e i).l = true) :
    (N i).l = true := by
  by_cases he : i = e
  · subst i
    apply (row_no_new_leader (N e) (N (ring.rightNeighbor e))).1
    simpa [nativeE] using hi
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      apply (row_no_new_leader (N e) (N (ring.rightNeighbor e))).2
      simpa [nativeE, he] using hi
    · simpa [nativeE, he, hj] using hi

/-- PPlus survival plus no native births fixes the actual singleton root. -/
theorem leader_fixed {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (N : Fin n → CertNative) (e p : Fin n)
    (hp : (N p).l = true)
    (hu : ∀ i : Fin n, (N i).l = true → i = p)
    (hP : PPlus ring N) :
    (nativeE ring N e p).l = true ∧
    (∀ i : Fin n, (nativeE ring N e i).l = true → i = p) ∧
    (∀ i : Fin n, (nativeE ring N e i).l = (N i).l) := by
  have hplus := nativeE_preserves_PPlus hn ring N e hP
  obtain ⟨r, hr⟩ := hplus.1
  have hrp := hu r (native_no_new_leader ring N e r hr)
  have hroot : (nativeE ring N e p).l = true := by
    simpa only [hrp] using hr
  refine ⟨hroot, ?_, ?_⟩
  · intro i hi
    exact hu i (native_no_new_leader ring N e i hi)
  · intro i
    cases hold : (N i).l with
    | false =>
        cases hnew : (nativeE ring N e i).l with
        | false => rfl
        | true =>
            have ht := native_no_new_leader ring N e i hnew
            rw [hold] at ht
            cases ht
    | true =>
        have hip := hu i hold
        subst i
        exact hroot

/-! Rotation to the actual unique root. -/

private def zeroSite {n : Nat} (ring : DirectedRing n) : Fin n :=
  ⟨0, ring.hn⟩

def site {n : Nat} (ring : DirectedRing n)
    (p k : Fin n) : Fin n := PPL.shiftRight ring p k.val

def position {n : Nat} (ring : DirectedRing n)
    (p i : Fin n) : Fin n :=
  ⟨PPL.cyclicOffset ring p i, Nat.mod_lt _ ring.hn⟩

private theorem site_zero {n : Nat}
    (ring : DirectedRing n) (p : Fin n) :
    site ring p (zeroSite ring) = p := by
  apply Fin.ext
  simp [site, zeroSite, PPL.shiftRight, Nat.mod_eq_of_lt p.isLt]

private theorem shift_full {n : Nat}
    (ring : DirectedRing n) (p : Fin n) :
    PPL.shiftRight ring p n = p := by
  apply Fin.ext
  change (p.val + n) % n = p.val
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt p.isLt]

private theorem position_site {n : Nat}
    (ring : DirectedRing n) (p k : Fin n) :
    position ring p (site ring p k) = k := by
  apply Fin.ext
  change (((p.val + k.val) % n + n - p.val) % n) = k.val
  by_cases hs : p.val + k.val < n
  · rw [Nat.mod_eq_of_lt hs]
    have he : p.val + k.val + n - p.val = n + k.val := by omega
    rw [he, Nat.add_mod_left, Nat.mod_eq_of_lt k.isLt]
  · have hge : n ≤ p.val + k.val := by omega
    have hlt : p.val + k.val - n < n := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt]
    have he : p.val + k.val - n + n - p.val = k.val := by omega
    rw [he, Nat.mod_eq_of_lt k.isLt]

private theorem site_position {n : Nat}
    (ring : DirectedRing n) (p i : Fin n) :
    site ring p (position ring p i) = i := by
  apply Fin.ext
  change (p.val + ((i.val + n - p.val) % n)) % n = i.val
  by_cases hpi : p.val ≤ i.val
  · have he : i.val + n - p.val = n + (i.val - p.val) := by omega
    rw [he, Nat.add_mod_left,
      Nat.mod_eq_of_lt (by omega : i.val - p.val < n)]
    have hh : p.val + (i.val - p.val) = i.val := by omega
    rw [hh, Nat.mod_eq_of_lt i.isLt]
  · have hlt : i.val + n - p.val < n := by omega
    rw [Nat.mod_eq_of_lt hlt]
    have hh : p.val + (i.val + n - p.val) = i.val + n := by omega
    rw [hh, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

private theorem site_injective {n : Nat}
    (ring : DirectedRing n) (p a b : Fin n)
    (h : site ring p a = site ring p b) : a = b := by
  have he := congrArg (position ring p) h
  rw [position_site, position_site] at he
  exact he

private theorem site_eq_root {n : Nat}
    (ring : DirectedRing n) (p k : Fin n) :
    site ring p k = p ↔ k.val = 0 := by
  constructor
  · intro h
    have he := site_injective ring p k (zeroSite ring)
      (h.trans (site_zero ring p).symm)
    exact congrArg Fin.val he
  · intro h
    have he : k = zeroSite ring := Fin.ext h
    rw [he, site_zero]

private theorem site_next {n : Nat}
    (ring : DirectedRing n) (p k : Fin n) :
    site ring p (ring.rightNeighbor k) =
      ring.rightNeighbor (site ring p k) := by
  apply Fin.ext
  change (p.val + (k.val + 1) % n) % n =
    ((p.val + k.val) % n + 1) % n
  calc
    (p.val + (k.val + 1) % n) % n =
        ((k.val + 1) % n + p.val) % n := by rw [Nat.add_comm]
    _ = (k.val + 1 + p.val) % n := Nat.mod_add_mod _ _ _
    _ = (p.val + k.val + 1) % n := by congr 1; omega
    _ = ((p.val + k.val) % n + 1) % n :=
      (Nat.mod_add_mod _ _ _).symm

private theorem root_boolean {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative) (p : Fin n)
    (hp : (N p).l = true)
    (hu : ∀ i : Fin n, (N i).l = true → i = p)
    (k : Fin n) :
    (N (site ring p k)).l = decide (k.val = 0) := by
  by_cases hk : k.val = 0
  · rw [(site_eq_root ring p k).2 hk]
    simp [hp, hk]
  · have hne : site ring p k ≠ p := by
      intro h
      exact hk ((site_eq_root ring p k).1 h)
    cases hs : (N (site ring p k)).l with
    | false => simp [hk]
    | true => exact False.elim (hne (hu _ hs))

private theorem sector_full {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative) (p : Fin n)
    (hp : (N p).l = true)
    (hu : ∀ i : Fin n, (N i).l = true → i = p) :
    sectorLength ring N p ⟨n, by omega⟩ := by
  refine ⟨ring.hn, hp, ?_, ?_⟩
  · simpa only [shift_full] using hp
  · intro k hk hkn
    cases hl : (N (PPL.shiftRight ring p k.val)).l with
    | false => rfl
    | true =>
        have he := hu _ hl
        have hz := (site_eq_root ring p k).1 he
        omega

private theorem sector_unique {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative) (p : Fin n)
    (hu : ∀ i : Fin n, (N i).l = true → i = p)
    (q : Fin n) (d : Fin (n + 1))
    (hs : sectorLength ring N q d) :
    q = p ∧ d.val = n := by
  have hqp : q = p := hu q hs.2.1
  subst q
  refine ⟨rfl, ?_⟩
  have hnext : PPL.shiftRight ring p d.val = p :=
    hu _ hs.2.2.1
  have hdpos : 0 < d.val := hs.1
  have hdle : d.val ≤ n := by
    have hdlt : d.val < n + 1 := d.isLt
    omega
  by_cases hd : d.val < n
  · have hz : d.val = 0 :=
      (site_eq_root ring p ⟨d.val, hd⟩).1 hnext
    omega
  · omega

/-! The shield-independent observation of an E row with surviving leaders. -/

private structure Observation where
  leader : Bool
  bullet : Fin 3
  signal : Bool
  deriving DecidableEq, Repr

private def observe (a : CertNative) : Observation :=
  ⟨a.l, a.b, a.sg⟩

private theorem observation_ext {x y : Observation}
    (hl : x.leader = y.leader)
    (hb : x.bullet = y.bullet)
    (hs : x.signal = y.signal) : x = y := by
  cases x
  cases y
  cases hl
  cases hb
  cases hs
  rfl

private theorem observation_mk_eq
    (l r : Bool) (b c : Fin 3) (s t : Bool) :
    (Observation.mk l b s = Observation.mk r c t) ↔
      (l = r ∧ b = c ∧ s = t) := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl, rfl⟩
  · intro h
    exact observation_ext h.1 h.2.1 h.2.2

private def observedPair (x y : Observation) : Observation × Observation :=
  let sent : Fin 3 :=
    if x.leader then (if x.signal then 2 else x.bullet) else x.bullet
  let rb : Fin 3 :=
    if y.leader then (if y.signal then 1 else y.bullet)
    else if y.bullet = 0 then sent else y.bullet
  let rs : Bool :=
    if y.leader then false else if sent = 0 then y.signal else false
  let ls : Bool :=
    (if x.leader then false else x.signal) || rs || y.leader
  (⟨x.leader, 0, ls⟩, ⟨y.leader, rb, rs⟩)

/-- This finite lemma uses the literal certLiteralEPair, not a replacement
protocol. Its only condition is preservation of the right leader bit. -/
private theorem row_observed (a b : CertNative)
    (hkeep : (certLiteralEPair a b).2.l = b.l) :
    (observe (certLiteralEPair a b).1,
      observe (certLiteralEPair a b).2) =
        observedPair (observe a) (observe b) := by
  rcases a with ⟨al, ab, ash, asg⟩
  rcases b with ⟨bl, bb, bsh, bsg⟩
  rcases finThreeCases ab with rfl | rfl | rfl <;>
  rcases finThreeCases bb with rfl | rfl | rfl <;>
  cases al <;> cases bl <;> cases ash <;> cases bsh <;>
  cases asg <;> cases bsg <;>
  simp_all [observe, observedPair, certLiteralEPair, certFinThree]

/-! A normal form for the exact singleton signal/bullet conditions.

host=n, kind=0 means no bullet. Otherwise host<n is the single bullet
position and kind is either dummy or live. Followers have signal one
exactly at offsets >=cut. A present bullet has host<cut and ready=false.
A bullet-free ready leader requires cut=1.
-/

structure CleanWord where
  host : Nat
  kind : Fin 3
  cut : Nat
  ready : Bool

def WordValid (n : Nat) (w : CleanWord) : Prop :=
  1 ≤ w.cut ∧ w.cut ≤ n ∧
    ((w.host = n ∧ w.kind = 0 ∧ (w.ready = true → w.cut = 1)) ∨
     (w.host < n ∧ w.kind ≠ 0 ∧ w.host < w.cut ∧ w.ready = false))

def wordAt (w : CleanWord) (i : Nat) : Observation :=
  { leader := decide (i = 0)
    bullet := if i = w.host then w.kind else 0
    signal := if i = 0 then w.ready else decide (w.cut ≤ i) }

private def wordStep (n : Nat) (w : CleanWord) (a i : Nat) : Observation :=
  let j := if a + 1 < n then a + 1 else 0
  let out := observedPair (wordAt w a) (wordAt w j)
  if i = a then out.1 else if i = j then out.2 else wordAt w i

def nextWord (n : Nat) (w : CleanWord) (a : Nat) : CleanWord :=
  if w.host = n then
    if w.ready = true ∧ a = 0 then
      { host := 1, kind := 2, cut := 2, ready := false }
    else if w.ready = true ∧ a + 1 = n then
      { host := 0, kind := 1, cut := 1, ready := false }
    else
      { host := n, kind := 0
        cut := if a = 0 then w.cut else if w.cut = a + 1 then a else w.cut
        ready := if a = 0 then decide (w.cut = 1) else w.ready }
  else if a = w.host then
    if a + 1 = n then
      { host := n, kind := 0, cut := a, ready := false }
    else
      { host := a + 1, kind := w.kind
        cut := if w.cut = a + 1 then a + 2 else w.cut
        ready := false }
  else
    { host := w.host, kind := w.kind
      cut := if w.cut = a + 1 then a else w.cut
      ready := false }

private theorem decide_same (p q : Prop) [Decidable p] [Decidable q] :
    (decide p = decide q) ↔ (p ↔ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

private theorem decide_or (p q : Prop) [Decidable p] [Decidable q] :
    (decide p || decide q) = decide (p ∨ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem nextWord_valid (n : Nat) (hn : 5 ≤ n)
    (w : CleanWord) (hv : WordValid n w) (a : Nat) (ha : a < n) :
    WordValid n (nextWord n w a) := by
  rcases hv with ⟨hcutpos, hcutle, hcases⟩
  rcases hcases with hempty | hfull
  · rcases hempty with ⟨hhost, _, hready⟩
    by_cases hleft : w.ready = true ∧ a = 0
    · rw [nextWord, if_pos hhost, if_pos hleft]
      have hnewcutle : 2 ≤ n := by omega
      have hnewhostlt : 1 < n := by omega
      have hnewcutpos : 1 ≤ (2 : Nat) := by omega
      have hnewbefore : (1 : Nat) < 2 := by omega
      have hnewkind : (2 : Fin 3) ≠ 0 := by decide
      exact ⟨hnewcutpos, hnewcutle,
        Or.inr ⟨hnewhostlt, hnewkind, hnewbefore, rfl⟩⟩
    · by_cases hright : w.ready = true ∧ a + 1 = n
      · rw [nextWord, if_pos hhost, if_neg hleft, if_pos hright]
        have hnewcutle : 1 ≤ n := by omega
        have hnewhostlt : 0 < n := by omega
        have hnewcutpos : 1 ≤ (1 : Nat) := by omega
        have hnewbefore : (0 : Nat) < 1 := by omega
        have hnewkind : (1 : Fin 3) ≠ 0 := by decide
        exact ⟨hnewcutpos, hnewcutle,
          Or.inr ⟨hnewhostlt, hnewkind, hnewbefore, rfl⟩⟩
      · rw [nextWord, if_pos hhost, if_neg hleft, if_neg hright]
        by_cases hzero : a = 0
        · simp only [if_pos hzero]
          refine ⟨hcutpos, hcutle, Or.inl ⟨rfl, rfl, ?_⟩⟩
          intro hnewready
          exact of_decide_eq_true hnewready
        · simp only [if_neg hzero]
          by_cases hcut : w.cut = a + 1
          · simp only [if_pos hcut]
            have hapos : 1 ≤ a := by omega
            have hale : a ≤ n := by omega
            refine ⟨hapos, hale, Or.inl ⟨rfl, rfl, ?_⟩⟩
            intro hr
            have hcutone : w.cut = 1 := hready hr
            omega
          · simp only [if_neg hcut]
            exact ⟨hcutpos, hcutle, Or.inl ⟨rfl, rfl, hready⟩⟩
  · rcases hfull with ⟨hhostlt, hkind, hbefore, _⟩
    have hhostne : w.host ≠ n := by omega
    rw [nextWord, if_neg hhostne]
    by_cases hat : a = w.host
    · rw [if_pos hat]
      by_cases hwrap : a + 1 = n
      · rw [if_pos hwrap]
        have hapos : 1 ≤ a := by omega
        have hale : a ≤ n := by omega
        refine ⟨hapos, hale, Or.inl ⟨rfl, rfl, ?_⟩⟩
        intro hfalse
        cases hfalse
      · rw [if_neg hwrap]
        have hnextlt : a + 1 < n := by omega
        by_cases hcut : w.cut = a + 1
        · simp only [if_pos hcut]
          have hnewcutpos : 1 ≤ a + 2 := by omega
          have hnewcutle : a + 2 ≤ n := by omega
          have hnewbefore : a + 1 < a + 2 := by omega
          exact ⟨hnewcutpos, hnewcutle,
            Or.inr ⟨hnextlt, hkind, hnewbefore, rfl⟩⟩
        · simp only [if_neg hcut]
          have hnewbefore : a + 1 < w.cut := by omega
          exact ⟨hcutpos, hcutle,
            Or.inr ⟨hnextlt, hkind, hnewbefore, rfl⟩⟩
    · rw [if_neg hat]
      by_cases hcut : w.cut = a + 1
      · simp only [if_pos hcut]
        have hhostbefore : w.host < a := by omega
        have hapos : 1 ≤ a := by omega
        have hale : a ≤ n := by omega
        exact ⟨hapos, hale,
          Or.inr ⟨hhostlt, hkind, hhostbefore, rfl⟩⟩
      · simp only [if_neg hcut]
        exact ⟨hcutpos, hcutle,
          Or.inr ⟨hhostlt, hkind, hbefore, rfl⟩⟩

private theorem bool_eq_of_true_iff (b c : Bool)
    (h : (b = true ↔ c = true)) : b = c := by
  cases b <;> cases c <;> simp_all

private theorem observation_eq_of_true_iff {x y : Observation}
    (hl : x.leader = true ↔ y.leader = true)
    (hb : x.bullet = y.bullet)
    (hs : x.signal = true ↔ y.signal = true) : x = y := by
  exact observation_ext
    (bool_eq_of_true_iff _ _ hl) hb (bool_eq_of_true_iff _ _ hs)

theorem nextWord_eq (n : Nat) (hn : 5 ≤ n)
    (w : CleanWord) (hv : WordValid n w)
    (a i : Nat) (ha : a < n) (hi : i < n) :
    wordStep n w a i = wordAt (nextWord n w a) i := by
  have hnpos : 0 < n := by omega
  have hanext : a + 1 ≤ n := by omega
  have hane : a ≠ n := by omega
  have hine : i ≠ n := by omega
  have hnextpos : a + 1 ≠ 0 := by omega
  rcases hv with ⟨hcutpos, hcutbound, hempty | hfull⟩
  · rcases hempty with ⟨hhost, hkind, hreadycut⟩
    cases hready : w.ready with
    | false =>
        by_cases hazero : a = 0 <;> try omega
        all_goals
          by_cases hanextlt : a + 1 < n <;> try omega
        all_goals
          by_cases halast : a + 1 = n <;> try omega
        all_goals
          by_cases hcutnext : w.cut = a + 1 <;> try omega
        all_goals
          by_cases hia : i = a <;> try omega
        all_goals
          by_cases hinext : i = a + 1 <;> try omega
        all_goals
          by_cases hizero : i = 0 <;> try omega
        all_goals
          apply observation_eq_of_true_iff <;>
            simp_all [wordStep, wordAt, nextWord, observedPair] <;> omega
    | true =>
        have hcutone : w.cut = 1 := hreadycut (by simp [hready])
        clear hreadycut
        obtain ⟨host, kind, cut, ready⟩ := w
        try dsimp only at hhost hkind hcutone hready hcutpos hcutbound
        subst hkind hcutone hready
        have h1n : 1 < n := by omega
        have hn1 : ¬ n ≤ 1 := by omega
        by_cases hazero : a = 0 <;> try omega
        all_goals
          by_cases hanextlt : a + 1 < n <;> try omega
        all_goals
          by_cases halast : a + 1 = n <;> try omega
        all_goals
          by_cases hcutnext : a = 0 <;> try omega
        all_goals
          by_cases hia : i = a <;> try omega
        all_goals
          by_cases hinext : i = a + 1 <;> try omega
        all_goals
          by_cases hizero : i = 0 <;> try omega
        all_goals
          by_cases hione : i = 1 <;> try omega
        all_goals
          have hza : (0 = a) = (a = 0) := propext eq_comm
          have hzi : (0 = i) = (i = 0) := propext eq_comm
          have hoi : (1 = i) = (i = 1) := propext eq_comm
          have hai : (a = i) = (i = a) := propext eq_comm
          have hsi : (a + 1 = i) = (i = a + 1) := propext eq_comm
        all_goals
          apply observation_eq_of_true_iff <;>
            simp [wordStep, wordAt, nextWord, observedPair, *] <;> omega
  · rcases hfull with ⟨hhostlt, hkind, hhostcut, hready⟩
    have hhostne : w.host ≠ n := by omega
    by_cases hazero : a = 0 <;> try omega
    all_goals
      by_cases hanextlt : a + 1 < n <;> try omega
    all_goals
      by_cases halast : a + 1 = n <;> try omega
    all_goals
      by_cases hahost : a = w.host <;> try omega
    all_goals
      by_cases hnexthost : a + 1 = w.host <;> try omega
    all_goals
      by_cases hzerohost : 0 = w.host <;> try omega
    all_goals
      by_cases hcutnext : w.cut = a + 1 <;> try omega
    all_goals
      by_cases hia : i = a <;> try omega
    all_goals
      by_cases hinext : i = a + 1 <;> try omega
    all_goals
      by_cases hizero : i = 0 <;> try omega
    all_goals
      by_cases hihost : i = w.host <;> try omega
    all_goals
      apply observation_eq_of_true_iff <;>
        simp_all [wordStep, wordAt, nextWord, observedPair] <;> omega

def Shape {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (p : Fin n) (w : CleanWord) : Prop :=
  ∀ k : Fin n, observe (N (site ring p k)) = wordAt w k.val

/-- Extract the finite-cut normal form from the exact C_native predicate. -/
theorem clean_shape {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (N : Fin n → CertNative) (p : Fin n)
    (hp : (N p).l = true)
    (hu : ∀ i : Fin n, (N i).l = true → i = p)
    (hc : C_native ring N) :
    ∃ w : CleanWord, WordValid n w ∧ Shape ring N p w := by
  classical
  have hsector := sector_full ring N p hp hu
  have hi := hc.1.2 p ⟨n, by omega⟩ hsector
  have hs := hc.2 p ⟨n, by omega⟩ hsector
  rcases hs with hbullet | hempty
  · rcases hbullet with ⟨h, hh, hb, htrail, cut, hlo, hhi, hz, ho⟩
    let w : CleanWord :=
      { host := h.val, kind := (N (site ring p h)).b
        cut := cut.val, ready := false }
    refine ⟨w, ?_, ?_⟩
    · refine ⟨by dsimp [w]; omega, hhi, Or.inr ?_⟩
      exact ⟨h.isLt, hb, by dsimp [w]; omega, rfl⟩
    · intro k
      apply observation_ext
      · exact root_boolean ring N p hp hu k
      · change (N (site ring p k)).b =
          if k.val = h.val then (N (site ring p h)).b else 0
        by_cases hkh : k.val = h.val
        · have he : k = h := Fin.ext hkh
          subst k
          simp
        · have hkzero : (N (site ring p k)).b = 0 := by
            by_cases hkz : (N (site ring p k)).b = 0
            · exact hkz
            · have he : k = h := hi.1 k h k.isLt h.isLt hkz hb
              exact False.elim (hkh (congrArg Fin.val he))
          simpa [hkh] using hkzero
      · change (N (site ring p k)).sg =
          if k.val = 0 then false else decide (cut.val ≤ k.val)
        by_cases hkh : k.val ≤ h.val
        · have hzero : (N (site ring p k)).sg = false :=
            htrail k hkh
          have hlt : ¬ cut.val ≤ k.val := by omega
          simp [hzero, hlt]
        · have hkpos : k.val ≠ 0 := by omega
          have hkafter : h.val + 1 ≤ k.val := by omega
          by_cases hkcut : k.val < cut.val
          · have hzero : (N (site ring p k)).sg = false :=
              hz k hkafter hkcut
            have hlt : ¬ cut.val ≤ k.val := by omega
            simp [hzero, hkpos, hlt]
          · have hle : cut.val ≤ k.val := by omega
            have hone : (N (site ring p k)).sg = true :=
              ho k hle k.isLt
            simp [hone, hkpos, hle]
  · rcases hempty with ⟨hno, ⟨cut, hlo, hhi, hz, ho⟩, hready⟩
    have hcutready : (N p).sg = true → cut.val = 1 := by
      intro hr
      by_cases he : cut.val = 1
      · exact he
      · let one : Fin n := ⟨1, by omega⟩
        have hzero := hz one (by simp [one]) (by dsimp [one]; omega)
        have hone := hready hr one (by simp [one]) one.isLt
        rw [hzero] at hone
        cases hone
    let w : CleanWord :=
      { host := n, kind := 0, cut := cut.val, ready := (N p).sg }
    refine ⟨w, ⟨hlo, hhi, Or.inl ⟨rfl, rfl, hcutready⟩⟩, ?_⟩
    intro k
    apply observation_ext
    · exact root_boolean ring N p hp hu k
    · change (N (site ring p k)).b = if k.val = n then 0 else 0
      have hkzero : (N (site ring p k)).b = 0 := by
        by_cases hkz : (N (site ring p k)).b = 0
        · exact hkz
        · exact False.elim (hno k k.isLt hkz)
      simpa using hkzero
    · change (N (site ring p k)).sg =
        if k.val = 0 then (N p).sg else decide (cut.val ≤ k.val)
      by_cases hkzero : k.val = 0
      · rw [(site_eq_root ring p k).2 hkzero]
        simp [hkzero]
      · have hkpos : 1 ≤ k.val := by omega
        by_cases hkcut : k.val < cut.val
        · have hzero : (N (site ring p k)).sg = false :=
            hz k hkpos hkcut
          have hlt : ¬ cut.val ≤ k.val := by omega
          simp [hzero, hkzero, hlt]
        · have hle : cut.val ≤ k.val := by omega
          have hone : (N (site ring p k)).sg = true :=
            ho k hle k.isLt
          simp [hone, hkzero, hle]

/-- Reconstruct all clauses of I and C_native, not just a weakened
signal predicate. The input PPlus contains the actual shield condition. -/
theorem shape_clean {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative) (p : Fin n)
    (hu : ∀ i : Fin n, (N i).l = true → i = p)
    (hP : PPlus ring N) (w : CleanWord)
    (hv : WordValid n w) (hs : Shape ring N p w) :
    C_native ring N := by
  have hb : ∀ k : Fin n,
      (N (site ring p k)).b = if k.val = w.host then w.kind else 0 := by
    intro k
    exact congrArg Observation.bullet (hs k)
  have hg : ∀ k : Fin n,
      (N (site ring p k)).sg =
        if k.val = 0 then w.ready else decide (w.cut ≤ k.val) := by
    intro k
    exact congrArg Observation.signal (hs k)
  have hhost : ∀ k : Fin n, HasBullet N (site ring p k) →
      k.val = w.host ∧ w.kind ≠ 0 := by
    intro k hk
    change (N (site ring p k)).b ≠ 0 at hk
    rw [hb k] at hk
    by_cases he : k.val = w.host
    · exact ⟨he, by simpa [he] using hk⟩
    · simp [he] at hk
  have htrail : ∀ a : Fin n, HasBullet N (site ring p a) →
      ∀ k : Fin n, k.val ≤ a.val → (N (site ring p k)).sg = false := by
    intro a ha k hk
    obtain ⟨hah, hkind⟩ := hhost a ha
    rcases hv.2.2 with hempty | hfull
    · exact False.elim (hkind hempty.2.1)
    · have hcut := hfull.2.2.1
      have hr := hfull.2.2.2
      have hlt : ¬ w.cut ≤ k.val := by omega
      rw [hg k]
      simp [hr, hlt]
  have hsuffix : ∀ lo : Nat, 1 ≤ lo → lo ≤ w.cut →
      signalZeroStarOneStar ring N p lo n := by
    intro lo hlo hcut
    have hcutpos : 1 ≤ w.cut := hv.1
    have hcutbound : w.cut ≤ n := hv.2.1
    have hcutlt : w.cut < n + 1 := by omega
    refine ⟨⟨w.cut, hcutlt⟩, hcut, hcutbound, ?_, ?_⟩
    · intro k hklo hkcut
      change k.val < w.cut at hkcut
      change (N (site ring p k)).sg = false
      have hkpos : 1 ≤ k.val := by omega
      have hkzero : k.val ≠ 0 := by omega
      have hlt : ¬ w.cut ≤ k.val := by omega
      rw [hg k]
      simp [hkzero, hlt]
    · intro k hkcut hkn
      change w.cut ≤ k.val at hkcut
      change (N (site ring p k)).sg = true
      have hkpos : 1 ≤ k.val := by omega
      have hkzero : k.val ≠ 0 := by omega
      rw [hg k]
      simp [hkzero, hkcut]
  constructor
  · refine ⟨hP, ?_⟩
    intro q d hsector
    obtain ⟨hqp, hd⟩ := sector_unique ring N p hu q d hsector
    subst q
    constructor
    · intro a b ha hbb hba hbullet
      have hapos := (hhost a hba).1
      have hbpos := (hhost b hbullet).1
      apply Fin.ext
      omega
    · intro a ha hba k hk
      exact htrail a hba k hk
  · intro q d hsector
    obtain ⟨hqp, hd⟩ := sector_unique ring N p hu q d hsector
    subst q
    rw [hd]
    rcases hv.2.2 with hempty | hfull
    · right
      refine ⟨?_, hsuffix 1 (by omega) hv.1, ?_⟩
      · intro k hk hbullet
        have hpos := (hhost k hbullet).1
        have hh := hempty.1
        have hkn := k.isLt
        omega
      · intro hready k hk hkn
        have hroot : (N p).sg = w.ready := by
          have hh := hg (zeroSite ring)
          rw [site_zero] at hh
          simpa [zeroSite] using hh
        have hr : w.ready = true := hroot.symm.trans hready
        have hcut := hempty.2.2 hr
        change (N (site ring p k)).sg = true
        rw [hg k]
        have hkzero : k.val ≠ 0 := by omega
        simp [hkzero, hcut, hk]
    · left
      let a : Fin n := ⟨w.host, hfull.1⟩
      have hbullet : HasBullet N (site ring p a) := by
        change (N (site ring p a)).b ≠ 0
        rw [hb a]
        simpa [a] using hfull.2.1
      refine ⟨a, a.isLt, hbullet, htrail a hbullet, ?_⟩
      exact hsuffix (a.val + 1) (by omega)
        (by have hh := hfull.2.2.1; dsimp [a]; omega)

private theorem candidateRight_ne {n : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n) (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  have heLt : e.val < n := e.isLt
  intro heq
  have hv : (e.val + 1) % n = e.val :=
    congrArg Fin.val heq
  by_cases hsucc : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hsucc] at hv
    omega
  · have hwrap : e.val + 1 = n := by omega
    rw [hwrap, Nat.mod_self] at hv
    omega

/-- Reindex the actual native step, then apply its finite observed-row
lemma. The coordinate word has the same two selected physical sites. -/
theorem shape_step {n : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n)
    (N : Fin n → CertNative) (e p : Fin n) (w : CleanWord)
    (hfixed : ∀ i : Fin n, (nativeE ring N e i).l = (N i).l)
    (hs : Shape ring N p w) :
    ∀ k : Fin n,
      observe (nativeE ring N e (site ring p k)) =
        wordStep n w (position ring p e).val k.val := by
  let a := position ring p e
  let j := ring.rightNeighbor a
  have hsitea : site ring p a = e := site_position ring p e
  have hsitej : site ring p j = ring.rightNeighbor e := by
    dsimp [j]
    rw [site_next, hsitea]
  have hne := candidateRight_ne hn ring e
  have hkeep :
      (certLiteralEPair (N e) (N (ring.rightNeighbor e))).2.l =
        (N (ring.rightNeighbor e)).l := by
    have hh := hfixed (ring.rightNeighbor e)
    simpa [nativeE, hne] using hh
  have hp := row_observed (N e) (N (ring.rightNeighbor e)) hkeep
  have haobs : observe (N e) = wordAt w a.val := by
    simpa only [hsitea] using hs a
  have hjobs : observe (N (ring.rightNeighbor e)) = wordAt w j.val := by
    simpa only [hsitej] using hs j
  rw [haobs, hjobs] at hp
  have hjval : j.val = if a.val + 1 < n then a.val + 1 else 0 := by
    change (a.val + 1) % n = if a.val + 1 < n then a.val + 1 else 0
    by_cases ht : a.val + 1 < n
    · simp [ht, Nat.mod_eq_of_lt ht]
    · have he : a.val + 1 = n := by have hh := a.isLt; omega
      simp [ht, he]
  intro k
  change observe (nativeE ring N e (site ring p k)) =
    wordStep n w a.val k.val
  have hout :
      observe (nativeE ring N e (site ring p k)) =
        if k.val = a.val then (observedPair (wordAt w a.val) (wordAt w j.val)).1
        else if k.val = j.val then (observedPair (wordAt w a.val) (wordAt w j.val)).2
        else wordAt w k.val := by
    by_cases hka : k.val = a.val
    · have he : k = a := Fin.ext hka
      subst k
      simp only [if_pos rfl]
      rw [hsitea]
      simpa [nativeE] using congrArg Prod.fst hp
    · by_cases hkj : k.val = j.val
      · have he : k = j := Fin.ext hkj
        subst k
        simp only [if_neg hka, if_pos rfl]
        rw [hsitej]
        simpa [nativeE, hne] using congrArg Prod.snd hp
      · simp only [if_neg hka, if_neg hkj]
        have hxe : site ring p k ≠ e := by
          intro he
          have hh := site_injective ring p k a (he.trans hsitea.symm)
          exact hka (congrArg Fin.val hh)
        have hxj : site ring p k ≠ ring.rightNeighbor e := by
          intro he
          have hh := site_injective ring p k j (he.trans hsitej.symm)
          exact hkj (congrArg Fin.val hh)
        simpa [nativeE, hxe, hxj] using hs k
  simpa only [wordStep, ← hjval] using hout

end CandidateNativeProof

/-- Root-relative normal form of a singleton clean native word (repair.tex, proof of
lem:singleton-generated-closure). For n >= 5, if `p` is the unique leader and `C_native` holds,
the native word read clockwise from `p` is described by a `CleanWord` `w`: `w.host` is the offset
of the single bullet (`w.host = n` when there is none), `w.kind` its kind (0 none, 1 dummy, 2 live),
followers carry signal one exactly at offsets `>= w.cut`, and `w.ready` is the leader's signal; a
present bullet lies before the cut and forces `ready = false`, and a bullet-free ready leader has
`cut = 1` (`WordValid`). `Shape` says the observed (leader, bullet, signal) triple at offset `k`
is `wordAt w k`. `CandidateNativeProof.nextWord_eq` and `shape_step` give how one `nativeE` edge
moves this word. -/
theorem singleton_native_normal_form {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n)
    (N : Fin n → CertNative) (p : Fin n) (hp : (N p).l = true)
    (hu : ∀ i : Fin n, (N i).l = true → i = p) (hc : C_native ring N) :
    ∃ w : CandidateNativeProof.CleanWord,
      CandidateNativeProof.WordValid n w ∧ CandidateNativeProof.Shape ring N p w :=
  CandidateNativeProof.clean_shape hn ring N p hp hu hc

/--
Native part of repair.tex, lem:singleton-generated-closure.
For every edge, a protected clean singleton remains the same singleton
and satisfies every clause of the literal Native.C_native definition.
The live shield condition is supplied by nativeE_preserves_PPlus;
the finite-cut proof handles both live and dummy bullets.
-/
theorem nativeE_preserves_singleton_C_native {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (N : Fin n → CertNative) (e : Fin n)
    (h : OneNativeLeader N ∧ C_native ring N) :
    OneNativeLeader (nativeE ring N e) ∧
      C_native ring (nativeE ring N e) := by
  obtain ⟨p, hp, hu⟩ := h.1
  have hfixed := CandidateNativeProof.leader_fixed
    (by omega : 3 ≤ n) ring N e p hp hu h.2.1.1
  obtain ⟨w, hv, hs⟩ :=
    CandidateNativeProof.clean_shape hn ring N p hp hu h.2
  let a := CandidateNativeProof.position ring p e
  have hvalid := CandidateNativeProof.nextWord_valid n hn w hv a.val a.isLt
  have hstep := CandidateNativeProof.shape_step
    (by omega : 2 ≤ n) ring N e p w hfixed.2.2 hs
  have hshape : CandidateNativeProof.Shape ring (nativeE ring N e) p
      (CandidateNativeProof.nextWord n w a.val) := by
    intro k
    exact (hstep k).trans
      (CandidateNativeProof.nextWord_eq n hn w hv a.val k.val a.isLt k.isLt)
  have hplus := nativeE_preserves_PPlus
    (by omega : 3 ≤ n) ring N e h.2.1.1
  exact ⟨⟨p, hfixed.1, hfixed.2.1⟩,
    CandidateNativeProof.shape_clean ring (nativeE ring N e) p
      hfixed.2.1 hplus (CandidateNativeProof.nextWord n w a.val)
      hvalid hshape⟩

/-- Class closure, distinct from the separate no-second-credit assertion. -/
theorem singleton_generated_class_closed {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (S : Fin n → NativeCand) (e : Fin n)
    (h : OneNativeLeader (candidateNative S) ∧
      C_native ring (candidateNative S) ∧ H_cand ring S) :
    OneNativeLeader (candidateNative (birthFreeCandidateStep ring S e)) ∧
      C_native ring (candidateNative (birthFreeCandidateStep ring S e)) ∧
      H_cand ring (birthFreeCandidateStep ring S e) := by
  have hnative := nativeE_preserves_singleton_C_native
    hn ring (candidateNative S) e ⟨h.1, h.2.1⟩
  rw [← birthFreeCandidateStep_native (by omega : 2 ≤ n) ring S e] at hnative
  exact ⟨hnative.1, hnative.2, H_cand_birthFree_step ring S e h.2.2⟩


end L3
