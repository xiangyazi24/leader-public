import Leader.L4.Statement
import Leader.L4.Payment
import Leader.L4.GeometryPair

/-!
# Deterministic closure layer for the L4 table

The walk is cut at the sole living root. Positions of the cut-open ring are
represented by their clockwise offsets, independent of patrol and stock bytes.
-/

namespace L4

private def clockwise {n : Nat} (root : Fin n) (d : Nat) : Fin n :=
  ⟨(root.val + d) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt root.isLt)⟩

private theorem clockwise_zero {n : Nat} (root : Fin n) :
    clockwise root 0 = root := by
  apply Fin.ext
  simp [clockwise, Nat.mod_eq_of_lt root.isLt]

private theorem clockwise_succ {n : Nat} (root : Fin n) (d : Nat) :
    clockwise root (d+1) = rightNeighbor (clockwise root d) := by
  apply Fin.ext
  simp [clockwise, rightNeighbor, Nat.add_assoc]

private theorem clockwise_eq_index {n : Nat} (root i : Fin n) :
    ∃ d : Nat, d < n ∧ clockwise root d = i := by
  by_cases h : root.val ≤ i.val
  · refine ⟨i.val - root.val, by omega, Fin.ext ?_⟩
    change (root.val + (i.val - root.val)) % n = i.val
    rw [show root.val + (i.val - root.val) = i.val by omega, Nat.mod_eq_of_lt i.isLt]
  · refine ⟨n - root.val + i.val, by omega, Fin.ext ?_⟩
    change (root.val + (n - root.val + i.val)) % n = i.val
    rw [show root.val + (n - root.val + i.val) = n + i.val by omega]
    simpa [Nat.add_comm] using Nat.mod_eq_of_lt i.isLt

private theorem clockwise_inj_lt {n : Nat} (root : Fin n) {i j : Nat}
    (hi : i < n) (hj : j < n) (h : clockwise root i = clockwise root j) :
    i = j := by
  have h := congrArg Fin.val h
  change (root.val + i) % n = (root.val + j) % n at h
  have hr := root.isLt
  by_cases h₁ : root.val + i < n <;> by_cases h₂ : root.val + j < n
  · rw [Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂] at h; omega
  · rw [Nat.mod_eq_of_lt h₁, Nat.mod_eq_sub_mod (by omega : n ≤ root.val + j),
        Nat.mod_eq_of_lt (by omega : root.val + j - n < n)] at h; omega
  · rw [Nat.mod_eq_sub_mod (by omega : n ≤ root.val + i),
        Nat.mod_eq_of_lt (by omega : root.val + i - n < n), Nat.mod_eq_of_lt h₂] at h; omega
  · rw [Nat.mod_eq_sub_mod (by omega : n ≤ root.val + i),
        Nat.mod_eq_of_lt (by omega : root.val + i - n < n),
        Nat.mod_eq_sub_mod (by omega : n ≤ root.val + j),
        Nat.mod_eq_of_lt (by omega : root.val + j - n < n)] at h
    omega

private theorem clockwise_full {n : Nat} (root : Fin n) :
    clockwise root n = root := by
  apply Fin.ext
  simp [clockwise, Nat.mod_eq_of_lt root.isLt]

/-- All signals from the living root through clockwise offset `d` are zero. -/
def ZeroPrefix {p c1 n : Nat} (x : Config p c1 n) (root : Fin n) (d : Nat) : Prop :=
  ∀ i : Nat, i ≤ d → (x (clockwise root i)).signal = .zero

/-- Every live bullet has the sole root shielded, with zero signal on the
entire clockwise prefix through its carrier. -/
def SoleRootPeaceful {p c1 n : Nat} (x : Config p c1 n) (root : Fin n) : Prop :=
  ∀ d : Nat, d < n → (x (clockwise root d)).bullet = .live →
    (x root).shield = true ∧ ZeroPrefix x root d

/-- Deterministic terminal invariant, including the two parts of cover used
by the full-product conclusion. Stock and rail fields remain unrestricted. -/
def TerminalAt {p c1 n : Nat} (x : Config p c1 n) (root : Fin n) : Prop :=
  UniqueLeaderAt x root ∧
  (∀ u : Fin n, (x u).mark = true ↔ rightNeighbor u = root) ∧
  (∀ u : Fin n, rightNeighbor u ≠ root →
    (x (rightNeighbor u)).residue = nextResidue (x u).residue) ∧
  (∀ v : Fin n, (x v).source ≠ .off → (x v).leader = false ∧
    ∃ u : Fin n, rightNeighbor u = v ∧ (x u).mark = true) ∧
  SoleRootPeaceful x root

/-- The covered source condition simplifies at rank one: every source is OFF. -/
theorem terminalAt_source_off {p c1 n : Nat} {x : Config p c1 n} {root : Fin n}
    (h : TerminalAt x root) (v : Fin n) : (x v).source = .off := by
  by_cases hgood : (x v).source = .off
  · exact hgood
  · exfalso
    have bad := hgood
    obtain ⟨hv, u, huv, hu⟩ := h.2.2.2.1 v bad
    have hr : v = root := huv.symm.trans ((h.2.1 u).mp hu)
    have hL := (h.1 v).mpr hr
    rw [hv] at hL
    contradiction

private theorem rightNeighbor_ne_self {n : Nat} (hn : 4 ≤ n) (e : Fin n) :
    rightNeighbor e ≠ e := by
  intro h
  have h := congrArg Fin.val h
  change (e.val + 1) % n = e.val at h
  have he := e.isLt
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at h
    omega
  · have hh : e.val + 1 = n := by omega
    rw [hh, Nat.mod_self] at h
    omega

-- The global geometry uses only these projected local equalities. It should
-- not unfold the entire stock and timer program at every ring position.
private theorem step_geometry_of_pair {p c1 n : Nat} (hn : 4 ≤ n)
    (x : Config p c1 n) (e : Fin n)
    (hLeft : let r := (pairStep (x e) (x (rightNeighbor e))).1
      r.leader = (x e).leader ∧ r.mark = (x e).mark ∧
        r.residue = (x e).residue ∧ r.source = .off)
    (hRight : let v := rightNeighbor e
      let r := (pairStep (x e) (x v)).2
      r.leader = (x v).leader ∧ r.mark = (x v).mark ∧
        r.residue = (x v).residue ∧ r.source = .off)
    (hs : ∀ v : Fin n, (x v).source = .off) :
    ∀ u : Fin n, let r := step x e u
      r.leader = (x u).leader ∧ r.mark = (x u).mark ∧
        r.residue = (x u).residue ∧ r.source = .off := by
  intro u
  by_cases hu : u = e
  · subst u
    simpa [step] using hLeft
  · by_cases hv : u = rightNeighbor e
    · subst u
      simpa [step, rightNeighbor_ne_self hn e] using hRight
    · simp [step, hu, hv, hs]

private theorem patrol_off_unpinned {Q : Nat} (root leader : Bool)
    (src : Source Q) (l r : Rail) :
    (patrol root false leader src l r).source = .off := by
  cases root <;> cases leader <;> cases src <;> cases l <;> cases r <;> rfl

private theorem finishBirth_unpinned {p c1 : Nat} (f : Bool) (u v : Site p c1)
    (h : pinned u v = false) : finishBirth f u v = (u,v) := by
  simp [finishBirth, h]

private theorem unpinned_pair_step {p c1 : Nat} (u v : Site p c1)
    (h : pinned (stepPrefix u v).1 (stepPrefix u v).2 = false) :
    pairStep u v = patrolWrite (stepPrefix u v).1 (stepPrefix u v).2
      (patrol ((stepPrefix u v).2.leader || (stepPrefix u v).1.mark) false
        (stepPrefix u v).2.leader (stepPrefix u v).2.source
        (stepPrefix u v).1.rail (stepPrefix u v).2.rail) := by
  unfold pairStep
  generalize he : stepPrefix u v = w at *
  cases w with
  | mk x y =>
    dsimp at *
    rw [h]
    apply finishBirth_unpinned
    exact h

private theorem materialize_stable {p c1 : Nat} (u v : Site p c1)
    (hm : u.mark = v.leader)
    (hc : v.leader = false → v.residue = nextResidue u.residue) :
    materialize u v = u := by
  cases hv : v.leader with
  | false => simp [materialize, hv, hm, defect, hc hv]
  | true =>
    simp [materialize, hv]
    cases u
    simp_all

private theorem fireInitiator_mark {p c1 : Nat} (u : Site p c1) :
    (fireInitiator u).mark = u.mark := by
  unfold fireInitiator
  split <;> rfl

@[simp] private theorem bullet_beq_eq (a b : Bullet) : (a == b) = true ↔ a = b := by
  cases a <;> cases b <;> decide

@[simp] private theorem signal_beq_eq (a b : Signal) : (a == b) = true ↔ a = b := by
  cases a <;> cases b <;> decide

@[simp] private theorem bullet_beq_false (a b : Bullet) : (a == b) = false ↔ a ≠ b := by
  cases a <;> cases b <;> decide

@[simp] private theorem signal_beq_false (a b : Signal) : (a == b) = false ↔ a ≠ b := by
  cases a <;> cases b <;> decide

@[simp] private theorem max_with_zero (s : Signal) : s.max .zero = s := by
  cases s <;> rfl

private def interiorNative {p c1 : Nat} (u v : Site p c1) :
    Site p c1 × Site p c1 :=
  let a := fireInitiator u
  if a.bullet == .none then ({ a with signal := a.signal.max v.signal }, v)
  else
    ({ a with bullet := .none, signal := a.signal.max .zero },
      { v with bullet := (if v.bullet == .none then a.bullet else v.bullet), signal := .zero })

private theorem native_interior {p c1 : Nat} (u v : Site p c1)
    (hu : u.mark = false) (hv : v.leader = false) :
    native u v = interiorNative u v := by
  unfold native interiorNative
  cases hb : (fireInitiator u).bullet <;>
    simp [fireResponder, impact, hv, pinned, fireInitiator_mark, hu, followerBullet, hb]

private def SameGeometry {p c1 : Nat} (u v : Site p c1) : Prop :=
  v.leader = u.leader ∧ v.mark = u.mark ∧ v.residue = u.residue ∧ v.source = .off

private structure InteriorPair {p c1 : Nat} (u v a b : Site p c1) : Prop where
  leftGeo : SameGeometry u a
  rightGeo : SameGeometry v b
  leftNoLive : a.bullet ≠ .live
  leftZero : u.signal = .zero → v.signal = .zero → a.signal = .zero
  rightZero : v.signal = .zero → b.signal = .zero
  leftKeepShield : u.shield = true → a.shield = true
  rightKeepShield : v.shield = true → b.shield = true
  rightLive : b.bullet = .live →
    v.bullet = .live ∨
      (u.bullet = .live ∧ a.signal = .zero ∧ b.signal = .zero) ∨
      (u.leader = true ∧ a.shield = true ∧ a.signal = .zero ∧ b.signal = .zero)

private theorem interiorPair_native {p c1 : Nat} (u v : Site p c1)
    (hu : u.source = .off) (hv : v.source = .off)
    (hold : u.bullet = .live → u.signal = .zero) :
    InteriorPair u v (interiorNative u v).1 (interiorNative u v).2 := by
  unfold interiorNative fireInitiator
  split
  · rename_i hfire
    have hl : u.leader = true := by simpa using (Bool.and_eq_true_iff.mp hfire).1
    constructor <;> simp [SameGeometry, hu, hv, hl, Signal.max]
  · rename_i hNoFire
    cases hb : u.bullet <;>
      constructor <;> simp [SameGeometry, hu, hv, hb, Signal.max]
    all_goals
      cases hc : v.bullet <;> simp_all


private def strip {p c1 : Nat} (a : Site p c1) : Site p c1 :=
  { a with stock := false, rail := .e }

private theorem interiorPair_strip {p c1 : Nat} (u v a b : Site p c1) :
    InteriorPair u v (strip a) (strip b) ↔ InteriorPair u v a b := by
  constructor <;> intro h <;>
    exact ⟨h.leftGeo, h.rightGeo, h.leftNoLive, h.leftZero, h.rightZero,
      h.leftKeepShield, h.rightKeepShield, h.rightLive⟩

private theorem interior_safe {p c1 : Nat} (u v : Site p c1)
    (hm : u.mark = false) (hl : v.leader = false)
    (hr : v.residue = nextResidue u.residue)
    (hu : u.source = .off) (hv : v.source = .off)
    (hold : u.bullet = .live → u.signal = .zero) :
    InteriorPair u v (pairStep u v).1 (pairStep u v).2 := by
  let s := interiorNative u v
  have hNative : InteriorPair u v s.1 s.2 := interiorPair_native u v hu hv hold
  have hsMark : s.1.mark = false := hNative.leftGeo.2.1.trans hm
  have hsLeader : s.2.leader = false := hNative.rightGeo.1.trans hl
  have hPre : stepPrefix u v = payment s.1 s.2 := by
    unfold stepPrefix
    rw [materialize_stable u v (hm.trans hl.symm) (fun _ => hr),
      native_interior u v hm hl]
  obtain ⟨hp1, hp2⟩ := payment_stock_only s.1 s.2 hsMark hsLeader
  have hm' : (stepPrefix u v).1.mark = false := by
    rw [hPre]
    exact (congrArg Site.mark hp1).trans hsMark
  have hl' : (stepPrefix u v).2.leader = false := by
    rw [hPre]
    exact (congrArg Site.leader hp2).trans hsLeader
  have hpin : pinned (stepPrefix u v).1 (stepPrefix u v).2 = false := by
    simp [pinned, hm', hl']
  have hPost1 : strip (pairStep u v).1 = strip s.1 := by
    simp only [unpinned_pair_step u v hpin, patrolWrite, hPre, strip]
    have hh := congrArg strip hp1
    exact hh
  have hPost2 : strip (pairStep u v).2 = strip s.2 := by
    rw [unpinned_pair_step u v hpin]
    simp only [patrolWrite, strip, patrol_off_unpinned, hPre]
    have hS : s.2.source = .off := hNative.rightGeo.2.2.2
    have hh := congrArg (fun a : Site p c1 => { (strip a) with source := (Source.off : Source (2 * c1)) }) hp2
    simpa [strip, hS] using hh
  apply (interiorPair_strip u v _ _).mp
  rw [hPost1, hPost2]
  exact (interiorPair_strip u v _ _).mpr hNative

-- Logical part of the blue argument, decoupled from the ring arithmetic.
-- A read through an untouched branch uses the old prefix; a new carrier uses
-- either that old prefix plus the cleared landing slot or a newly shielded root.
private def BlueSafe {p c1 : Nat} (n : Nat) (x : Nat → Site p c1) : Prop :=
  ∀ d : Nat, d < n → (x d).bullet = .live →
    (x 0).shield = true ∧ ∀ j : Nat, j ≤ d → (x j).signal = .zero

private theorem blueSafe_interior {p c1 n e : Nat} (x y : Nat → Site p c1)
    (he : e+1 < n) (old : BlueSafe n x)
    (hFrame : ∀ j, j < n → j ≠ e → j ≠ e+1 → y j = x j)
    (hNoLeft : (y e).bullet ≠ .live)
    (hLeftZero : (x e).signal = .zero → (x (e+1)).signal = .zero →
      (y e).signal = .zero)
    (hRightZero : (x (e+1)).signal = .zero → (y (e+1)).signal = .zero)
    (hShield : (x 0).shield = true → (y 0).shield = true)
    (hRightLive : (y (e+1)).bullet = .live →
      (x (e+1)).bullet = .live ∨
      ((x e).bullet = .live ∧ (y e).signal = .zero ∧ (y (e+1)).signal = .zero) ∨
      (e = 0 ∧ (y 0).shield = true ∧ (y e).signal = .zero ∧ (y (e+1)).signal = .zero)) :
    BlueSafe n y := by
  have keepPrefix : ∀ d, d < n → d ≠ e →
      (∀ j, j ≤ d → (x j).signal = .zero) →
      ∀ j, j ≤ d → (y j).signal = .zero := by
    intro d hd hne hz j hj
    by_cases hje : j = e
    · subst j
      exact hLeftZero (hz e hj) (hz (e+1) (by omega))
    · by_cases hjr : j = e+1
      · subst j
        exact hRightZero (hz (e+1) hj)
      · rw [hFrame j (by omega) hje hjr]
        exact hz j hj
  intro d hd hb
  by_cases hde : d = e
  · subst d
    exact False.elim (hNoLeft hb)
  by_cases hdr : d = e+1
  · subst d
    rcases hRightLive hb with hRetain | hMove | hFresh
    · obtain ⟨hsh, hz⟩ := old (e+1) he hRetain
      exact ⟨hShield hsh, keepPrefix (e+1) he (by omega) hz⟩
    · obtain ⟨hpre, hl, hr⟩ := hMove
      obtain ⟨hsh, hz⟩ := old e (by omega) hpre
      refine ⟨hShield hsh, ?_⟩
      intro j hj
      by_cases hje : j = e
      · simpa [hje] using hl
      by_cases hjr : j = e+1
      · simpa [hjr] using hr
      rw [hFrame j (by omega) hje hjr]
      exact hz j (by omega)
    · obtain ⟨he0, hsh, hl, hr⟩ := hFresh
      refine ⟨hsh, ?_⟩
      intro j hj
      have hcase : j = e ∨ j = e + 1 := by omega
      rcases hcase with hcase | hcase
      · simpa [hcase] using hl
      · simpa [hcase] using hr
  · rw [hFrame d hd hde hdr] at hb
    obtain ⟨hsh, hz⟩ := old d hd hb
    exact ⟨hShield hsh, keepPrefix d hd hde hz⟩

private theorem blueSafe_wrap {p c1 n e : Nat} (x y : Nat → Site p c1)
    (he : e+1 = n) (old : BlueSafe n x)
    (hFrame : ∀ j, j < n → j ≠ e → j ≠ 0 → y j = x j)
    (hNoLast : (y e).bullet ≠ .live)
    (hNewRoot : (y 0).bullet = .live → (y 0).shield = true ∧
      (y 0).signal = .zero)
    (hKeepRoot : (x 0).shield = true → (x 0).signal = .zero →
      (y 0).shield = true ∧ (y 0).signal = .zero) :
    BlueSafe n y := by
  intro d hd hb
  by_cases hde : d = e
  · subst d
    exact False.elim (hNoLast hb)
  by_cases hd0 : d = 0
  · subst d
    obtain ⟨hsh,hz⟩ := hNewRoot hb
    refine ⟨hsh, ?_⟩
    intro j hj
    have : j = 0 := by omega
    simpa [this] using hz
  · rw [hFrame d hd hde hd0] at hb
    obtain ⟨hsh,hz⟩ := old d hd hb
    obtain ⟨hsh',hz'⟩ := hKeepRoot hsh (hz 0 (by omega))
    refine ⟨hsh', ?_⟩
    intro j hj
    by_cases hj0 : j = 0
    · simpa [hj0] using hz'
    have hje : j ≠ e := by omega
    rw [hFrame j (by omega) hje hj0]
    exact hz j hj

private theorem terminalFromGeometry {p c1 n : Nat} {x y : Config p c1 n}
    {root : Fin n} (old : TerminalAt x root)
    (geom : ∀ u, SameGeometry (x u) (y u)) (blue : SoleRootPeaceful y root) :
    TerminalAt y root := by
  refine ⟨?_, ?_, ?_, ?_, blue⟩
  · intro j
    rw [(geom j).1]
    exact old.1 j
  · intro j
    rw [(geom j).2.1]
    exact old.2.1 j
  · intro j hj
    rw [(geom j).2.2.1, (geom (rightNeighbor j)).2.2.1]
    exact old.2.2.1 j hj
  · intro v bad
    exact False.elim (bad (geom v).2.2.2)

-- Form the source-to-carrier line and distinguish the single wrapping edge.
-- The native pair analysis and the prefix preservation are separate; the
-- ring proof needs only their small lists of projected invariants.
/-- The terminal product is closed under every selected directed edge.
No stock or patrol-rail condition is imposed on a protected configuration. -/
theorem terminalAt_step {p c1 n : Nat} (hn : 4 ≤ n)
    (x : Config p c1 n) (root e : Fin n) (old : TerminalAt x root) :
    TerminalAt (step x e) root := by
  obtain ⟨d, hd, he⟩ := clockwise_eq_index root e
  have hr : clockwise root (d+1) = rightNeighbor e := by rw [clockwise_succ, he]
  let f := fun j => x (clockwise root j)
  let g := fun j => step x e (clockwise root j)
  have pre : BlueSafe n f := by
    intro j hj h
    simpa [f, clockwise_zero, ZeroPrefix] using old.2.2.2.2 j hj h
  have hs := terminalAt_source_off old
  have hLeft : step x e e = (pairStep (x e) (x (rightNeighbor e))).1 := by
    simp [step]
  have hRight : step x e (rightNeighbor e) = (pairStep (x e) (x (rightNeighbor e))).2 := by
    simp [step, rightNeighbor_ne_self hn e]
  have finish (ha : SameGeometry (x e) (pairStep (x e) (x (rightNeighbor e))).1)
      (hb : SameGeometry (x (rightNeighbor e)) (pairStep (x e) (x (rightNeighbor e))).2)
      (hp : BlueSafe n g) : TerminalAt (step x e) root := by
    apply terminalFromGeometry old
    · exact step_geometry_of_pair hn x e ha hb hs
    · intro j hj h
      simpa [g, clockwise_zero, ZeroPrefix] using hp j hj h
  by_cases hwrap : d+1 = n
  · have hvRoot : rightNeighbor e = root := by rw [← hr, hwrap, clockwise_full]
    have huRoot : e ≠ root := by rw [← hvRoot]; exact Ne.symm (rightNeighbor_ne_self hn e)
    have huv : (x e).leader = false := by
      cases h : (x e).leader
      · rfl
      · exact False.elim (huRoot ((old.1 e).mp h))
    have hkill : (x e).bullet = .live →
        (x (rightNeighbor e)).signal = .zero ∧ (x (rightNeighbor e)).shield = true := by
      intro b
      obtain ⟨hsh, hp⟩ := old.2.2.2.2 d hd (by simpa [he] using b)
      simpa [hvRoot, clockwise_zero] using And.intro (hp 0 (by omega)) hsh
    have hOldBlue : (x (rightNeighbor e)).bullet = .live →
        (x (rightNeighbor e)).shield = true ∧ (x (rightNeighbor e)).signal = .zero := by
      intro b
      obtain ⟨hsh,hp⟩ := old.2.2.2.2 0 (by omega) (by simpa [clockwise_zero,hvRoot] using b)
      simpa [hvRoot, clockwise_zero] using And.intro hsh (hp 0 (by omega))
    obtain ⟨ha,hb,hNone,hLive,hKeep⟩ := incoming_safe (x e) (x (rightNeighbor e))
      huv ((old.1 _).mpr hvRoot) ((old.2.1 e).mpr hvRoot) (hs e) hkill hOldBlue
    apply finish ha hb
    apply blueSafe_wrap f g hwrap pre
    · intro j hj hje hj0
      have h₁ : clockwise root j ≠ e := fun eq => hje (clockwise_inj_lt root hj hd (eq.trans he.symm))
      have h₂ : clockwise root j ≠ rightNeighbor e := by
        intro eq
        apply hj0
        apply clockwise_inj_lt root hj (by omega)
        exact eq.trans (hvRoot.trans (clockwise_zero root).symm)
      simp [f,g,step,h₁,h₂]
    · simpa [g,he,hLeft] using hNone
    · simpa [g,clockwise_zero,← hvRoot,hRight] using hLive
    · simpa [f,g,clockwise_zero,← hvRoot,hRight] using hKeep
  · have hdi : d+1 < n := by omega
    have hvRoot : rightNeighbor e ≠ root := by
      intro hh
      have : d+1 = 0 := clockwise_inj_lt root hdi (by omega)
        (by simpa [clockwise_zero, hr] using hh)
      omega
    have huMark : (x e).mark = false := by
      cases h : (x e).mark
      · rfl
      · exact False.elim (hvRoot ((old.2.1 e).mp h))
    have hvL : (x (rightNeighbor e)).leader = false := by
      cases h : (x (rightNeighbor e)).leader
      · rfl
      · exact False.elim (hvRoot ((old.1 _).mp h))
    have hold : (x e).bullet = .live → (x e).signal = .zero := by
      intro h
      obtain ⟨_, hz⟩ := old.2.2.2.2 d hd (by simpa [he] using h)
      simpa [he] using hz d (by omega)
    have hpair := interior_safe (x e) (x (rightNeighbor e)) huMark hvL
      (old.2.2.1 e hvRoot) (hs e) (hs _) hold
    apply finish hpair.leftGeo hpair.rightGeo
    apply blueSafe_interior f g hdi pre
    · intro j hj hje hjr
      have h₁ : clockwise root j ≠ e := fun eq => hje (clockwise_inj_lt root hj hd (eq.trans he.symm))
      have h₂ : clockwise root j ≠ rightNeighbor e := fun eq =>
        hjr (clockwise_inj_lt root hj hdi (eq.trans hr.symm))
      simp [f,g,step,h₁,h₂]
    · simpa [g,he,hLeft] using hpair.leftNoLive
    · simpa [f,g,he,hr,hLeft] using hpair.leftZero
    · simpa [f,g,hr,hRight] using hpair.rightZero
    · intro h
      by_cases hRoot : root = e
      · simpa [f,g,clockwise_zero,hRoot,hLeft] using
          hpair.leftKeepShield (by simpa [f,clockwise_zero,hRoot] using h)
      · simpa [f,g,clockwise_zero,step,hRoot,Ne.symm hvRoot] using h
    · have srcIndex : (x e).leader = true → d = 0 := by
        intro h
        apply clockwise_inj_lt root hd (by omega)
        simpa [he, clockwise_zero] using (old.1 e).mp h
      intro b
      rcases hpair.rightLive (by simpa [g,hr,hRight] using b) with hRetain | hMove | hNew
      · exact Or.inl (by simpa [f,hr] using hRetain)
      · exact Or.inr (Or.inl (by simpa [f,g,he,hr,hLeft,hRight] using hMove))
      · obtain ⟨huL,hsh,hL,hR⟩ := hNew
        have hz := srcIndex huL
        have heRoot : e = root := by simpa [hz, clockwise_zero] using he.symm
        exact Or.inr (Or.inr ⟨hz,
          by simpa [g,clockwise_zero,step,heRoot] using hsh,
          by simpa [g,he,hLeft] using hL, by simpa [g,hr,hRight] using hR⟩)

/-- Every scheduler word preserves the entire terminal invariant. -/
theorem terminalAt_run {p c1 n : Nat} (hn : 4 ≤ n)
    (x : Config p c1 n) (root : Fin n) (w : List (Fin n))
    (h : TerminalAt x root) : TerminalAt (run x w) root := by
  induction w generalizing x with
  | nil => exact h
  | cons e w ih => exact ih (step x e) (terminalAt_step hn x root e h)

/-- The same sole leader survives all finite scheduler continuations from
the paper's covered, root-peaceful singleton-live domain. -/
theorem terminalAt_safeOneLeader {p c1 n : Nat} (hn : 4 ≤ n)
    (x : Config p c1 n) (root : Fin n) (h : TerminalAt x root) : SafeOneLeader x :=
  ⟨root, fun w => (terminalAt_run hn x root w h).1⟩

end L4

#print axioms L4.terminalAt_source_off
#print axioms L4.terminalAt_step
#print axioms L4.terminalAt_run
#print axioms L4.terminalAt_safeOneLeader
