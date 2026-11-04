import Leader.L3.Alphabet
import Leader.L3.CertArith
import Leader.L3.Primitive.TapSound
import Leader.L3.Primitive.ExactPeriod
import Leader.L3.Primitive.TapTable
import Leader.L3.CertRows

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-!
# Static L3 certificate relations (proof development)

The public certificate word is (leader,u,beta,d). It is exactly a
projection of Agent c; there is no new protocol-state coordinate.

Raw scanner correspondence (CertRows.rawD1Step):
* R1b/R1c launch; R0b advances a genuine sampled t-bit window;
* R0b at stage t stores beta of the last sampled site versus AND of
  those t sampled u bits, provided none of those sites is a leader;
* R0c at the following site checks OR and tap XOR of the sampled bits
  against the next u, unless a sampled or terminal leader exempts them.
  Its already stored marker mismatch is not cleared by a terminal leader.

TOP checker correspondence (CertRows.liveTopPair, QO/QI/QC):
a strict coherent comparison examines consecutive complete
marker-delimited source and target blocks, in base topA, with the
least significant digit at the marker, and checks target=source+1.
The aggregate topReject also has an OLD-dirty discharge cause, which
is NOT a static block-increment failure. Arbitrary inherited Q
terminals are not certificates of a strict comparison.

The rootless marker-cycle bridge is proved below. Rooted feasibility
is proved on the supported tap-table domain t <= 17. The unrestricted
rooted assertion for this total compiler is refuted by a zero-tap
counterexample. The additions are uncompiled.
-/

/-- Static word (l,u,beta,d), at the installed digit radix. -/
abbrev CertificateWord (n : Nat) (c : Compiled) :=
  Fin n → Bool × Bool × Bool × Fin c.topA

/-- Projection from the installed Cartesian agent alphabet. -/
def certificateWordOfAgents {n : Nat} (c : Compiled)
    (S : Fin n → Agent c) : CertificateWord n c :=
  fun i => ((S i).l, (S i).u, (S i).beta, (S i).d)

def certLeader {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (i : Fin n) : Bool := (W i).1

def certBit {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (i : Fin n) : Bool := (W i).2.1

def certMarker {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (i : Fin n) : Bool := (W i).2.2.1

def certDigit {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (i : Fin n) : Fin c.topA := (W i).2.2.2

/-- Physical site k clockwise offsets from i. -/
def certSite {n : Nat} (i : Fin n) (k : Nat) : Fin n :=
  ⟨(i.val + k) % n, Nat.mod_lt _ (by have hi := i.isLt; omega)⟩

theorem certSite_zero {n : Nat} (i : Fin n) :
    certSite i 0 = i := by
  apply Fin.ext
  change (i.val + 0) % n = i.val
  simp [Nat.mod_eq_of_lt i.isLt]

theorem certSite_n {n : Nat} (i : Fin n) :
    certSite i n = i := by
  apply Fin.ext
  change (i.val + n) % n = i.val
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

theorem certSite_add {n : Nat} (i : Fin n) (a b : Nat) :
    certSite (certSite i a) b = certSite i (a + b) := by
  apply Fin.ext
  change ((i.val + a) % n + b) % n = (i.val + (a + b)) % n
  calc
    ((i.val + a) % n + b) % n = (i.val + a + b) % n :=
      Nat.mod_add_mod _ _ _
    _ = (i.val + (a + b)) % n := by congr 1; omega

/-- The t sampled bits, in the order used by raw R0b. -/
def certWindow {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (s : Fin n) : Fin c.t → Bool :=
  fun j => certBit W (certSite s j.val)

/-- Every requisite site in the indicated clockwise arc is a follower. -/
def certFollowerArc {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (s : Fin n) (length : Nat) : Prop :=
  ∀ j : Fin length, certLeader W (certSite s j.val) = false

/-- Recurrence test at R0c (the next u after the t sampled bits).
The shift coordinates of recStep are inherent in certWindow; its
final coordinate is the literal tap-XOR feedback.  Requisite sites
are s,...,s+t, including the terminal. -/
def RecurrenceRelation {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (s : Fin n) : Prop :=
  certFollowerArc W s (c.t + 1) →
    certWindow W (certSite s 1) =
      recStep c.t c.taps (certWindow W s)

/-- Nonzero test at R0c: OR of the FIRST t bits, excluding the
terminal u.  The exemption still includes that terminal leader. -/
def NonzeroRelation {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (s : Fin n) : Prop :=
  certFollowerArc W s (c.t + 1) →
    ∃ j : Fin c.t, certWindow W s j = true

/-- Marker test at R0b stage t: beta at s+t-1 equals the AND
of sampled bits s,...,s+t-1; it does NOT require s+t to
be a follower because the marker mismatch is stored earlier. -/
def MarkerRelation {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (s : Fin n) : Prop :=
  certFollowerArc W s c.t →
    certMarker W (certSite s (c.t - 1)) =
      Fin.foldl c.t (fun acc j => acc && certWindow W s j) true

/-- Strict complete TOP comparison geometry: three consecutive
markers (source, target, terminal), two rho-site blocks with no
interior markers, and no leader among their 2*rho+1 requisite sites.
This includes the cyclic rootless self-pair when rho=n. -/
def CompleteBlockPair {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (s : Fin n) : Prop :=
  certMarker W s = true ∧
  certMarker W (certSite s c.rho) = true ∧
  certMarker W (certSite s (2 * c.rho)) = true ∧
  certFollowerArc W s (2 * c.rho + 1) ∧
  (∀ j : Fin c.rho, 0 < j.val →
    certMarker W (certSite s j.val) = false) ∧
  (∀ j : Fin c.rho, 0 < j.val →
    certMarker W (certSite (certSite s c.rho) j.val) = false)

/-- Base-a value with digit zero at the marker (little endian). -/
def certBlockValue {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (s : Fin n) : Nat :=
  Fin.foldl c.rho
    (fun z j => z + (certDigit W (certSite s j.val)).val *
      c.topA ^ j.val) 0

def certBlockId {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (s : Fin n) : Nat :=
  certBlockValue W s % (c.topA ^ c.rho)

theorem certBlockId_lt {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (s : Fin n) :
    certBlockId W s < c.topA ^ c.rho := by
  unfold certBlockId
  exact Nat.mod_lt _ (Nat.pow_pos c.topA_pos)

/-- Strict coherent Q arithmetic: target ID = source ID + 1
modulo a^rho.  An inherited TOP-dirty notification is not
an increment failure. -/
def BlockIncrementRelation {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (s : Fin n) : Prop :=
  CompleteBlockPair W s →
    certBlockId W (certSite s c.rho) =
      (certBlockId W s + 1) % (c.topA ^ c.rho)

/-- Four static relation families, each with its literal exemption
domain. They refer to genuinely sampled/raw or strictly coherent
TOP comparisons, not arbitrary inherited terminal scratch. -/
def CertificateRelations {n : Nat} {c : Compiled}
    (W : CertificateWord n c) : Prop :=
  ∀ s : Fin n,
    RecurrenceRelation W s ∧
    NonzeroRelation W s ∧
    MarkerRelation W s ∧
    BlockIncrementRelation W s

def RootlessCertificate {n : Nat} {c : Compiled}
    (W : CertificateWord n c) : Prop :=
  ∀ i : Fin n, certLeader W i = false

def RootedCertificateAt {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (h : Fin n) : Prop :=
  certLeader W h = true ∧
    ∀ i : Fin n, i ≠ h → certLeader W i = false

/-! ## Primitive recurrence on the full rootless cycle -/

private theorem certWindows_iter {n : Nat} {c : Compiled}
    (W : CertificateWord n c)
    (hRec : ∀ s : Fin n,
      certWindow W (certSite s 1) =
        recStep c.t c.taps (certWindow W s))
    (s : Fin n) (k : Nat) :
    certWindow W (certSite s k) =
      recIter c.t c.taps k (certWindow W s) := by
  induction k with
  | zero =>
      simpa only [certSite_zero, recIter_zero]
  | succ k ih =>
      calc
        certWindow W (certSite s (k + 1)) =
            certWindow W (certSite (certSite s k) 1) := by
              rw [certSite_add]
        _ = recStep c.t c.taps (certWindow W (certSite s k)) :=
          hRec _
        _ = recIter c.t c.taps (k + 1) (certWindow W s) := by
          rw [ih]
          rfl

private theorem certRecIter_add (t : Nat) (taps : Nat → Bool)
    (a b : Nat) (u : Fin t → Bool) :
    recIter t taps (a + b) u =
      recIter t taps a (recIter t taps b u) := by
  induction a with
  | zero => simp only [Nat.zero_add, recIter_zero]
  | succ a ih =>
      simpa only [Nat.succ_add, recIter_succ] using
        congrArg (recStep t taps) ih

private theorem certRecIter_mul_fixed (t : Nat) (taps : Nat → Bool)
    (r : Nat) (u : Fin t → Bool)
    (h : recIter t taps r u = u) (k : Nat) :
    recIter t taps (r * k) u = u := by
  induction k with
  | zero => rfl
  | succ k ih =>
      calc
        recIter t taps (r * (k + 1)) u =
            recIter t taps (r * k + r) u := by rw [Nat.mul_succ]
        _ = recIter t taps (r * k) (recIter t taps r u) :=
          certRecIter_add t taps _ _ u
        _ = recIter t taps (r * k) u := by rw [h]
        _ = u := ih

/-- First rootless part of prop:certificate: primitive recurrence
plus nonzero forces rho | n. This uses the primitivity of the
compiled tap table at every width `t ≥ 2` (`tapTablePrimitive`). -/
theorem certificate_rootless_period_dvd
    (n : Nat) (hn : 5 ≤ n)
    (W : CertificateWord n (compileAdvice (ceilLogTwo n)))
    (hRoot : RootlessCertificate W)
    (hRel : CertificateRelations W) :
    (compileAdvice (ceilLogTwo n)).rho ∣ n := by
  let c : Compiled := compileAdvice (ceilLogTwo n)
  let s : Fin n := ⟨0, by omega⟩
  let u : Fin c.t → Bool := certWindow W s
  have hq : 3 ≤ ceilLogTwo n := (ringQ_facts n hn).1
  have ht : 2 ≤ c.t :=
    compileAdvice_t_ge_two (ceilLogTwo n) hq
  have hp : IsPrimitive c.t c.taps := by
    exact tapTablePrimitive c.t ht
  have hRec : ∀ z : Fin n,
      certWindow W (certSite z 1) =
        recStep c.t c.taps (certWindow W z) := by
    intro z
    exact (hRel z).1 (by intro j; exact hRoot _)
  have hNonzero : ∃ j : Fin c.t, u j = true := by
    exact (hRel s).2.1 (by intro j; exact hRoot _)
  have hCyclic : recIter c.t c.taps n u = u := by
    have h := certWindows_iter W hRec s n
    rw [certSite_n] at h
    exact h.symm
  let r : Nat := c.rho
  have hrpos : 0 < r := cert_rho_pos n hn
  have hPeriod : recIter c.t c.taps r u = u :=
    (hp u hNonzero).1
  have hMultiple : recIter c.t c.taps (r * (n / r)) u = u :=
    certRecIter_mul_fixed c.t c.taps r u hPeriod _
  have hDiv : n = n % r + r * (n / r) :=
    (Nat.mod_add_div n r).symm
  have hRem : recIter c.t c.taps (n % r) u = u := by
    calc
      recIter c.t c.taps (n % r) u =
          recIter c.t c.taps (n % r)
            (recIter c.t c.taps (r * (n / r)) u) := by rw [hMultiple]
      _ = recIter c.t c.taps (n % r + r * (n / r)) u :=
        (certRecIter_add c.t c.taps _ _ u).symm
      _ = recIter c.t c.taps n u := by rw [← hDiv]
      _ = u := hCyclic
  by_cases hz : n % r = 0
  · exact Nat.dvd_of_mod_eq_zero hz
  · have hPos : 0 < n % r := by omega
    have hLt : n % r < r := Nat.mod_lt n hrpos
    exact False.elim ((hp u hNonzero).2 (n % r) hPos hLt hRem)

/-- A nonzero primitive window visits the all-ones window within
one period. This is the orbit-coverage step before marker counting. -/
theorem certificate_rootless_has_all_ones_window
    (n : Nat) (hn : 5 ≤ n)
    (W : CertificateWord n (compileAdvice (ceilLogTwo n)))
    (hRoot : RootlessCertificate W)
    (hRel : CertificateRelations W) :
    ∃ s : Fin n, certWindow W s = (fun _ => true) := by
  let c : Compiled := compileAdvice (ceilLogTwo n)
  let s : Fin n := ⟨0, by omega⟩
  let u : Fin c.t → Bool := certWindow W s
  have hq : 3 ≤ ceilLogTwo n := (ringQ_facts n hn).1
  have ht : 2 ≤ c.t :=
    compileAdvice_t_ge_two (ceilLogTwo n) hq
  have hp : IsPrimitive c.t c.taps :=
    tapTablePrimitive c.t ht
  have hRec : ∀ z : Fin n,
      certWindow W (certSite z 1) =
        recStep c.t c.taps (certWindow W z) := by
    intro z
    exact (hRel z).1 (by intro j; exact hRoot _)
  have hu : ∃ j : Fin c.t, u j = true :=
    (hRel s).2.1 (by intro j; exact hRoot _)
  have hv : ∃ j : Fin c.t, (fun _ : Fin c.t => true) j = true :=
    ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨k, _, hk⟩ :=
    isPrimitive_orbit_covers hp u (fun _ => true) hu hv
  refine ⟨certSite s k, ?_⟩
  calc
    certWindow W (certSite s k) =
        recIter c.t c.taps k u :=
      certWindows_iter W hRec s k
    _ = (fun _ => true) := hk

/-! ## The modular contradiction after marker-cycle extraction -/

/-- A cycle of m base-A identifiers cannot increase by one on
each link if 0<m<A. This uses no unspecified matrix or parser fact. -/
theorem cert_increment_cycle_impossible
    (A m : Nat) (hm : 0 < m) (hmA : m < A)
    (v : Nat → Nat) (hv : v 0 < A)
    (hStep : ∀ k : Nat, k < m →
      v (k + 1) = (v k + 1) % A)
    (hClose : v m = v 0) : False := by
  have hFormula : ∀ k : Nat, k ≤ m →
      v k = (v 0 + k) % A := by
    intro k
    induction k with
    | zero =>
        intro _
        simp [Nat.mod_eq_of_lt hv]
    | succ k ih =>
        intro hk
        calc
          v (k + 1) = (v k + 1) % A := hStep k (by omega)
          _ = ((v 0 + k) % A + 1) % A := by rw [ih (by omega)]
          _ = (v 0 + k + 1) % A := Nat.mod_add_mod _ _ _
  have hEq : v 0 = (v 0 + m) % A :=
    hClose.symm.trans (hFormula m (by omega))
  by_cases hSmall : v 0 + m < A
  · rw [Nat.mod_eq_of_lt hSmall] at hEq
    omega
  · have hGe : A ≤ v 0 + m := by omega
    have hRange : v 0 + m - A < A := by omega
    have hRed : (v 0 + m) % A = v 0 + m - A := by
      rw [Nat.mod_eq_sub_mod hGe, Nat.mod_eq_of_lt hRange]
    rw [hRed] at hEq
    omega

/-- Numeric end of prop:certificate using the earlier
cert_m_pos and cert_blocks_lt. The marker-cycle extraction below
instantiates v with consecutive strictly complete block identifiers. -/
theorem cert_installed_increment_cycle_impossible
    (n : Nat) (hn : 5 ≤ n)
    (v : Nat → Nat)
    (hv : v 0 <
      (compileAdvice (ceilLogTwo n)).topA ^
      (compileAdvice (ceilLogTwo n)).rho)
    (hStep : ∀ k : Nat,
      k < n / (compileAdvice (ceilLogTwo n)).rho →
      v (k + 1) = (v k + 1) %
        ((compileAdvice (ceilLogTwo n)).topA ^
         (compileAdvice (ceilLogTwo n)).rho))
    (hClose : v (n / (compileAdvice (ceilLogTwo n)).rho) = v 0) :
    False := by
  exact cert_increment_cycle_impossible
    ((compileAdvice (ceilLogTwo n)).topA ^
      (compileAdvice (ceilLogTwo n)).rho)
    (n / (compileAdvice (ceilLogTwo n)).rho)
    (cert_m_pos n hn) (cert_blocks_lt n hn)
    v hv hStep hClose

/-! ## Two width-two six-site controls -/

/-- Rootless recurrence-perfect 110110. Its beta is the trailing-two
all-ones marker, at residues 1 modulo 3, with all digits zero. -/
def sixCertWord : CertificateWord 6
    (compileAdvice (ceilLogTwo 6)) :=
  fun i =>
    (false, decide (i.val % 3 ≠ 2),
      decide (i.val % 3 = 1),
      ⟨0, (compileAdvice (ceilLogTwo 6)).topA_pos⟩)

theorem sixCertWidth :
    (compileAdvice (ceilLogTwo 6)).t = 2 := by
  decide +kernel




/-- One-root six-site path, relative offsets 1..5 carrying
11011. Marker flags are the trailing-two AND at offsets 2 and 5.
Every 7-site strict two-block comparison meets the root and is
therefore exempt, including under any rotation of the root. -/
def sixRootedWord (h : Fin 6) : CertificateWord 6
    (compileAdvice (ceilLogTwo 6)) :=
  fun i =>
    let k := (i.val + 6 - h.val) % 6
    (decide (k = 0),
      decide (k = 1 ∨ k = 2 ∨ k = 4 ∨ k = 5),
      decide (k = 2 ∨ k = 5),
      ⟨0, (compileAdvice (ceilLogTwo 6)).topA_pos⟩)



/-! ## Extracting the rootless marker cycle -/


private theorem certAndSplit {a b : Bool} (h : (a && b) = true) :
    a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

private theorem certAndMk {a b : Bool} (ha : a = true) (hb : b = true) :
    (a && b) = true := by
  rw [ha, hb]; rfl

private theorem certFoldAnd_acc_true_iff (t : Nat) :
    ∀ (u : Fin t → Bool) (b : Bool),
      Fin.foldl t (fun z j => z && u j) b = true ↔
        b = true ∧ ∀ j, u j = true := by
  induction t with
  | zero =>
      intro u b
      rw [Fin.foldl_zero]
      constructor
      · intro hb
        exact ⟨hb, fun j => j.elim0⟩
      · intro hb
        exact hb.1
  | succ t ih =>
      intro u b
      rw [Fin.foldl_succ, ih]
      constructor
      · intro h
        have hfirst := certAndSplit h.1
        refine ⟨hfirst.1, ?_⟩
        intro j
        exact Fin.cases hfirst.2 (fun k => h.2 k) j
      · intro h
        refine ⟨certAndMk h.1 (h.2 0), ?_⟩
        intro j
        exact h.2 j.succ

private theorem certFoldAnd_true_iff (t : Nat) (u : Fin t → Bool) :
    Fin.foldl t (fun z j => z && u j) true = true ↔
      u = (fun _ => true) := by
  rw [certFoldAnd_acc_true_iff]
  constructor
  · intro h
    funext j
    exact h.2 j
  · intro h
    exact ⟨rfl, fun j => congrFun h j⟩

private theorem cert_rootless_marker_window
    {n : Nat} {c : Compiled}
    (W : CertificateWord n c)
    (hRoot : RootlessCertificate W)
    (hRel : CertificateRelations W)
    (s : Fin n) :
    certMarker W (certSite s (c.t - 1)) = true ↔
      certWindow W s = (fun _ => true) := by
  have hm := (hRel s).2.2.1 (by intro j; exact hRoot _)
  rw [hm]
  exact certFoldAnd_true_iff c.t (certWindow W s)

/-- Exactly one true marker in each rho-site recurrence period,
with its phase chosen to be zero. This includes every period
encountered while repeatedly traversing the physical ring. -/
theorem certificate_rootless_marker_phase
    (n : Nat) (hn : 5 ≤ n)
    (W : CertificateWord n (compileAdvice (ceilLogTwo n)))
    (hRoot : RootlessCertificate W)
    (hRel : CertificateRelations W) :
    ∃ s0 : Fin n, ∀ j ell : Nat,
      ell < (compileAdvice (ceilLogTwo n)).rho →
      (certMarker W
          (certSite s0
            (j * (compileAdvice (ceilLogTwo n)).rho + ell)) = true ↔
        ell = 0) := by
  let c : Compiled := compileAdvice (ceilLogTwo n)
  have ht : 2 ≤ c.t :=
    compileAdvice_t_ge_two (ceilLogTwo n) (ringQ_facts n hn).1
  have hp : IsPrimitive c.t c.taps :=
    tapTablePrimitive c.t ht
  have hRec : ∀ z : Fin n,
      certWindow W (certSite z 1) =
        recStep c.t c.taps (certWindow W z) := by
    intro z
    exact (hRel z).1 (by intro j; exact hRoot _)
  obtain ⟨a, ha⟩ :=
    certificate_rootless_has_all_ones_window n hn W hRoot hRel
  let ones : Fin c.t → Bool := fun _ => true
  have ha' : certWindow W a = ones := ha
  have hOnes : ∃ i : Fin c.t, ones i = true :=
    ⟨⟨0, by omega⟩, rfl⟩
  have hPeriod : recIter c.t c.taps c.rho ones = ones :=
    (hp ones hOnes).1
  have hShort : ∀ k : Nat, 0 < k → k < c.rho →
      recIter c.t c.taps k ones ≠ ones :=
    (hp ones hOnes).2
  have hMultiple (j : Nat) :
      recIter c.t c.taps (j * c.rho) ones = ones := by
    rw [Nat.mul_comm j c.rho]
    exact certRecIter_mul_fixed c.t c.taps c.rho ones hPeriod j
  have hWindow (j ell : Nat) :
      certWindow W (certSite a (j * c.rho + ell)) =
        recIter c.t c.taps ell ones := by
    calc
      certWindow W (certSite a (j * c.rho + ell)) =
          recIter c.t c.taps (j * c.rho + ell)
            (certWindow W a) :=
        certWindows_iter W hRec a (j * c.rho + ell)
      _ = recIter c.t c.taps (ell + j * c.rho) ones := by
        rw [ha', Nat.add_comm (j * c.rho) ell]
      _ = recIter c.t c.taps ell
            (recIter c.t c.taps (j * c.rho) ones) :=
        certRecIter_add c.t c.taps ell (j * c.rho) ones
      _ = recIter c.t c.taps ell ones := by
        rw [hMultiple j]
  let s0 : Fin n := certSite a (c.t - 1)
  have hSite (j ell : Nat) :
      certSite s0 (j * c.rho + ell) =
        certSite (certSite a (j * c.rho + ell)) (c.t - 1) := by
    change
      certSite (certSite a (c.t - 1)) (j * c.rho + ell) =
        certSite (certSite a (j * c.rho + ell)) (c.t - 1)
    rw [certSite_add, certSite_add]
    congr 1
    omega
  have hMarkerWindow (j ell : Nat) :
      certMarker W (certSite s0 (j * c.rho + ell)) = true ↔
        recIter c.t c.taps ell ones = ones := by
    rw [hSite j ell]
    rw [cert_rootless_marker_window W hRoot hRel]
    rw [hWindow j ell]
  refine ⟨s0, ?_⟩
  intro j ell hell
  rw [hMarkerWindow j ell]
  constructor
  · intro he
    by_cases hz : ell = 0
    · exact hz
    · exact False.elim (hShort ell (by omega) hell he)
  · intro he
    subst ell
    rfl

/-- Rootless exclusion in the installed, certified tap range.
The markers delimit a closed cycle of exactly n/rho complete
blocks, each of whose identifiers must increase by one. -/
theorem certificate_rootless_exclusion
    (n : Nat) (hn : 5 ≤ n)
    (W : CertificateWord n (compileAdvice (ceilLogTwo n)))
    (hRoot : RootlessCertificate W) :
    ¬ CertificateRelations W := by
  intro hRel
  let c : Compiled := compileAdvice (ceilLogTwo n)
  obtain ⟨s0, hPhase⟩ :=
    certificate_rootless_marker_phase n hn W hRoot hRel
  have hMark (j : Nat) :
      certMarker W (certSite s0 (j * c.rho)) = true := by
    have h := (hPhase j 0 (cert_rho_pos n hn)).2 rfl
    simpa only [Nat.add_zero] using h
  have hInterior (j : Nat) (ell : Fin c.rho)
      (hell : 0 < ell.val) :
      certMarker W
        (certSite (certSite s0 (j * c.rho)) ell.val) = false := by
    cases hb : certMarker W
        (certSite (certSite s0 (j * c.rho)) ell.val) with
    | false => rfl
    | true =>
        have hm :
            certMarker W
              (certSite s0 (j * c.rho + ell.val)) = true := by
          simpa only [certSite_add] using hb
        have hz := (hPhase j ell.val ell.isLt).mp hm
        have hFalse : False := by omega
        exact False.elim hFalse
  have hStepSite (j : Nat) :
      certSite (certSite s0 (j * c.rho)) c.rho =
        certSite s0 ((j + 1) * c.rho) := by
    rw [certSite_add, Nat.add_mul, Nat.one_mul]
  have hTwoSite (j : Nat) :
      certSite (certSite s0 (j * c.rho)) (2 * c.rho) =
        certSite s0 ((j + 2) * c.rho) := by
    rw [certSite_add, Nat.add_mul]
  have hPair (j : Nat) :
      CompleteBlockPair W (certSite s0 (j * c.rho)) := by
    refine ⟨hMark j, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hStepSite j]
      exact hMark (j + 1)
    · rw [hTwoSite j]
      exact hMark (j + 2)
    · intro ell
      exact hRoot _
    · intro ell hell
      exact hInterior j ell hell
    · intro ell hell
      rw [hStepSite j]
      exact hInterior (j + 1) ell hell
  have hdvd : c.rho ∣ n :=
    certificate_rootless_period_dvd n hn W hRoot hRel
  have hWrap : (n / c.rho) * c.rho = n :=
    Nat.div_mul_cancel hdvd
  let v : Nat → Nat :=
    fun j => certBlockId W (certSite s0 (j * c.rho))
  have hStep : ∀ j : Nat, j < n / c.rho →
      v (j + 1) = (v j + 1) % (c.topA ^ c.rho) := by
    intro j _
    change
      certBlockId W (certSite s0 ((j + 1) * c.rho)) =
        (certBlockId W (certSite s0 (j * c.rho)) + 1) %
          (c.topA ^ c.rho)
    rw [← hStepSite j]
    exact (hRel (certSite s0 (j * c.rho))).2.2.2 (hPair j)
  have hClose : v (n / c.rho) = v 0 := by
    simp only [v, hWrap, Nat.zero_mul, certSite_n, certSite_zero]
  exact cert_installed_increment_cycle_impossible n hn v
    (certBlockId_lt W _) hStep hClose

/-- The little-endian base-a digits reconstruct the residue modulo a^r. -/
private theorem cert_digits_value (a r v : Nat) :
    Fin.foldl r
      (fun z j => z + ((v / a ^ j.val) % a) * a ^ j.val) 0 =
      v % a ^ r := by
  induction r with
  | zero => simp [Nat.mod_one]
  | succ r ih =>
      rw [Fin.foldl_succ_last]
      change
        Fin.foldl r
          (fun z j => z + ((v / a ^ j.val) % a) * a ^ j.val) 0 +
          ((v / a ^ r) % a) * a ^ r =
        v % a ^ (r + 1)
      rw [ih, Nat.mod_pow_succ, Nat.mul_comm ((v / a ^ r) % a) (a ^ r)]

/-! ## A rooted path in the supported tap-table range -/

private theorem certPath_fold_identity (t : Nat) (b : Bool) :
    Fin.foldl t (fun z _ => z) b = b := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simpa only [Fin.foldl_succ] using ih

private theorem certPath_iter_false
    (t : Nat) (taps : Nat → Bool) (k : Nat) :
    recIter t taps k (fun _ => false) = (fun _ => false) := by
  have hstep : recStep t taps (fun _ => false) = (fun _ => false) := by
    funext i
    unfold recStep
    split
    · rfl
    · simpa only [Bool.and_false, Bool.xor_false] using
        certPath_fold_identity t false
  induction k with
  | zero => rfl
  | succ k ih =>
      change recStep t taps (recIter t taps k (fun _ => false)) =
        (fun _ => false)
      rw [ih, hstep]

private theorem certPath_iter_mod
    (t : Nat) (taps : Nat → Bool) (r : Nat)
    (u : Fin t → Bool) (hperiod : recIter t taps r u = u)
    (k : Nat) :
    recIter t taps k u = recIter t taps (k % r) u := by
  calc
    recIter t taps k u =
        recIter t taps (k % r + r * (k / r)) u := by
          rw [Nat.mod_add_div]
    _ = recIter t taps (k % r)
          (recIter t taps (r * (k / r)) u) :=
      certRecIter_add t taps _ _ u
    _ = recIter t taps (k % r) u := by
      rw [certRecIter_mul_fixed t taps r u hperiod]

private theorem certPath_nonzero_of_return
    (t : Nat) (taps : Nat → Bool) (M k : Nat)
    (u : Fin t → Bool) (hk : k ≤ M)
    (hM : recIter t taps M u = u)
    (hu : ∃ i, u i = true) :
    ∃ i, recIter t taps k u i = true := by
  classical
  by_cases hnz : ∃ i, recIter t taps k u i = true
  · exact hnz
  · have hzero : recIter t taps k u = (fun _ => false) := by
      funext i
      cases hb : recIter t taps k u i with
      | false => rfl
      | true => exact False.elim (hnz ⟨i, hb⟩)
    have hsum : M - k + k = M := Nat.sub_add_cancel hk
    have hzeroU : u = (fun _ => false) := by
      calc
        u = recIter t taps M u := hM.symm
        _ = recIter t taps (M - k + k) u := by rw [hsum]
        _ = recIter t taps (M - k) (recIter t taps k u) :=
          certRecIter_add t taps _ _ u
        _ = recIter t taps (M - k) (fun _ => false) := by rw [hzero]
        _ = (fun _ => false) := certPath_iter_false t taps _
    obtain ⟨i, hi⟩ := hu
    have hbad : false = true :=
      (congrFun hzeroU.symm i).trans hi
    cases hbad

private theorem certPath_iter_nonzero
    (c : Compiled) (ht : 0 < c.t) (hr : 0 < c.rho)
    (hp : IsPrimitive c.t c.taps) (k : Nat) :
    ∃ i, recIter c.t c.taps k (fun _ => true) i = true := by
  have hu : ∃ i : Fin c.t, (fun _ : Fin c.t => true) i = true :=
    ⟨⟨0, ht⟩, rfl⟩
  have hperiod : recIter c.t c.taps c.rho (fun _ => true) =
      (fun _ => true) := (hp _ hu).1
  rw [certPath_iter_mod c.t c.taps c.rho _ hperiod]
  exact certPath_nonzero_of_return c.t c.taps c.rho (k % c.rho)
    (fun _ => true) (Nat.le_of_lt (Nat.mod_lt _ hr)) hperiod hu

private theorem certPath_iter_ones_iff
    (c : Compiled) (ht : 0 < c.t) (hr : 0 < c.rho)
    (hp : IsPrimitive c.t c.taps) (k : Nat) :
    recIter c.t c.taps k (fun _ => true) = (fun _ => true) ↔
      k % c.rho = 0 := by
  have hu : ∃ i : Fin c.t, (fun _ : Fin c.t => true) i = true :=
    ⟨⟨0, ht⟩, rfl⟩
  have hperiod : recIter c.t c.taps c.rho (fun _ => true) =
      (fun _ => true) := (hp _ hu).1
  rw [certPath_iter_mod c.t c.taps c.rho _ hperiod]
  constructor
  · intro hreturn
    by_cases hz : k % c.rho = 0
    · exact hz
    · exact False.elim
        ((hp _ hu).2 (k % c.rho) (by omega)
          (Nat.mod_lt _ hr) hreturn)
  · intro hz
    rw [hz, recIter_zero]

private theorem certPath_iter_coordinate
    (t : Nat) (taps : Nat → Bool) (u : Fin t → Bool)
    (k : Nat) :
    ∀ (i : Nat) (hi : i + k < t),
      recIter t taps k u ⟨i, by omega⟩ = u ⟨i + k, hi⟩ := by
  induction k with
  | zero =>
      intro i hi
      rfl
  | succ k ih =>
      intro i hi
      have hnext : i + 1 < t := by omega
      change recStep t taps (recIter t taps k u) ⟨i, by omega⟩ =
        u ⟨i + (k + 1), hi⟩
      rw [recStep, dif_pos hnext]
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (i + 1) (by omega)

/-- The root is coordinate zero. Follower coordinates start at one.
The first full all-ones window ends at t; later markers are t modulo rho.
Digits store the successive block number in little-endian base topA. -/
private def certPathWord (n : Nat) (c : Compiled)
    (ht : 0 < c.t) : CertificateWord n c :=
  fun i =>
    (decide (i.val = 0),
      recIter c.t c.taps (i.val - 1) (fun _ => true) ⟨0, ht⟩,
      decide (c.t ≤ i.val ∧ (i.val - c.t) % c.rho = 0),
      ⟨((i.val - c.t) / c.rho /
          c.topA ^ ((i.val - c.t) % c.rho)) % c.topA,
        Nat.mod_lt _ c.topA_pos⟩)

private theorem certPath_arc_bounds
    (n : Nat) (c : Compiled) (ht : 0 < c.t)
    (s : Fin n) (length : Nat) (hpos : 0 < length)
    (ha : certFollowerArc (certPathWord n c ht) s length) :
    0 < s.val ∧ s.val + length ≤ n := by
  have hz := ha ⟨0, hpos⟩
  rw [certSite_zero] at hz
  change decide (s.val = 0) = false at hz
  have hsne : s.val ≠ 0 := of_decide_eq_false hz
  refine ⟨by omega, ?_⟩
  by_cases hbound : s.val + length ≤ n
  · exact hbound
  · have hj : n - s.val < length := by omega
    have hh := ha ⟨n - s.val, hj⟩
    change decide ((s.val + (n - s.val)) % n = 0) = false at hh
    have he : s.val + (n - s.val) = n := by
      have hs := s.isLt
      omega
    rw [he, Nat.mod_self] at hh
    cases hh

private theorem certPath_window
    (n : Nat) (c : Compiled) (ht : 0 < c.t)
    (s : Fin n) (hs : 0 < s.val) (hend : s.val + c.t ≤ n) :
    certWindow (certPathWord n c ht) s =
      recIter c.t c.taps (s.val - 1) (fun _ => true) := by
  funext j
  change
    recIter c.t c.taps ((s.val + j.val) % n - 1)
      (fun _ => true) ⟨0, ht⟩ =
    recIter c.t c.taps (s.val - 1) (fun _ => true) j
  have hlt : s.val + j.val < n := by
    have hj := j.isLt
    omega
  rw [Nat.mod_eq_of_lt hlt]
  have he : s.val + j.val - 1 = j.val + (s.val - 1) := by omega
  rw [he, certRecIter_add]
  have hc := certPath_iter_coordinate c.t c.taps
    (recIter c.t c.taps (s.val - 1) (fun _ => true))
    j.val 0 (by have hj := j.isLt; omega)
  simpa only [Nat.zero_add] using hc

private theorem certPath_blockId
    (n : Nat) (c : Compiled) (ht : 0 < c.t)
    (s : Fin n) (hstart : c.t ≤ s.val)
    (hmod : (s.val - c.t) % c.rho = 0)
    (hr : 0 < c.rho) (hend : s.val + c.rho ≤ n) :
    certBlockId (certPathWord n c ht) s =
      ((s.val - c.t) / c.rho) % (c.topA ^ c.rho) := by
  have hd : ∀ j : Fin c.rho,
      (certDigit (certPathWord n c ht) (certSite s j.val)).val =
        (((s.val - c.t) / c.rho) / c.topA ^ j.val) % c.topA := by
    intro j
    change
      (((s.val + j.val) % n - c.t) / c.rho /
        c.topA ^ (((s.val + j.val) % n - c.t) % c.rho)) % c.topA =
      (((s.val - c.t) / c.rho) / c.topA ^ j.val) % c.topA
    have hlt : s.val + j.val < n := by
      have hj := j.isLt
      omega
    rw [Nat.mod_eq_of_lt hlt]
    have he : s.val + j.val - c.t = (s.val - c.t) + j.val := by omega
    rw [he]
    have hrem : ((s.val - c.t) + j.val) % c.rho = j.val := by
      simp [Nat.add_mod, hmod, Nat.mod_eq_of_lt j.isLt]
    have hmul : s.val - c.t =
        ((s.val - c.t) / c.rho) * c.rho := by
      have hx := Nat.mod_add_div (s.val - c.t) c.rho
      rw [hmod, Nat.zero_add] at hx
      simpa only [Nat.mul_comm] using hx.symm
    have hdiv : ((s.val - c.t) + j.val) / c.rho =
        (s.val - c.t) / c.rho := by
      calc
        ((s.val - c.t) + j.val) / c.rho =
            (((s.val - c.t) / c.rho) * c.rho + j.val) / c.rho :=
          congrArg (fun x => (x + j.val) / c.rho) hmul
        _ = j.val / c.rho + (s.val - c.t) / c.rho := by
          rw [Nat.add_comm (((s.val - c.t) / c.rho) * c.rho) j.val,
            Nat.add_mul_div_right j.val ((s.val - c.t) / c.rho) hr]
        _ = (s.val - c.t) / c.rho := by
          rw [Nat.div_eq_of_lt j.isLt, Nat.zero_add]
    rw [hdiv, hrem]
  have hf :
      (fun (z : Nat) (j : Fin c.rho) =>
        z + (certDigit (certPathWord n c ht) (certSite s j.val)).val *
          c.topA ^ j.val) =
      (fun (z : Nat) (j : Fin c.rho) =>
        z + ((((s.val - c.t) / c.rho) / c.topA ^ j.val) % c.topA) *
          c.topA ^ j.val) := by
    funext z j
    rw [hd j]
  unfold certBlockId certBlockValue
  rw [hf, cert_digits_value, Nat.mod_mod]

private theorem certificate_rooted_zero_supported
    (n : Nat) (hn : 5 ≤ n)
    :
    ∃ W : CertificateWord n (compileAdvice (ceilLogTwo n)),
      RootedCertificateAt W ⟨0, by omega⟩ ∧ CertificateRelations W := by
  let c : Compiled := compileAdvice (ceilLogTwo n)
  have htge : 2 ≤ c.t :=
    compileAdvice_t_ge_two (ceilLogTwo n) (ringQ_facts n hn).1
  have ht : 0 < c.t := by omega
  have hr : 0 < c.rho := cert_rho_pos n hn
  have hp : IsPrimitive c.t c.taps :=
    tapTablePrimitive c.t htge
  let W : CertificateWord n c := certPathWord n c ht
  refine ⟨W, ?_, ?_⟩
  · constructor
    · rfl
    · intro i hi
      have hv : i.val ≠ 0 := by
        intro hz
        apply hi
        exact Fin.ext hz
      change decide (i.val = 0) = false
      simp [hv]
  · intro s
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro ha
      obtain ⟨hs, hend⟩ :=
        certPath_arc_bounds n c ht s (c.t + 1) (by omega) ha
      have hsite : (certSite s 1).val = s.val + 1 := by
        change (s.val + 1) % n = s.val + 1
        exact Nat.mod_eq_of_lt (by omega)
      have hwindow := certPath_window n c ht s hs (by omega)
      have hnext := certPath_window n c ht (certSite s 1)
        (by rw [hsite]; omega) (by rw [hsite]; omega)
      change certWindow (certPathWord n c ht) (certSite s 1) =
        recStep c.t c.taps (certWindow (certPathWord n c ht) s)
      rw [hnext, hwindow, hsite]
      have he : s.val + 1 - 1 = (s.val - 1) + 1 := by omega
      rw [he, recIter_succ]
    · intro ha
      obtain ⟨hs, hend⟩ :=
        certPath_arc_bounds n c ht s (c.t + 1) (by omega) ha
      change ∃ j : Fin c.t, certWindow (certPathWord n c ht) s j = true
      rw [certPath_window n c ht s hs (by omega)]
      exact certPath_iter_nonzero c ht hr hp (s.val - 1)
    · intro ha
      obtain ⟨hs, hend⟩ := certPath_arc_bounds n c ht s c.t ht ha
      have hsite : (certSite s (c.t - 1)).val = s.val + (c.t - 1) := by
        change (s.val + (c.t - 1)) % n = s.val + (c.t - 1)
        exact Nat.mod_eq_of_lt (by omega)
      have hwindow := certPath_window n c ht s hs hend
      change
        decide (c.t ≤ (certSite s (c.t - 1)).val ∧
          ((certSite s (c.t - 1)).val - c.t) % c.rho = 0) =
        Fin.foldl c.t
          (fun z j => z && certWindow (certPathWord n c ht) s j) true
      rw [hsite, hwindow]
      have he : s.val + (c.t - 1) - c.t = s.val - 1 := by omega
      have hge : c.t ≤ s.val + (c.t - 1) := by omega
      rw [he]
      simp only [hge, true_and]
      have heq :
          (decide ((s.val - 1) % c.rho = 0) = true) ↔
          (Fin.foldl c.t
            (fun z j => z &&
              recIter c.t c.taps (s.val - 1) (fun _ => true) j) true = true) := by
        rw [decide_eq_true_eq, certFoldAnd_true_iff]
        exact (certPath_iter_ones_iff c ht hr hp (s.val - 1)).symm
      cases hl : decide ((s.val - 1) % c.rho = 0) <;>
        cases hf : Fin.foldl c.t
          (fun z j => z &&
            recIter c.t c.taps (s.val - 1) (fun _ => true) j) true <;>
        simp [hl, hf] at heq ⊢
    · intro hb
      obtain ⟨hs, hend⟩ :=
        certPath_arc_bounds n c ht s (2 * c.rho + 1)
          (by omega) hb.2.2.2.1
      have hmarkB : decide
          (c.t ≤ s.val ∧ (s.val - c.t) % c.rho = 0) = true := hb.1
      have hmark := of_decide_eq_true hmarkB
      have hnextB : decide
          (c.t ≤ (certSite s c.rho).val ∧
            ((certSite s c.rho).val - c.t) % c.rho = 0) = true := hb.2.1
      have hmarkNext := of_decide_eq_true hnextB
      have hsite : (certSite s c.rho).val = s.val + c.rho := by
        change (s.val + c.rho) % n = s.val + c.rho
        exact Nat.mod_eq_of_lt (by omega)
      have hsourceId := certPath_blockId n c ht s
        hmark.1 hmark.2 hr (by omega)
      have htargetId := certPath_blockId n c ht (certSite s c.rho)
        hmarkNext.1 hmarkNext.2 hr (by rw [hsite]; omega)
      change certBlockId (certPathWord n c ht) (certSite s c.rho) =
        (certBlockId (certPathWord n c ht) s + 1) % (c.topA ^ c.rho)
      rw [htargetId, hsourceId, hsite]
      have he : s.val + c.rho - c.t = (s.val - c.t) + c.rho := by omega
      rw [he, Nat.add_div_right (s.val - c.t) hr]
      exact (Nat.mod_add_mod ((s.val - c.t) / c.rho) (c.topA ^ c.rho) 1).symm

/-- Rotation preserves all four relations, including their requisite arcs. -/
private theorem cert_rooted_rotate {n : Nat} {c : Compiled}
    (hn : 0 < n) (h : Fin n)
    (Wzero : CertificateWord n c)
    (hRoot : RootedCertificateAt Wzero ⟨0, hn⟩)
    (hRel : CertificateRelations Wzero) :
    ∃ W : CertificateWord n c,
      RootedCertificateAt W h ∧ CertificateRelations W := by
  let rot : Fin n → Fin n := fun i => certSite i (n - h.val)
  let W : CertificateWord n c := fun i => Wzero (rot i)
  have hBack (i : Fin n) : certSite (rot i) h.val = i := by
    dsimp [rot]
    rw [certSite_add, Nat.sub_add_cancel (Nat.le_of_lt h.isLt),
      certSite_n]
  have hAt : rot h = ⟨0, hn⟩ := by
    apply Fin.ext
    change (h.val + (n - h.val)) % n = 0
    rw [Nat.add_sub_of_le (Nat.le_of_lt h.isLt), Nat.mod_self]
  have hSite (s : Fin n) (k : Nat) :
      rot (certSite s k) = certSite (rot s) k := by
    dsimp [rot]
    rw [certSite_add, certSite_add, Nat.add_comm k (n - h.val)]
  have hWindow (s : Fin n) :
      certWindow W s = certWindow Wzero (rot s) := by
    funext j
    change certBit Wzero (rot (certSite s j.val)) =
      certBit Wzero (certSite (rot s) j.val)
    rw [hSite]
  have hArc (s : Fin n) (len : Nat) :
      certFollowerArc W s len →
        certFollowerArc Wzero (rot s) len := by
    intro ha j
    have hj := ha j
    change certLeader Wzero (rot (certSite s j.val)) = false at hj
    simpa only [hSite] using hj
  have hPair (s : Fin n) (hp : CompleteBlockPair W s) :
      CompleteBlockPair Wzero (rot s) := by
    simpa only [CompleteBlockPair, certMarker, certFollowerArc,
      certLeader, W, hSite] using hp
  have hId (s : Fin n) :
      certBlockId W s = certBlockId Wzero (rot s) := by
    simp only [certBlockId, certBlockValue, certDigit, W, hSite]
  refine ⟨W, ?_, ?_⟩
  · constructor
    · change certLeader Wzero (rot h) = true
      rw [hAt]
      exact hRoot.1
    · intro i hi
      change certLeader Wzero (rot i) = false
      apply hRoot.2
      intro heq
      apply hi
      have hrot : rot i = rot h := heq.trans hAt.symm
      calc
        i = certSite (rot i) h.val := (hBack i).symm
        _ = certSite (rot h) h.val := by rw [hrot]
        _ = h := hBack h
  · intro s
    have hs := hRel (rot s)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro ha
      calc
        certWindow W (certSite s 1) =
            certWindow Wzero (rot (certSite s 1)) := hWindow _
        _ = certWindow Wzero (certSite (rot s) 1) := by rw [hSite]
        _ = recStep c.t c.taps (certWindow Wzero (rot s)) :=
          hs.1 (hArc s _ ha)
        _ = recStep c.t c.taps (certWindow W s) := by rw [hWindow]
    · intro ha
      obtain ⟨j, hj⟩ := hs.2.1 (hArc s _ ha)
      refine ⟨j, ?_⟩
      rw [hWindow]
      exact hj
    · intro ha
      calc
        certMarker W (certSite s (c.t - 1)) =
            certMarker Wzero (certSite (rot s) (c.t - 1)) := by
          change certMarker Wzero (rot (certSite s (c.t - 1))) = _
          rw [hSite]
        _ = Fin.foldl c.t
            (fun acc j => acc && certWindow Wzero (rot s) j) true :=
          hs.2.2.1 (hArc s _ ha)
        _ = Fin.foldl c.t
            (fun acc j => acc && certWindow W s j) true := by
          rw [hWindow]
    · intro hp
      calc
        certBlockId W (certSite s c.rho) =
            certBlockId Wzero (rot (certSite s c.rho)) := hId _
        _ = certBlockId Wzero (certSite (rot s) c.rho) := by rw [hSite]
        _ = (certBlockId Wzero (rot s) + 1) % (c.topA ^ c.rho) :=
          hs.2.2.2 (hPair s hp)
        _ = (certBlockId W s + 1) % (c.topA ^ c.rho) := by rw [hId]

/-- Rooted feasibility at every ring size, from the primitive compiled tap table. -/
theorem certificate_rooted_feasible_supported
    (n : Nat) (hn : 5 ≤ n)
    (h : Fin n) :
    ∃ W : CertificateWord n (compileAdvice (ceilLogTwo n)),
      RootedCertificateAt W h ∧ CertificateRelations W := by
  obtain ⟨W, hRoot, hRel⟩ :=
    certificate_rooted_zero_supported n hn
  exact cert_rooted_rotate (by omega) h W hRoot hRel

/-! ## Zero feedback taps cannot satisfy the rooted relations -/

private theorem cert_obstruction_fold_identity (t : Nat) (b : Bool) :
    Fin.foldl t (fun x _ => x) b = b := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simpa only [Fin.foldl_succ] using ih

private theorem cert_obstruction_site_ne {n : Nat}
    (h : Fin n) (k : Nat) (hk : 0 < k) (hkn : k < n) :
    certSite h k ≠ h := by
  intro he
  have hv : (h.val + k) % n = h.val := congrArg Fin.val he
  have hh := h.isLt
  by_cases hsmall : h.val + k < n
  · rw [Nat.mod_eq_of_lt hsmall] at hv
    omega
  · have hge : n ≤ h.val + k := by omega
    have hlt : h.val + k - n < n := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt] at hv
    omega

private theorem cert_obstruction_forward_arc {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (h : Fin n)
    (hRoot : RootedCertificateAt W h)
    (a length : Nat) (ha : 0 < a) (hEnd : a + length ≤ n) :
    certFollowerArc W (certSite h a) length := by
  intro j
  rw [certSite_add]
  apply hRoot.2 _
  apply cert_obstruction_site_ne h (a + j.val)
  · omega
  · have hj := j.isLt
    omega

/-- With zero feedback taps, a long follower path cannot satisfy
both recurrence and nonzero tests. This is independent of markers
and block digits. -/
theorem certificate_rooted_zero_taps_impossible
    {n : Nat} {c : Compiled}
    (ht : 0 < c.t) (hSize : 2 * c.t + 2 ≤ n)
    (hTaps : ∀ j : Nat, c.taps j = false)
    (h : Fin n) (W : CertificateWord n c)
    (hRoot : RootedCertificateAt W h) :
    ¬ CertificateRelations W := by
  intro hRel
  have hArc :
      certFollowerArc W (certSite h (c.t + 1)) (c.t + 1) :=
    cert_obstruction_forward_arc W h hRoot
      (c.t + 1) (c.t + 1) (by omega) (by omega)
  obtain ⟨j, hj⟩ := (hRel (certSite h (c.t + 1))).2.1 hArc
  have hJ := j.isLt
  have hzArc :
      certFollowerArc W (certSite h (j.val + 1)) (c.t + 1) :=
    cert_obstruction_forward_arc W h hRoot
      (j.val + 1) (c.t + 1) (by omega) (by omega)
  have hRec := (hRel (certSite h (j.val + 1))).1 hzArc
  let last : Fin c.t := ⟨c.t - 1, by omega⟩
  have hLast : last.val = c.t - 1 := rfl
  have hEnd := congrFun hRec last
  have hFeedback :
      recStep c.t c.taps
        (certWindow W (certSite h (j.val + 1))) last = false := by
    unfold recStep
    have hnot : ¬ last.val + 1 < c.t := by omega
    rw [dif_neg hnot]
    simp only [hTaps, Bool.false_and, Bool.xor_false]
    exact cert_obstruction_fold_identity c.t false
  rw [hFeedback] at hEnd
  change certBit W
    (certSite (certSite (certSite h (j.val + 1)) 1) last.val) = false
    at hEnd
  have hsite :
      certSite (certSite (certSite h (j.val + 1)) 1) last.val =
        certSite (certSite h (c.t + 1)) j.val := by
    simp only [certSite_add]
    rw [hLast]
    congr 1
    omega
  rw [hsite] at hEnd
  change certBit W (certSite (certSite h (c.t + 1)) j.val) = true at hj
  rw [hEnd] at hj
  cases hj

end L3
