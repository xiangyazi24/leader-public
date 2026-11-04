import Leader.L3.Bank.FinishClean

/-!
R10 request stage on the drain (repair.tex 5374-5380): from
`BankPostInheritedGrantDrain ∧ BankRepairDebtCleared`, every request
reaches the protected root within n² expected interactions
(two half-units).

On the drain every grant bit is false, so there is no FIRE and no HOLD.
DebtCleared gives QReader, QDigit and zero debt, so every OLD pair runs
the quiet DCC row D2 and produces no request.  The literal E step never
creates a leader, so the unique leader p is fixed along the drain.
Hence on edge (e, e+1): the initiator's request leaves e, it lands on
e+1 unless e = p (absorbed by the source leader) or e+1 = p (sunk by
the destination leader), and no other site changes.  Requests move only
clockwise toward p.

Potential: the largest clockwise distance to p among request sites
(p itself counts n).  It never increases, and the edge out of its
unique argmax site lowers it by one.  Scaled by n it has drift one,
and it starts at most n², which is the two half-unit budget.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-! ## Token rows without grants, FIRE or produced requests -/

/-- The initiator always leaves with no request.
Consumer: `bankRequestCloseMaskedPair`. -/
theorem bankRequestCloseTokenSource {c : Compiled} (x y : Agent c)
    (fX fY : CertNative) (b : Bool)
    (hgx : x.grant = false) (hgy : y.grant = false) :
    (tokenStep x y fX fY none false b).1.req = false := by
  cases hxr : x.req <;> cases hyr : y.req <;> cases hfx : fX.l <;>
    cases hfy : fY.l <;> cases hb : b <;>
    simp [tokenStep, hgx, hgy, hxr, hyr, hfx, hfy] <;>
    (repeat' split) <;> simp_all

/-- The responder keeps or receives a request exactly when it is not a
final leader.  Consumer: `bankRequestCloseMaskedPair`. -/
theorem bankRequestCloseTokenDestination {c : Compiled} (x y : Agent c)
    (fX fY : CertNative) (b la lb : Bool)
    (hgx : x.grant = false) (hgy : y.grant = false)
    (hfa : fX.l = la) (hfb : fY.l = lb) :
    (tokenStep x y fX fY none false b).2.1.req =
      (!lb && (y.req || (x.req && !la))) := by
  subst hfa hfb
  cases hxr : x.req <;> cases hyr : y.req <;> cases hfx : fX.l <;>
    cases hfy : fY.l <;> cases hb : b <;>
    simp [tokenStep, hgx, hgy, hxr, hyr, hfx, hfy] <;>
    (repeat' split) <;> simp_all

/-- One masked pair on a grant-free, debt-free, quiet edge, in both
masking branches.  Consumer: `bankRequestCloseStep`. -/
theorem bankRequestCloseMaskedPair (c : Compiled) (s : Bool) (x y : Agent c)
    (hgx : x.grant = false) (hgy : y.grant = false)
    (hEUx : x.EU = false) (hEDx : x.ED = false)
    (hEUy : y.EU = false) (hEDy : y.ED = false)
    (hev : (certificateStep c x y).2.2 = Closure.readerDigitQuietEvent)
    (hl1 : (transition c x y).1.l =
      (certLiteralEPair x.certNative y.certNative).1.l)
    (hl2 : (transition c x y).2.l =
      (certLiteralEPair x.certNative y.certNative).2.l) :
    (renewalMaskedPair c s x y).1.req = false ∧
      (renewalMaskedPair c s x y).2.req =
        (!(certLiteralEPair x.certNative y.certNative).2.l &&
          (y.req || (x.req && !x.l))) := by
  have hfire : oldFire x y = none := by
    simp [oldFire, fireSelect, hgx, hgy]
  have hsel : ∀ a b : CertNative, fireSelect x y a b = none := by
    intro a b
    simp [fireSelect, hgx, hgy]
  have hdcc := Closure.dccQuietRow x y _ hEUx hEDx hEUy hEDy hev
  cases s with
  | false =>
      rw [renewalMaskedPairOff]
      constructor
      · rw [Closure.transitionRequestSourceFormula,
          Closure.baseStepRequestSourceFormula, hfire, hdcc]
        exact bankRequestCloseTokenSource x y _ _ _ hgx hgy
      · rw [Closure.transitionRequestDestinationFormula,
          Closure.baseStepRequestDestinationFormula, hfire, hdcc]
        refine bankRequestCloseTokenDestination x y _ _ _ _ _ hgx hgy ?_ ?_
        · show (if fireAtSite (oldFire x y) .siteX then firedNative
            else (certLiteralEPair x.certNative y.certNative).1).l = x.l
          rw [hfire]
          rfl
        · show (if fireAtSite (oldFire x y) .siteY then firedNative
            else (certLiteralEPair x.certNative y.certNative).2).l = _
          rw [hfire]
          rfl
  | true =>
      show (renewalNoNewGrantTokens c x y).1.req = false ∧
        (renewalNoNewGrantTokens c x y).2.1.req = _
      unfold renewalNoNewGrantTokens
      rw [hsel, hdcc]
      constructor
      · exact bankRequestCloseTokenSource x y _ _ _ hgx hgy
      · refine bankRequestCloseTokenDestination x y _ _ _ _ _ hgx hgy ?_ ?_
        · show (transition c x y).1.l = x.l
          rw [hl1]
          rfl
        · exact hl2

/-! ## One reference edge on the request class -/

/-- One masked BANK edge from a drain DebtCleared state: the initiator
leaves with no request, the responder's request is
`!l' ∧ (req_j ∨ (req_e ∧ !l_e))`, and every other site is unchanged.
Consumer: `bankRequestCloseFrontStep`. -/
theorem bankRequestCloseStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hD : BankPostInheritedGrantDrain ring hbank z)
    (hC : BankRepairDebtCleared ring hbank z) (e : Fin n) :
    ((bankRepairNext ring hbank z e).val.1 e).req = false ∧
      ((bankRepairNext ring hbank z e).val.1 (ring.rightNeighbor e)).req =
        (!((bankRepairNext ring hbank z e).val.1 (ring.rightNeighbor e)).l &&
          ((z.val.1 (ring.rightNeighbor e)).req ||
            ((z.val.1 e).req && !(z.val.1 e).l))) ∧
      (∀ i : Fin n, i ≠ e → i ≠ ring.rightNeighbor e →
        (bankRepairNext ring hbank z e).val.1 i = z.val.1 i) := by
  have hne := clockNeighborDifferent ring (by omega) e
  have hQReader : AcceptedReceipts.QReader ring (piR z.val.1) :=
    AcceptedReceipts.accepted_reader_qreader ring
      (AcceptedReceipts.AcceptedWord ring
        (BlockA.wordT ring) (BlockA.wordValidated ring))
      (Closure.readerFoldValid (ceilLogTwo n) n)
      (piR z.val.1) hC.1.1.2
  have hQDigit : AcceptedReceipts.QDigit ring (piD z.val.1) :=
    AcceptedReceipts.barred_digit_qdigit ring
      (AcceptedReceipts.AcceptedWordAtRoot ring
        (BlockA.wordT ring) (BlockA.wordValidated ring))
      (piD z.val.1) hC.1.2
  have hev := Closure.certificateEventQuietFromSafe
    (by omega) ring z.val.1 e hQReader hQDigit
  have hg := hD.1.2
  have hdebt := hC.2
  have hnative := bankAfterGrantDrainNativeStep ring hn hbank z hD.1 e
  change nativeProjection (bankRepairNext ring hbank z e).val.1 =
    nativeE ring (nativeProjection z.val.1) e at hnative
  have hstep : ∀ i : Fin n, (bankRepairNext ring hbank z e).val.1 i =
      (if i = e then
        (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          (renewalBankCut ring z.val.1 z.val.2 e)
          (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).1
       else if i = ring.rightNeighbor e then
        (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          (renewalBankCut ring z.val.1 z.val.2 e)
          (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).2
       else z.val.1 i) := fun i => rfl
  have hxe : (bankRepairNext ring hbank z e).val.1 e =
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalBankCut ring z.val.1 z.val.2 e)
        (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).1 :=
    (hstep e).trans (if_pos rfl)
  have hxj : (bankRepairNext ring hbank z e).val.1 (ring.rightNeighbor e) =
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalBankCut ring z.val.1 z.val.2 e)
        (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).2 :=
    (hstep (ring.rightNeighbor e)).trans ((if_neg hne).trans (if_pos rfl))
  have hNe : nativeE ring (nativeProjection z.val.1) e e =
      (certLiteralEPair (z.val.1 e).certNative
        (z.val.1 (ring.rightNeighbor e)).certNative).1 := by
    simp [nativeE, nativeProjection]
  have hNj : nativeE ring (nativeProjection z.val.1) e (ring.rightNeighbor e) =
      (certLiteralEPair (z.val.1 e).certNative
        (z.val.1 (ring.rightNeighbor e)).certNative).2 := by
    simp [nativeE, nativeProjection, hne]
  have hle : ((bankRepairNext ring hbank z e).val.1 e).l =
      (certLiteralEPair (z.val.1 e).certNative
        (z.val.1 (ring.rightNeighbor e)).certNative).1.l := by
    have h := congrFun hnative e
    rw [hNe] at h
    exact congrArg CertNative.l h
  have hlj : ((bankRepairNext ring hbank z e).val.1 (ring.rightNeighbor e)).l =
      (certLiteralEPair (z.val.1 e).certNative
        (z.val.1 (ring.rightNeighbor e)).certNative).2.l := by
    have h := congrFun hnative (ring.rightNeighbor e)
    rw [hNj] at h
    exact congrArg CertNative.l h
  have hmaskL : ∀ s : Bool,
      (renewalMaskedPair (compileAdvice (ceilLogTwo n)) s
        (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).1.l =
        (transition (compileAdvice (ceilLogTwo n))
          (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).1.l ∧
      (renewalMaskedPair (compileAdvice (ceilLogTwo n)) s
        (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).2.l =
        (transition (compileAdvice (ceilLogTwo n))
          (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).2.l := by
    intro s
    cases s <;> exact ⟨rfl, rfl⟩
  have hl1 : (transition (compileAdvice (ceilLogTwo n))
      (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).1.l =
      (certLiteralEPair (z.val.1 e).certNative
        (z.val.1 (ring.rightNeighbor e)).certNative).1.l := by
    rw [← (hmaskL (renewalBankCut ring z.val.1 z.val.2 e)).1, ← hxe, hle]
  have hl2 : (transition (compileAdvice (ceilLogTwo n))
      (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).2.l =
      (certLiteralEPair (z.val.1 e).certNative
        (z.val.1 (ring.rightNeighbor e)).certNative).2.l := by
    rw [← (hmaskL (renewalBankCut ring z.val.1 z.val.2 e)).2, ← hxj, hlj]
  have hpair := bankRequestCloseMaskedPair (compileAdvice (ceilLogTwo n))
    (renewalBankCut ring z.val.1 z.val.2 e)
    (z.val.1 e) (z.val.1 (ring.rightNeighbor e))
    (hg e) (hg (ring.rightNeighbor e))
    (hdebt e).1 (hdebt e).2
    (hdebt (ring.rightNeighbor e)).1 (hdebt (ring.rightNeighbor e)).2
    hev hl1 hl2
  refine ⟨?_, ?_, ?_⟩
  · rw [hxe]; exact hpair.1
  · rw [hlj, hxj]; exact hpair.2
  · intro i hi hj
    rw [hstep]
    simp only [if_neg hi]
    exact if_neg hj

/-! ## The fixed leader -/

/-- The class of the request stage, with its leader site named.
Consumer: `bankRepairRequestHalfOnDrainProved`. -/
def BankRequestCloseClass {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (p : Fin n) (z : BankReferenceState ring hbank) : Prop :=
  BankPostInheritedGrantDrain ring hbank z ∧
    BankRepairDebtCleared ring hbank z ∧ (z.val.1 p).l = true

/-- Core names a unique leader.  Consumer: `bankRequestCloseClassStep`,
`bankRequestCloseFrontStep`. -/
theorem bankRequestCloseLeaderUnique {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hc : BankRepairCore ring hbank z) (p : Fin n)
    (hp : (z.val.1 p).l = true) (i : Fin n)
    (hi : (z.val.1 i).l = true) : i = p := by
  have hone : OneNativeLeader (nativeProjection z.val.1) := hc.1.1
  obtain ⟨q, _, hqu⟩ := hone
  have h1 : i = q := hqu i hi
  have h2 : p = q := hqu p hp
  rw [h1, h2]

/-- The leader site survives every drain edge.
Consumer: `bankRequestCloseClassStep`. -/
theorem bankRequestCloseLeaderStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hD : BankPostInheritedGrantDrain ring hbank z)
    (hc : BankRepairCore ring hbank z)
    (hc' : ∀ e, BankRepairCore ring hbank (bankRepairNext ring hbank z e))
    (p : Fin n) (hp : (z.val.1 p).l = true) (e : Fin n) :
    ((bankRepairNext ring hbank z e).val.1 p).l = true := by
  have hnative := bankAfterGrantDrainNativeStep ring hn hbank z hD.1 e
  change nativeProjection (bankRepairNext ring hbank z e).val.1 =
    nativeE ring (nativeProjection z.val.1) e at hnative
  have hone : OneNativeLeader
      (nativeProjection (bankRepairNext ring hbank z e).val.1) := (hc' e).1.1
  obtain ⟨q, hq, _⟩ := hone
  have hq' : (nativeE ring (nativeProjection z.val.1) e q).l = true := by
    rw [← hnative]; exact hq
  have hold := Closure.nativeENoNewLeader (by omega) ring
    (nativeProjection z.val.1) e q hq'
  have hqp : q = p := bankRequestCloseLeaderUnique ring hbank z hc p hp q hold
  rw [← hqp]
  exact hq

/-- The named class is closed.  Consumer:
`bankRepairRequestHalfOnDrainProved`. -/
theorem bankRequestCloseClassStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (p : Fin n) (z : BankReferenceState ring hbank)
    (hz : BankRequestCloseClass ring hbank p z) (e : Fin n) :
    BankRequestCloseClass ring hbank p (bankRepairNext ring hbank z e) := by
  have hpres := bankFinishCleanPreservation ring hn hbank
  have hC' : ∀ e, BankRepairDebtCleared ring hbank (bankRepairNext ring hbank z e) :=
    fun e => hpres.2.2.2.2 z hz.1 hz.2.1 e
  exact ⟨bankPostInheritedGrantDrainClosed ring hn hbank z hz.1 e, hC' e,
    bankRequestCloseLeaderStep ring hn hbank z hz.1 hz.2.1.1.1.1.1
      (fun e => (hC' e).1.1.1.1) p hz.2.2 e⟩

/-! ## Distance to the leader and the front potential -/

/-- Clockwise distance from `i` to the leader `p`, with `p` itself at
distance n.  Consumer: `bankRequestCloseFront`. -/
def bankRequestCloseDist {n : Nat} (p i : Fin n) : Nat :=
  if p.val ≤ i.val then n - (i.val - p.val) else p.val - i.val

/-- Consumer: `bankRequestCloseFrontPositive`, `bankRequestCloseFrontLe`. -/
theorem bankRequestCloseDistBounds {n : Nat} (p i : Fin n) :
    1 ≤ bankRequestCloseDist p i ∧ bankRequestCloseDist p i ≤ n := by
  have hi := i.isLt
  unfold bankRequestCloseDist
  split <;> omega

/-- Consumer: `bankRequestCloseFrontStep`. -/
theorem bankRequestCloseDistInjective {n : Nat} (p i k : Fin n)
    (h : bankRequestCloseDist p i = bankRequestCloseDist p k) : i = k := by
  have hi := i.isLt
  have hk := k.isLt
  apply Fin.ext
  unfold bankRequestCloseDist at h
  split at h <;> split at h <;> omega

/-- A step toward the leader lowers the distance by one.
Consumer: `bankRequestCloseFrontStep`. -/
theorem bankRequestCloseDistStep {n : Nat} (ring : DirectedRing n)
    (p e : Fin n) (hep : e ≠ p) (hjp : ring.rightNeighbor e ≠ p) :
    bankRequestCloseDist p (ring.rightNeighbor e) + 1 =
      bankRequestCloseDist p e := by
  have he := e.isLt
  have hp := p.isLt
  have hep' : e.val ≠ p.val := fun h => hep (Fin.ext h)
  have hjp' : (ring.rightNeighbor e).val ≠ p.val := fun h => hjp (Fin.ext h)
  have hj := rightNeighbor_val ring e
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hj
    unfold bankRequestCloseDist
    rw [hj] at hjp' ⊢
    split <;> split <;> omega
  · have heq : e.val + 1 = n := by omega
    rw [heq, Nat.mod_self] at hj
    unfold bankRequestCloseDist
    rw [hj] at hjp' ⊢
    split <;> split <;> omega

/-- Maximum of a function on `Fin m`.  Consumer: `bankRequestCloseFront`. -/
def bankRequestCloseMax : {m : Nat} → (Fin m → Nat) → Nat
  | 0, _ => 0
  | _ + 1, f => max (f 0) (bankRequestCloseMax (fun i => f i.succ))

/-- Consumer: `bankRequestCloseFrontStep`. -/
theorem bankRequestCloseLeMax : ∀ {m : Nat} (f : Fin m → Nat) (i : Fin m),
    f i ≤ bankRequestCloseMax f
  | 0, _, i => i.elim0
  | _ + 1, f, i => by
      show f i ≤ max (f 0) (bankRequestCloseMax (fun i => f i.succ))
      cases i using Fin.cases with
      | zero => exact Nat.le_max_left _ _
      | succ k =>
          exact Nat.le_trans (bankRequestCloseLeMax (fun i => f i.succ) k)
            (Nat.le_max_right _ _)

/-- Consumer: `bankRequestCloseFrontStep`, `bankRequestCloseFrontLe`. -/
theorem bankRequestCloseMaxLe : ∀ {m : Nat} (f : Fin m → Nat) (M : Nat),
    (∀ i, f i ≤ M) → bankRequestCloseMax f ≤ M
  | 0, _, _, _ => Nat.zero_le _
  | _ + 1, f, M, h => by
      show max (f 0) (bankRequestCloseMax (fun i => f i.succ)) ≤ M
      exact Nat.max_le.mpr ⟨h 0,
        bankRequestCloseMaxLe (fun i => f i.succ) M (fun i => h i.succ)⟩

/-- Consumer: `bankRequestCloseDrift`. -/
theorem bankRequestCloseMaxAttained : ∀ {m : Nat} (f : Fin m → Nat),
    0 < bankRequestCloseMax f → ∃ i, f i = bankRequestCloseMax f
  | 0, _, h => absurd h (Nat.lt_irrefl 0)
  | _ + 1, f, h => by
      change 0 < max (f 0) (bankRequestCloseMax (fun i => f i.succ)) at h
      show ∃ i, f i = max (f 0) (bankRequestCloseMax (fun i => f i.succ))
      by_cases h0 : bankRequestCloseMax (fun i => f i.succ) ≤ f 0
      · exact ⟨0, (Nat.max_eq_left h0).symm⟩
      · have hlt : f 0 < bankRequestCloseMax (fun i => f i.succ) := by omega
        obtain ⟨k, hk⟩ := bankRequestCloseMaxAttained (fun i => f i.succ)
          (by omega)
        exact ⟨k.succ, by rw [Nat.max_eq_right (Nat.le_of_lt hlt)]; exact hk⟩

/-- Distance of a request site, zero elsewhere.
Consumer: `bankRequestCloseFront`. -/
def bankRequestCloseSiteValue {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (p : Fin n) (z : BankReferenceState ring hbank) (i : Fin n) : Nat :=
  if (z.val.1 i).req then bankRequestCloseDist p i else 0

/-- The request front: largest distance to the leader of a request.
Consumer: `bankRepairRequestHalfOnDrainProved`. -/
def bankRequestCloseFront {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (p : Fin n) (z : BankReferenceState ring hbank) : Nat :=
  bankRequestCloseMax (bankRequestCloseSiteValue ring hbank p z)

/-- Consumer: `bankRepairRequestHalfOnDrainProved`. -/
theorem bankRequestCloseFrontLe {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (p : Fin n) (z : BankReferenceState ring hbank) :
    bankRequestCloseFront ring hbank p z ≤ n := by
  apply bankRequestCloseMaxLe
  intro i
  unfold bankRequestCloseSiteValue
  split
  · exact (bankRequestCloseDistBounds p i).2
  · exact Nat.zero_le _

/-- A live request makes the front positive.
Consumer: `bankRequestCloseDrift`. -/
theorem bankRequestCloseFrontPositive {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (p : Fin n) (z : BankReferenceState ring hbank)
    (hz : ¬ BankRepairRequestZero ring hbank z) :
    0 < bankRequestCloseFront ring hbank p z := by
  have hex : ∃ i : Fin n, (z.val.1 i).req = true := by
    apply Classical.byContradiction
    intro hno
    apply hz
    intro i
    cases h : (z.val.1 i).req with
    | false => rfl
    | true => exact absurd ⟨i, h⟩ hno
  obtain ⟨i, hi⟩ := hex
  have hv : bankRequestCloseSiteValue ring hbank p z i =
      bankRequestCloseDist p i := by
    unfold bankRequestCloseSiteValue
    rw [hi]; rfl
  have h1 := bankRequestCloseLeMax (bankRequestCloseSiteValue ring hbank p z) i
  have h2 := (bankRequestCloseDistBounds p i).1
  unfold bankRequestCloseFront
  omega

/-- Boolean reading of the responder row.  Consumer:
`bankRequestCloseFrontStep`. -/
theorem bankRequestCloseBoolRow (a b c d : Bool)
    (h : (!a && (b || (c && !d))) = true) :
    a = false ∧ (b = true ∨ (c = true ∧ d = false)) := by
  revert h
  cases a <;> cases b <;> cases c <;> cases d <;> decide

/-- One edge: every site value after the edge is at most the front, and
strictly below it when the edge leaves a front site.
Consumer: `bankRequestCloseDrift`. -/
theorem bankRequestCloseFrontStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (p : Fin n) (z : BankReferenceState ring hbank)
    (hz : BankRequestCloseClass ring hbank p z) (e : Fin n) (slack : Nat)
    (hslack : slack = 0 ∨
      (slack = 1 ∧ bankRequestCloseSiteValue ring hbank p z e =
        bankRequestCloseFront ring hbank p z ∧
        0 < bankRequestCloseFront ring hbank p z)) :
    bankRequestCloseFront ring hbank p (bankRepairNext ring hbank z e) + slack ≤
      bankRequestCloseFront ring hbank p z := by
  have hne := clockNeighborDifferent ring (by omega) e
  obtain ⟨hreqE, hreqJ, hother⟩ :=
    bankRequestCloseStep ring hn hbank z hz.1 hz.2.1 e
  have hz' := bankRequestCloseClassStep ring hn hbank p z hz e
  have hlead : ∀ i, (z.val.1 i).l = true → i = p :=
    bankRequestCloseLeaderUnique ring hbank z hz.2.1.1.1.1.1 p hz.2.2
  have hlead' : ∀ i, ((bankRepairNext ring hbank z e).val.1 i).l = true → i = p :=
    bankRequestCloseLeaderUnique ring hbank _ hz'.2.1.1.1.1.1 p hz'.2.2
  -- the front value
  have hle : ∀ i, bankRequestCloseSiteValue ring hbank p z i ≤
      bankRequestCloseFront ring hbank p z :=
    fun i => bankRequestCloseLeMax _ i
  -- a site other than e with the front value is impossible under slack 1
  have hbelow : ∀ i, i ≠ e → slack = 1 →
      bankRequestCloseSiteValue ring hbank p z i + 1 ≤
        bankRequestCloseFront ring hbank p z := by
    intro i hie hs1
    rcases hslack with h0 | ⟨_, hfe, hpos⟩
    · omega
    · have hvi := hle i
      unfold bankRequestCloseSiteValue at hvi ⊢
      unfold bankRequestCloseSiteValue at hfe
      by_cases hri : (z.val.1 i).req = true
      · rw [if_pos hri] at hvi ⊢
        by_cases hre : (z.val.1 e).req = true
        · rw [if_pos hre] at hfe
          have hd : bankRequestCloseDist p i ≠ bankRequestCloseDist p e :=
            fun h => hie (bankRequestCloseDistInjective p i e h)
          omega
        · rw [if_neg hre] at hfe
          omega
      · rw [if_neg hri]
        omega
  have hsF : slack ≤ bankRequestCloseFront ring hbank p z := by
    rcases hslack with h0 | ⟨h1, _, hpos⟩ <;> omega
  have hs1 : slack ≤ 1 := by
    rcases hslack with h0 | ⟨h1, _, _⟩ <;> omega
  have hsite : ∀ i, bankRequestCloseSiteValue ring hbank p
      (bankRepairNext ring hbank z e) i + slack ≤
        bankRequestCloseFront ring hbank p z := by
    intro i
    by_cases hie : i = e
    · subst hie
      unfold bankRequestCloseSiteValue
      simp only [hreqE, Bool.false_eq_true, ↓reduceIte]
      omega
    · by_cases hij : i = ring.rightNeighbor e
      · subst hij
        unfold bankRequestCloseSiteValue
        by_cases hr : ((bankRepairNext ring hbank z e).val.1
            (ring.rightNeighbor e)).req = true
        · rw [if_pos hr]
          rw [hreqJ] at hr
          obtain ⟨hl', hor⟩ := bankRequestCloseBoolRow _ _ _ _ hr
          have hjp : ring.rightNeighbor e ≠ p := by
            intro h
            have hlp := hz'.2.2
            rw [← h, hl'] at hlp
            exact Bool.noConfusion hlp
          rcases hor with hrj | ⟨hre, hle'⟩
          · have hv := hle (ring.rightNeighbor e)
            unfold bankRequestCloseSiteValue at hv
            rw [if_pos hrj] at hv
            rcases hslack with h0 | ⟨h1, _, _⟩
            · omega
            · have hb := hbelow (ring.rightNeighbor e) hie h1
              unfold bankRequestCloseSiteValue at hb
              rw [if_pos hrj] at hb
              omega
          · have hep : e ≠ p := by
              intro h
              have hlp := hz.2.2
              rw [← h, hle'] at hlp
              exact Bool.noConfusion hlp
            have hd := bankRequestCloseDistStep ring p e hep hjp
            have hv := hle e
            unfold bankRequestCloseSiteValue at hv
            rw [if_pos hre] at hv
            omega
        · rw [if_neg hr]
          omega
      · have hv' : bankRequestCloseSiteValue ring hbank p
            (bankRepairNext ring hbank z e) i =
            bankRequestCloseSiteValue ring hbank p z i := by
          unfold bankRequestCloseSiteValue
          rw [hother i hie hij]
        rw [hv']
        rcases hslack with h0 | ⟨h1, _, _⟩
        · have := hle i
          omega
        · exact h1 ▸ hbelow i hie h1
  have hmax := bankRequestCloseMaxLe
    (bankRequestCloseSiteValue ring hbank p (bankRepairNext ring hbank z e))
    (bankRequestCloseFront ring hbank p z - slack)
    (fun i => by have := hsite i; omega)
  have hmax' : bankRequestCloseFront ring hbank p (bankRepairNext ring hbank z e) ≤
      bankRequestCloseFront ring hbank p z - slack := hmax
  omega

/-! ## Drift and the stage -/

/-- Consumer: `bankRequestCloseSumSpike`. -/
theorem bankRequestCloseSumLe : ∀ {m : Nat} (F : Fin m → Nat) (B : Nat),
    (∀ e, F e ≤ B) → (List.ofFn F).sum ≤ m * B
  | 0, _, _, _ => by simp
  | m + 1, F, B, h => by
      rw [List.ofFn_succ, List.sum_cons, Nat.succ_mul]
      have h1 := bankRequestCloseSumLe (fun i => F i.succ) B (fun i => h i.succ)
      have h2 := h 0
      omega

/-- Consumer: `bankRequestCloseDrift`. -/
theorem bankRequestCloseSumSpike : ∀ {m : Nat} (F : Fin m → Nat) (c : Fin m)
    (B d : Nat), (∀ e, F e ≤ B) → F c + d ≤ B → (List.ofFn F).sum + d ≤ m * B
  | 0, _, c, _, _, _, _ => c.elim0
  | m + 1, F, c, B, d, h, hc => by
      rw [List.ofFn_succ, List.sum_cons, Nat.succ_mul]
      cases c using Fin.cases with
      | zero =>
          have h1 := bankRequestCloseSumLe (fun i => F i.succ) B (fun i => h i.succ)
          omega
      | succ k =>
          have h1 := bankRequestCloseSumSpike (fun i => F i.succ) k B d
            (fun i => h i.succ) hc
          have h2 := h 0
          omega

/-- Drift of the scaled front.  Consumer:
`bankRepairRequestHalfOnDrainProved`. -/
theorem bankRequestCloseDrift {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (p : Fin n) (z : BankReferenceState ring hbank)
    (hz : BankRequestCloseClass ring hbank p z)
    (hnz : ¬ BankRepairRequestZero ring hbank z) :
    n + (List.ofFn (fun e : Fin n => n *
        bankRequestCloseFront ring hbank p (bankRepairNext ring hbank z e))).sum ≤
      n * (n * bankRequestCloseFront ring hbank p z) := by
  have hpos := bankRequestCloseFrontPositive ring hbank p z hnz
  obtain ⟨i, hi⟩ := bankRequestCloseMaxAttained
    (bankRequestCloseSiteValue ring hbank p z) hpos
  have hall : ∀ e, n * bankRequestCloseFront ring hbank p
      (bankRepairNext ring hbank z e) ≤ n * bankRequestCloseFront ring hbank p z := by
    intro e
    have h := bankRequestCloseFrontStep ring hn hbank p z hz e 0 (Or.inl rfl)
    exact Nat.mul_le_mul_left n (by omega)
  have hspec : n * bankRequestCloseFront ring hbank p
      (bankRepairNext ring hbank z i) + n ≤
        n * bankRequestCloseFront ring hbank p z := by
    have h := bankRequestCloseFrontStep ring hn hbank p z hz i 1
      (Or.inr ⟨rfl, hi, hpos⟩)
    have h2 := Nat.mul_le_mul_left n h
    rw [Nat.mul_add, Nat.mul_one] at h2
    exact h2
  have hsum := bankRequestCloseSumSpike
    (fun e : Fin n => n *
      bankRequestCloseFront ring hbank p (bankRepairNext ring hbank z e))
    i (n * bankRequestCloseFront ring hbank p z) n hall hspec
  omega

/-- repair.tex 5374-5380 on the drain: requests reach the protected
root within n² (two half-units).  Consumer:
`bankFinishReferenceFinishRequestClosed`. -/
theorem bankRepairRequestHalfOnDrainProved {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    BankRepairRequestHalfOnDrain ring hbank := by
  intro z hz T
  have hone : OneNativeLeader (nativeProjection z.val.1) := hz.2.1.1.1.1.1.1
  obtain ⟨p, hp, _⟩ := hone
  have hI : BankRequestCloseClass ring hbank p z := ⟨hz.1, hz.2, hp⟩
  have hpot : costNumerator (bankRepairNext ring hbank)
      (BankRepairRequestZero ring hbank) z T ≤
        n ^ T * (n * bankRequestCloseFront ring hbank p z) :=
    L3.Prob.costNumerator_le_of_potential_on (bankRepairNext ring hbank)
      (BankRepairRequestZero ring hbank) (BankRequestCloseClass ring hbank p)
      (fun x => n * bankRequestCloseFront ring hbank p x)
      (fun x hx _ e => bankRequestCloseClassStep ring hn hbank p x hx e)
      (fun x hx hnz => bankRequestCloseDrift ring hn hbank p x hx hnz)
      z hI T
  have hF := bankRequestCloseFrontLe ring hbank p z
  have h1 : n * bankRequestCloseFront ring hbank p z ≤ n * n :=
    Nat.mul_le_mul_left n hF
  have h2 : n ^ T * (n * bankRequestCloseFront ring hbank p z) ≤
      n ^ T * (n * n) := Nat.mul_le_mul_left _ h1
  have h3 : n ^ T * (2 * n ^ 2) = 2 * (n ^ T * (n * n)) := by
    rw [Nat.pow_two]
    exact Nat.mul_left_comm _ _ _
  rw [h3]
  omega

/-- The BANK reference finish with the request stage discharged: the
open premises are the AcceptedWord completion (W monitor) and the digit
half-stage on the drain (R10c).  Consumer: the BANK reference finish
(`BankReferenceClock`, R12). -/
theorem bankFinishReferenceFinishRequestClosed {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hcompletion : ∀ root : Fin n,
      ∀ s : Fin n → ProjW (compileAdvice (ceilLogTwo n)),
        BankWordSerializerRootClass ring hbank root s →
        ∀ z : BankWordEpochState n,
          BankWordEpochReachable ring root s z →
          BankWordRenewalCompleted z →
          BankWordProjectedTarget ring z.2.1)
    (hdigit : BankRepairDigitHalfOnDrain ring hbank) :
    StageReferenceGeneratedFinish
      (bankRepairNext ring hbank)
      (BankPreparedAtSomeRoot ring hbank)
      (bankRepairStop ring hbank)
      (headlineReferenceFinishRate (ceilLogTwo n)) :=
  bankFinishReferenceFinishClean ring hn hbank hcompletion hdigit
    (bankRepairRequestHalfOnDrainProved ring hn hbank)

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankRepairRequestHalfOnDrainProved
#print axioms L3.RenewalReferenceClock.bankFinishReferenceFinishRequestClosed
