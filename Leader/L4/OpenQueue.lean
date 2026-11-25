/-!
# The L4 barrier's ideal open queue

This file is independent of the implementation of the physical pair rule.
An arbitrary sequence of selected bond names and outlet permissions drives
both queues on the same mark. The permissions may depend on the full past:
the deterministic comparison needs no stochastic hypothesis.
-/
namespace L4.OpenQueue

/-- Occupancy of the two sites immediately clockwise from the supplier. -/
structure StockPair where
  first : Bool
  second : Bool
  deriving DecidableEq, Repr

/-- The three distinguished physical edges, or an irrelevant mark. -/
inductive Bond where
  | inject | transfer | outlet | other
  deriving DecidableEq, Repr

/-- Reset value for each fresh long-tenure comparison. -/
def empty : StockPair := ⟨false, false⟩

/-- Coordinatewise domination by the blocked real queue. -/
def Below (ideal real : StockPair) : Prop :=
  (ideal.first = true → real.first = true) ∧
  (ideal.second = true → real.second = true)

instance (i r : StockPair) : Decidable (Below i r) := by
  unfold Below
  infer_instance

/-- The physical two-slot projection: acceptance is relevant only for the
outlet. Injection is supplied by the stationary leader. -/
def realStep (q : StockPair) (b : Bond) (accept : Bool) : StockPair :=
  match b with
  | .inject => ⟨true, q.second⟩
  | .transfer =>
    if q.first && !q.second then ⟨false, true⟩ else q
  | .outlet => ⟨q.first, q.second && !accept⟩
  | .other => q

/-- The ideal queue leaves the outlet permanently open. -/
def idealStep (q : StockPair) (b : Bond) : StockPair :=
  realStep q b true

/-- The exact real/ideal transition equality is false without an open real
outlet: an occupied second slot can stay occupied only in the real queue. -/
theorem blocked_outlet_not_ideal :
    realStep ⟨false, true⟩ .outlet false ≠ idealStep ⟨false, true⟩ .outlet := by
  decide

/-- Did the selected mark inject a new particle (as opposed to stuttering
on an already occupied entry slot)? -/
def ingress (q : StockPair) (b : Bond) : Bool :=
  match b with
  | .inject => !q.first
  | _ => false

/-- The comparison's reset lies below every initial real stock pair. -/
theorem empty_below (r : StockPair) : Below empty r := by
  cases r with
  | mk ra rb => cases ra <;> cases rb <;> decide

/-- The complete local comparison. Blockage can retain real stock at the
outlet. It cannot break order or cause a real-only ingress. -/
theorem oneStep (ideal real : StockPair) (b : Bond) (accept : Bool)
    (h : Below ideal real) :
    Below (idealStep ideal b) (realStep real b accept) ∧
      (ingress real b = true → ingress ideal b = true) := by
  cases ideal with
  | mk ia ib =>
    cases real with
    | mk ra rb =>
      revert h
      cases ia <;> cases ib <;> cases ra <;> cases rb <;>
        cases b <;> cases accept <;> decide

/-- A marked step includes the actual real outlet permission, not the ideal
outlet permission. It can be high or low on any selected mark. -/
structure Mark where
  bond : Bond
  accept : Bool
  deriving Repr

/-- Real stock at the end of a finite trace. -/
def runReal (q : StockPair) : List Mark → StockPair
  | [] => q
  | a :: w => runReal (realStep q a.bond a.accept) w

/-- Ideal stock at the end of the same finite trace. -/
def runIdeal (q : StockPair) : List Mark → StockPair
  | [] => q
  | a :: w => runIdeal (idealStep q a.bond) w

/-- Real emitted tokens, counted on their ingress marks, not at the outlet. -/
def realIngresses (q : StockPair) : List Mark → Nat
  | [] => 0
  | a :: w => (ingress q a.bond).toNat + realIngresses (realStep q a.bond a.accept) w

/-- New ideal stock emitted on the same marks. -/
def idealIngresses (q : StockPair) : List Mark → Nat
  | [] => 0
  | a :: w => (ingress q a.bond).toNat + idealIngresses (idealStep q a.bond) w

private theorem boolCount_le {a b : Bool} (h : a = true → b = true) :
    a.toNat ≤ b.toNat := by
  revert h
  cases a <;> cases b <;> decide

/-- Coordinatewise order and the ingress-count bound at every finite
prefix, for every choice of outlet permissions. -/
theorem run_below_and_ingresses (w : List Mark) (ideal real : StockPair)
    (h : Below ideal real) :
    Below (runIdeal ideal w) (runReal real w) ∧
      realIngresses real w ≤ idealIngresses ideal w := by
  induction w generalizing ideal real with
  | nil => exact ⟨h, Nat.le_refl _⟩
  | cons a w ih =>
    obtain ⟨hn, he⟩ := oneStep ideal real a.bond a.accept h
    obtain ⟨hr, hc⟩ := ih (idealStep ideal a.bond) (realStep real a.bond a.accept) hn
    exact ⟨hr, Nat.add_le_add (boolCount_le he) hc⟩

/-- An explicit same-mark assertion after any driven comparison prefix. -/
theorem ingress_same_mark_after_prefix (w : List Mark) (real : StockPair)
    (b : Bond) :
    ingress (runReal real w) b = true →
      ingress (runIdeal empty w) b = true := by
  have h := (run_below_and_ingresses w empty real (empty_below real)).1
  exact (oneStep (runIdeal empty w) (runReal real w) b false h).2

/-- Paper potential on the four queue occupancies. -/
def weight (q : StockPair) : Int :=
  match q.first, q.second with
  | false, false => 0
  | true, false => -3
  | false, true => -1
  | true, true => -5

/-- One mark's compensated ideal ingress, multiplied by five. -/
def scaledIncrement (q : StockPair) (b : Bond) : Int :=
  5 * (Int.ofNat (ingress q b).toNat) + (weight (idealStep q b) - weight q)

/-- An irrelevant edge does not contribute compensated current. -/
theorem scaledIncrement_other (q : StockPair) :
    scaledIncrement q .other = 0 := by
  simp [scaledIncrement, idealStep, realStep, ingress]

/-- Exact one-step drift numerator: the sum across the three distinguished
bond names is two, independently of the current ideal occupancy. -/
theorem three_bond_sum (q : StockPair) :
    scaledIncrement q .inject + scaledIncrement q .transfer + scaledIncrement q .outlet = 2 := by
  cases q with
  | mk a b => cases a <;> cases b <;> decide

/-- The four triples of scaled increments, in the order 00,10,01,11. -/
theorem increment_table :
    let triple (q : StockPair) :=
      (scaledIncrement q .inject, scaledIncrement q .transfer, scaledIncrement q .outlet)
    triple ⟨false,false⟩ = (2,0,0) ∧
    triple ⟨true,false⟩ = (0,2,0) ∧
    triple ⟨false,true⟩ = (1,0,1) ∧
    triple ⟨true,true⟩ = (0,0,2) := by
  decide

/-- The potential debit can never exceed five scaled units. -/
theorem weight_ge_neg_five (q : StockPair) : -5 ≤ weight q := by
  cases q with
  | mk a b => cases a <;> cases b <;> decide

/-- Total scaled compensation within one continuous episode. This does not
charge any discontinuity from resetting to empty between episodes. -/
def scaledCurrent (q : StockPair) : List Mark → Int
  | [] => 0
  | a :: w => scaledIncrement q a.bond + scaledCurrent (idealStep q a.bond) w

private theorem int_ofNat_add (a b : Nat) :
    Int.ofNat (a+b) = Int.ofNat a + Int.ofNat b := rfl

/-- Telescoping the potential across any finite (including truncated) episode. -/
theorem scaledCurrent_telescope (w : List Mark) (q : StockPair) :
    scaledCurrent q w =
      5 * Int.ofNat (idealIngresses q w) + weight (runIdeal q w) - weight q := by
  induction w generalizing q with
  | nil => simp [scaledCurrent, idealIngresses, runIdeal]
  | cons a w ih =>
    rw [scaledCurrent, ih]
    simp only [scaledIncrement, idealIngresses, runIdeal, int_ofNat_add]
    omega

/-- After an empty reset, at most one (unscaled) ingress is lost to the
episode's terminal potential, even when observation ends inside the episode. -/
theorem episode_ingresses_le (w : List Mark) :
    5 * Int.ofNat (idealIngresses empty w) ≤ scaledCurrent empty w + 5 := by
  rw [scaledCurrent_telescope]
  have h := weight_ge_neg_five (runIdeal empty w)
  have hw : weight empty = 0 := rfl
  omega

/-- Scale-five sum of fresh episode ingress counts. -/
def episodeScaledIngresses : List (List Mark) → Int
  | [] => 0
  | w :: ww => 5 * Int.ofNat (idealIngresses empty w) + episodeScaledIngresses ww

/-- Scale-five compensation across independently reset episodes. -/
def episodeCurrent : List (List Mark) → Int
  | [] => 0
  | w :: ww => scaledCurrent empty w + episodeCurrent ww

/-- Reset telescoping across all long pieces on a path. There is one unit
of unscaled debit per episode, and no fictitious increment on reset. -/
theorem reset_telescope_le (ww : List (List Mark)) :
    episodeScaledIngresses ww ≤ episodeCurrent ww + 5 * Int.ofNat ww.length := by
  induction ww with
  | nil => simp [episodeScaledIngresses, episodeCurrent]
  | cons w ww ih =>
    have h := episode_ingresses_le w
    simp only [episodeScaledIngresses, episodeCurrent, List.length_cons, int_ofNat_add, show Int.ofNat 1 = 1 from rfl]
    omega

end L4.OpenQueue

