import Leader.L4.Height.AllSizeWirePart17
set_option Elab.async false

namespace L4.Height.AllSizeWire
open AllSizeSpine L4.Compiler.Native Classical

section Family

open PhysicalCustody CustodySpec ClockDisplaySpec PublicSpec AllSizeProtocol
open Classical

variable {s n : Nat}

/-- One public coefficient covers both the bounded and packed deployments. -/
def patrolAllowance (C : Nat) := C - 2049

theorem public_budget (C n : Nat) : C*n^2 ≤ (2049+patrolAllowance C)*n^2 := by
  apply Nat.mul_le_mul_right
  unfold patrolAllowance
  omega

theorem packed_observer (hn : 4 ≤ n) (hs : 6 ≤ s) (H : PackedObserverMean) :
    let D := packedData s n hn hs
    ∀ x, D.display (by omega) x → IIDExpectedHittingTimeAtMost
      (D.next (by omega)) D.marked x (5*n^2+7*n) :=
  fun x hx => H hn x ((reference_iff_permanent x).2 hx)

theorem packed_publicSuffix (hn : 4 ≤ n) (hs : 6 ≤ s) (C : Nat)
    (hC : ∀ x : Raw s n, Marked x →
      IIDExpectedHittingTimeAtMost (rawNext s) PackedElected x (C*n^2)) :
    let D := packedData s n hn hs
    ∀ x, D.marked x → IIDExpectedHittingTimeAtMost (D.next (by omega))
      (D.elected (by omega)) x ((2049+patrolAllowance C)*n^2) := by
  dsimp only
  intro x hx
  change Marked x at hx
  rw [packed_next hn hs]
  have hTarget : (PackedElected : Raw s n → Prop) =
      (packedData s n hn hs).elected (by omega) :=
    funext fun y => propext (productSafe_iff_permanent (rawNext s) packedLeader y)
  have h := hC x hx
  rw [hTarget] at h
  exact expected_bound_mono _ _ _ h (public_budget C n)

noncomputable def boundedData (encode : L4.Site boundedP 12 → BoundedCode)
    (decode : BoundedCode → L4.Site boundedP 12) (n : Nat) : AllSizeData BoundedCode n where
  row := fun ab => boundedPairWith encode decode ab.1 ab.2
  leader := fun a => (decode a).leader
  reference := fun _ => false
  cust := fun _ => False
  marked := fun _ => False
  Chart := Empty
  State := Empty.elim
  m := Empty.elim
  hm := fun j => nomatch j
  r := 0
  width := Empty.elim
  clock := fun j => nomatch j
  raw := fun j => nomatch j
  opening := fun j => nomatch j
  level := fun j => nomatch j

theorem bounded_interfaces (encode : L4.Site boundedP 12 → BoundedCode)
    (decode : BoundedCode → L4.Site boundedP 12) (hn : 4 ≤ n) (hb : n ≤ boundedN) (g C : Nat)
    (hC : ∀ x : BoundedRaw n, IIDExpectedHittingTimeAtMost (boundedNextWith encode decode)
      (BoundedElectedWith encode decode) x (C*n^2)) :
    AllSizeInterfaces (boundedData encode decode n) (by omega) g (2^32) (patrolAllowance C) := by
  let D := boundedData encode decode n
  have hnp : ¬ 2^32 < n := Nat.not_lt.mpr hb
  refine {
    bounded := ?_
    custody := fun hp => (hnp hp).elim
    liftCustody := fun hp => (hnp hp).elim
    rawStep := fun j => Empty.elim j
    parameters := fun j => Empty.elim j
    service := fun j => Empty.elim j
    displaySplit := fun j => Empty.elim j
    missQuarter := fun j => Empty.elim j
    observer := fun hp => (hnp hp).elim
    publicSuffix := fun hp => (hnp hp).elim }
  intro _ x
  have hNext : D.next (by omega) = boundedNextWith encode decode := rfl
  change IIDExpectedHittingTimeAtMost (D.next (by omega)) (D.elected (by omega)) x
    ((2049+patrolAllowance C)*n^2)
  rw [hNext]
  have htarget : (BoundedElectedWith encode decode : BoundedRaw n → Prop) = D.elected (by omega) :=
    funext fun y => propext (productSafe_iff_permanent (boundedNextWith encode decode)
      (boundedLeaderWith decode) y)
  have hx := hC x
  rw [htarget] at hx
  exact expected_bound_mono _ _ _ hx (public_budget C n)

theorem packed_interfaces (hn : 4 ≤ n) (hs : 6 ≤ s) (ha : s = ell (ell n)) (g C : Nat)
    (hCust : ∀ x : Raw s n, IIDExpectedHittingTimeAtMost (rawNext s) Custody x
      (packingCoefficient g*n^2))
    (hBlock : ClockServiceSpec.ProductionStrictBlock) (hQuiet : RawLegitOfQuiet)
    (hTrial : ClockDisplaySpec.RawDisplayTrial) (hObs : PackedObserverMean)
    (hC : ∀ x : Raw s n, Marked x →
      IIDExpectedHittingTimeAtMost (rawNext s) PackedElected x (C*n^2)) :
    let D := packedData s n hn hs
    let origin := packedOrigin (s := s) (n := n) hn hs
    let trials := packed_trial hn hs ha hQuiet hTrial
    AllSizeInterfaces (withDisplayTrials D (by omega) (2^32) origin trials)
      (by omega) g (2^32) (patrolAllowance C) := by
  let D := packedData s n hn hs
  let trials := packed_trial hn hs ha hQuiet hTrial
  let origin := packedOrigin (s := s) (n := n) hn hs
  have hp := (packed_advice_iff n).1 (ha ▸ hs)
  have par := packed_parameters hn hs ha
  have serv := packed_service hn hs ha hBlock
  refine ⟨fun hb => (Nat.not_le_of_gt hp hb).elim, ?_, packed_liftCustody hn hs,
    packed_rawStep hn hs, par, serv,
    displaySplit_of_rawDisplay D (by omega) (packed_rawStep hn hs) origin trials,
    missQuarter_of_rawDisplay D (by omega) par serv origin trials (packed_trace_compatibility hn hs),
    fun _ => packed_observer hn hs hObs, fun _ => packed_publicSuffix hn hs C hC⟩
  intro _ x
  change IIDExpectedHittingTimeAtMost ((packedData s n hn hs).next (by omega)) Custody x
    (custodyCoeff g * n^2)
  rw [packed_next hn hs, ← custody_coeff_eq]
  exact hCust x

theorem packed_display_inputs (hn : 4 ≤ n) (hs : 6 ≤ s) (ha : s = ell (ell n))
    (hBlock : ClockServiceSpec.ProductionStrictBlock) (hQuiet : RawLegitOfQuiet)
    (hTrial : ClockDisplaySpec.RawDisplayTrial) :
    let D := packedData s n hn hs
    let origin := packedOrigin (s := s) (n := n) hn hs
    let trials := packed_trial hn hs ha hQuiet hTrial
    PackedDisplayInputs (withDisplayTrials D (by omega) (2^32) origin trials)
      (by omega) (2^32) := by
  let D := packedData s n hn hs
  let trials := packed_trial hn hs ha hQuiet hTrial
  let origin := packedOrigin (s := s) (n := n) hn hs
  have par := packed_parameters hn hs ha
  have serv := packed_service hn hs ha hBlock
  exact ⟨packed_liftCustody hn hs,packed_rawStep hn hs,par,serv,
    displaySplit_of_rawDisplay D (by omega) (packed_rawStep hn hs) origin trials,
    missQuarter_of_rawDisplay D (by omega) par serv origin trials (packed_trace_compatibility hn hs)⟩

/-- An advice value selects exactly one of the two padded alphabets and rows. -/
inductive Deployment where
  | bounded
  | packed (advice : Nat)
  | compactBounded
  | compactPacked (advice : Nat)

def deployment (s : Nat) : Deployment :=
  if 6 ≤ s then .packed s else .bounded

def compactDeployment (s : Nat) : Deployment :=
  if 6 ≤ s then .compactPacked s else .compactBounded

def Deployment.Site : Deployment → Type
  | .bounded => BoundedCode
  | .packed s => PackedSite s
  | .compactBounded => BoundedCode
  | .compactPacked s => PackedCore (BStarTrace.production s (radiusTwo s) (ell (radiusTwo s+1)) (streak s) (streak (radiusTwo s)) (radWidth s) (s+11) 2 12)

noncomputable def Deployment.row (encode : L4.Site boundedP 12 → BoundedCode)
    (decode : BoundedCode → L4.Site boundedP 12) :
    (d : Deployment) → d.Site × d.Site → d.Site × d.Site
  | .bounded => fun ab => boundedPairWith encode decode ab.1 ab.2
  | .packed s => largePair (rows s)
  | .compactBounded => fun ab => boundedPairWith encode decode ab.1 ab.2
  | .compactPacked s => PackedCore.pair (rows s)

noncomputable def Deployment.leader (decode : BoundedCode → L4.Site boundedP 12) :
    (d : Deployment) → d.Site → Bool
  | .bounded => fun a => (decode a).leader
  | .packed s => packedOutput s
  | .compactBounded => fun a => (decode a).leader
  | .compactPacked s => fun a => packedRead s (PackedCore.lift a)

def Deployment.budgetCoefficient (d : Deployment) (g patrol : Nat) :=
  match d with
  | .bounded | .packed _ => timeCoeff g (2^32) patrol
  | .compactBounded | .compactPacked _ => compactTimeCoeff g (2^32) patrol

/-- The physical conclusion uses the ordered pair rule and the final public output
at the same advice, and asks for one physical winner on every future word. -/
def Deployment.Expected (d : Deployment) (encode : L4.Site boundedP 12 → BoundedCode)
    (decode : BoundedCode → L4.Site boundedP 12) (n : Nat) (hn : 4 ≤ n) (g patrol : Nat) : Prop :=
  let next := PopulationProtocol.step
    ⟨d.Site, Bool, (fun a b => d.row encode decode (a,b)), d.leader decode⟩ (⟨by omega⟩ : DirectedRing n)
  ∀ x, UniformFirstHit.ExpectedHittingTimeAtMost next
    (Permanent next (fun y i => d.leader decode (y i))) x
    ((d.budgetCoefficient g patrol * n^2 : Nat) : Rat)

/-- The custody interface supplies a uniform custody coefficient. The verified rooted public
row supplies its own uniform coefficient from each completed handoff. -/
theorem all_sizes_expected_of_parts (custody : CustodyReached)
    (service : ClockServiceSpec.ProductionStrictBlock)
    (display : ClockDisplaySpec.RawDisplayTrial) (observerMean : PackedObserverMean) :
    ∃ g patrol : Nat, ∀ n (hn : 4 ≤ n),
      (deployment (ceilingLogTwo (ceilingLogTwo n))).Expected
        boundedEncode boundedDecode n hn g patrol := by
  obtain ⟨g,hg⟩ := custody
  obtain ⟨C,hPack,hBound⟩ := production_public_suffixes
  refine ⟨g,patrolAllowance C,?_⟩
  intro n hn
  let s := ceilingLogTwo (ceilingLogTwo n)
  change (deployment s).Expected boundedEncode boundedDecode n hn g (patrolAllowance C)
  have ha : s = ell (ell n) := rfl
  by_cases hs : 6 ≤ s
  · rw [deployment,if_pos hs]
    intro x
    exact physical_expected _ hn
      (packed_interfaces hn hs ha g C (hg hn hs ha) service packed_quiet display observerMean (hPack hn)) x
  · rw [deployment,if_neg hs]
    have hb : n ≤ boundedN := Nat.le_of_not_gt (fun h => hs ((packed_advice_iff n).2 h))
    intro x
    exact physical_expected _ hn
      (bounded_interfaces boundedEncode boundedDecode hn hb g C (hBound hn hb)) x

end Family

end L4.Height.AllSizeWire
