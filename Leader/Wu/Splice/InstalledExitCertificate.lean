import Std
import Leader.Wu.Splice.NeutralRow
import Leader.Wu.Splice.SealedLaneRecoveryMoves
import Leader.Wu.Coherence.AllOpenPairMoves


set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096


namespace ZZSCCCertificate


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair WriterProducerRepair
open Q11593SpliceControllerDesign
open R2CoherenceV31


private theorem h3 : 0 < 3 := by omega
private theorem h23 : 2 ≤ 3 := by omega


/-!
## 1. Exact finite keys


`CellP` itself has no derived DecidableEq.  Rather than install an orphan global
instance, copy its four fields exactly.  The physical field is the *complete*
V3.1 cell, so this key includes the bounded core, path0Crossed, stall, fuel,
mark and TokenV3, plus the three outer B9 fields.
-/


structure PackedCell where
  phys : R2CoherenceV31.Cell 3 3 48
  spliceRole : SpliceRole
  repairPending : Bool
  acquireTicket : Bool
  deriving DecidableEq


namespace PackedCell


def ofFinal (u : ZZFinalCarrierV3.Cell 3 3 48) : PackedCell :=
  ⟨u.phys, u.spliceRole, u.repairPending, u.acquireTicket⟩


def toFinal (u : PackedCell) : ZZFinalCarrierV3.Cell 3 3 48 :=
  ⟨u.phys, u.spliceRole, u.repairPending, u.acquireTicket⟩


@[simp] theorem toFinal_ofFinal
    (u : ZZFinalCarrierV3.Cell 3 3 48) :
    toFinal (ofFinal u) = u := by
  cases u
  rfl


@[simp] theorem ofFinal_toFinal (u : PackedCell) :
    ofFinal (toFinal u) = u := by
  cases u
  rfl


end PackedCell


private theorem fin6_cases (i : Fin 6) :
    i = (0 : Fin 6) ∨ i = 1 ∨ i = 2 ∨
      i = 3 ∨ i = 4 ∨ i = 5 := by
  have hi : i.val < 6 := i.isLt
  have hv :
      i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨
        i.val = 3 ∨ i.val = 4 ∨ i.val = 5 := by
    omega
  rcases hv with h | h | h | h | h | h
  · left; apply Fin.ext; exact h
  · right; left; apply Fin.ext; exact h
  · right; right; left; apply Fin.ext; exact h
  · right; right; right; left; apply Fin.ext; exact h
  · right; right; right; right; left; apply Fin.ext; exact h
  · right; right; right; right; right; apply Fin.ext; exact h


/-- Full exact n=6 installed configuration key. -/
structure Packed6 where
  c0 : PackedCell
  c1 : PackedCell
  c2 : PackedCell
  c3 : PackedCell
  c4 : PackedCell
  c5 : PackedCell
  deriving DecidableEq


namespace Packed6


def ofConfig (C : ZZFinalCarrierV3.Config 6 3 3 48) : Packed6 :=
  ⟨PackedCell.ofFinal (C 0), PackedCell.ofFinal (C 1),
   PackedCell.ofFinal (C 2), PackedCell.ofFinal (C 3),
   PackedCell.ofFinal (C 4), PackedCell.ofFinal (C 5)⟩


def toConfig (C : Packed6) : ZZFinalCarrierV3.Config 6 3 3 48 :=
  fun i =>
    match i.val with
    | 0 => C.c0.toFinal
    | 1 => C.c1.toFinal
    | 2 => C.c2.toFinal
    | 3 => C.c3.toFinal
    | 4 => C.c4.toFinal
    | _ => C.c5.toFinal


@[simp] theorem ofConfig_toConfig (C : Packed6) :
    ofConfig (toConfig C) = C := by
  cases C
  rfl


@[simp] theorem toConfig_ofConfig
    (C : ZZFinalCarrierV3.Config 6 3 3 48) :
    toConfig (ofConfig C) = C := by
  funext i
  rcases fin6_cases i with h | h | h | h | h | h
  all_goals subst i
  all_goals rfl


end Packed6


/-- Exact n=6 inner key used by the computable HOST-class mirror. -/
structure Inner6 where
  c0 : R2CoherenceV31.Cell 3 3 48
  c1 : R2CoherenceV31.Cell 3 3 48
  c2 : R2CoherenceV31.Cell 3 3 48
  c3 : R2CoherenceV31.Cell 3 3 48
  c4 : R2CoherenceV31.Cell 3 3 48
  c5 : R2CoherenceV31.Cell 3 3 48
  deriving DecidableEq


namespace Inner6


def ofConfig (C : R2CoherenceV31.FC 6 3 3 48) : Inner6 :=
  ⟨C 0, C 1, C 2, C 3, C 4, C 5⟩


def toConfig (C : Inner6) : R2CoherenceV31.FC 6 3 3 48 :=
  fun i =>
    match i.val with
    | 0 => C.c0
    | 1 => C.c1
    | 2 => C.c2
    | 3 => C.c3
    | 4 => C.c4
    | _ => C.c5


@[simp] theorem ofConfig_toConfig (C : Inner6) :
    ofConfig (toConfig C) = C := by
  cases C
  rfl


@[simp] theorem toConfig_ofConfig
    (C : R2CoherenceV31.FC 6 3 3 48) :
    toConfig (ofConfig C) = C := by
  funext i
  rcases fin6_cases i with h | h | h | h | h | h
  all_goals subst i
  all_goals rfl


/-- Put the complete inner cells under the exact neutral B9 wrapper. -/
def neutral (C : Inner6) : Packed6 :=
  ⟨⟨C.c0, .none, false, false⟩,
   ⟨C.c1, .none, false, false⟩,
   ⟨C.c2, .none, false, false⟩,
   ⟨C.c3, .none, false, false⟩,
   ⟨C.c4, .none, false, false⟩,
   ⟨C.c5, .none, false, false⟩⟩


end Inner6


/-- Forget only the outer wrapper; retain the entire physical V3 cell. -/
def Packed6.inner (C : Packed6) : Inner6 :=
  ⟨C.c0.phys, C.c1.phys, C.c2.phys,
   C.c3.phys, C.c4.phys, C.c5.phys⟩


/-- Exact n=2 key for the compiled sealed recovery fixture. -/
structure Packed2 where
  c0 : PackedCell
  c1 : PackedCell
  deriving DecidableEq


namespace Packed2


def ofConfig (C : ZZFinalCarrierV3.Config 2 3 3 48) : Packed2 :=
  ⟨PackedCell.ofFinal (C 0), PackedCell.ofFinal (C 1)⟩


end Packed2


/-!
## 2. Decidable scheduler / HOST-class step


The installed wrapper is noncomputable, but the inner V3 row is executable.
For a neutral HOST-certified class, this is the finite model step to use; bridge
it to `stepConcreteV3` with `ZZNeutralRow` theorems.
-/


def ring6 : DirectedRing 6 := ZZOrbitLiftClean.ring6


def edges6 : List (Fin 6) := [0, 1, 2, 3, 4, 5]


@[simp] theorem edges6_complete (e : Fin 6) : e ∈ edges6 := by
  rcases fin6_cases e with h | h | h | h | h | h
  all_goals subst e
  all_goals simp [edges6]


def hostStep (C : Inner6) (e : Fin 6) : Inner6 :=
  Inner6.ofConfig
    (R2CoherenceV31.stepV3 h3 h23 ring6 C.toConfig e)


/-- Executable packed model for the neutral HOST class. -/
def hostModelStep (C : Packed6) (e : Fin 6) : Packed6 :=
  (hostStep C.inner e).neutral


/-!
## 3. Exact finite witness shell


The orbit part is reconstructed by the exact executable services rather than by
copying a 102-entry table.  This yields the 17 distinct temporal states and all
six first successors of each.
-/


def orbitBase : Inner6 := Inner6.ofConfig ZZNeutralRow.innerC


def orbitA1 : Inner6 := hostStep orbitBase 0
def orbitA2 : Inner6 := hostStep orbitA1 0
def orbitA3 : Inner6 := hostStep orbitA2 0
def orbitA4 : Inner6 := hostStep orbitA3 1
def orbitA5 : Inner6 := hostStep orbitA4 1
def orbitA6 : Inner6 := hostStep orbitA5 0
def orbitA7 : Inner6 := hostStep orbitA6 0
def orbitA8 : Inner6 := hostStep orbitA7 0


def orbitB1 : Inner6 := hostStep orbitBase 3
def orbitB2 : Inner6 := hostStep orbitB1 3
def orbitB3 : Inner6 := hostStep orbitB2 3
def orbitB4 : Inner6 := hostStep orbitB3 4
def orbitB5 : Inner6 := hostStep orbitB4 4
def orbitB6 : Inner6 := hostStep orbitB5 3
def orbitB7 : Inner6 := hostStep orbitB6 3
def orbitB8 : Inner6 := hostStep orbitB7 3


def orbitPhases : List Inner6 :=
  [orbitBase,
   orbitA1, orbitA2, orbitA3, orbitA4,
   orbitA5, orbitA6, orbitA7, orbitA8,
   orbitB1, orbitB2, orbitB3, orbitB4,
   orbitB5, orbitB6, orbitB7, orbitB8]


def successors6 (C : Inner6) : List Inner6 :=
  edges6.map (hostStep C)


/-- Exact public copy of the private clean all-open physical literal. -/
def literalFollower (lab : Fin 3) : R2.Cell 3 3 48 :=
  let seed := WriterProducerRegression.clean h3 (fun _ => false) lab
  let b := seed.base.core.core
  let b' : BoundedAgentState 3 3 :=
    { b with
      leader := false
      shield := false
      gen_ws := false
      label := lab
      state := .none
      path := .bot
      bit := false
      path2 := none
      path3 := none
      path4 := none
      path5 := none
      p := false
      p_carry := false
      reset_cmd := false
      echo := false
      write_state := .none
      write := .none
      b_carry := false }
  ⟨⟨⟨b', false⟩, 48⟩, 0⟩


/-- The exact local all-open cell used by `ZZAllOpenPair`. -/
def allOpenCell (lab : Fin 3) : R2CoherenceV31.Cell 3 3 48 :=
  ⟨literalFollower lab, ⟨.open, .none⟩⟩


/-- Six-cell cyclic clean ruler containing both 0→1 and 2→0 open pair shapes. -/
def allOpenRuler6 : Inner6 :=
  ⟨allOpenCell 0, allOpenCell 1, allOpenCell 2,
   allOpenCell 0, allOpenCell 1, allOpenCell 2⟩


/-- Orbit + every first HOST successor + all-open ruler + its six first HOST successors. -/
def hostInnerFragment : List Inner6 :=
  orbitPhases.flatMap (fun C => C :: successors6 C) ++
    (allOpenRuler6 :: successors6 allOpenRuler6)


def neutralHost6 : List Packed6 :=
  hostInnerFragment.map Inner6.neutral


/-- Native n=2 sealed source and the two exact installed recovery successors. -/
def sealedRecovery2 : List Packed2 :=
  [Packed2.ofConfig ZZV31SealedInstalled.C,
   Packed2.ofConfig (ZZV31SealedInstalled.recoveredAt 0),
   Packed2.ofConfig (ZZV31SealedInstalled.recoveredAt 1)]


/-- The two fixed-n fibers are kept separate: SCC reachability is a fixed-n question. -/
structure WitnessFragment where
  neutralHost6 : List Packed6
  sealedRecovery2 : List Packed2




def witnessFragment : WitnessFragment :=
  ⟨neutralHost6, sealedRecovery2⟩


/-- Decidable membership checks for the two exact finite fibers. -/
def hostMemberB (C : Packed6) : Bool :=
  decide (C ∈ witnessFragment.neutralHost6)


def recovery2MemberB (C : Packed2) : Bool :=
  decide (C ∈ witnessFragment.sealedRecovery2)


/-!
## 4. Bounded reachability


`reachWithinStates k x` contains every state reachable from `x` in at most `k`
letters from the explicit scheduler list.  Duplicates are harmless for the
logical checker; a production BFS can add `eraseDups` after establishing a
structural DecidableEq key.
-/


universe u v




def oneStepImage {S : Type u} {E : Type v}
    (step : S → E → S) (edges : List E) (xs : List S) : List S :=
  xs.flatMap (fun x => edges.map (step x))




def reachWithinStates {S : Type u} {E : Type v}
    (step : S → E → S) (edges : List E) : Nat → S → List S
  | 0, x => [x]
  | Nat.succ k, x =>
      let old := reachWithinStates step edges k x
      old ++ oneStepImage step edges old




def ReachWithin {S : Type u} {E : Type v}
    (step : S → E → S) (edges : List E)
    (k : Nat) (x y : S) : Prop :=
  y ∈ reachWithinStates step edges k x




def Reachable {S : Type u} {E : Type v}
    (step : S → E → S) (edges : List E)
    (x y : S) : Prop :=
  ∃ k, ReachWithin step edges k x y




@[simp] theorem reachWithin_zero_iff
    {S : Type u} {E : Type v}
    (step : S → E → S) (edges : List E) (x y : S) :
    ReachWithin step edges 0 x y ↔ y = x := by
  simp [ReachWithin, reachWithinStates]


/-- Requested SCC-exit shape at a concrete bound K. -/
def ExitWithin {S : Type u} {E : Type v}
    (step : S → E → S) (edges : List E)
    (K : Nat) (C : S) : Prop :=
  ∃ e : E, ∀ k, k ≤ K →
    ¬ ReachWithin step edges k (step C e) C


/-- For a finite fragment the canonical diagnostic bound. -/
def fragmentK {S : Type u} (states : List S) : Nat :=
  states.length


/-- Every state of the fragment exits within `fragmentK states` steps. -/
def FragmentExitAt {S : Type u} {E : Type v}
    (step : S → E → S) (edges : List E)
    (states : List S) : Prop :=
  ∀ C, C ∈ states → ExitWithin step edges (fragmentK states) C


/-!
## 5. Stronger finite return-avoidance certificate


This is the preferred certificate object.  It proves no return for *all* k,
not merely through K, while still being checkable from one finite list.
-/


structure ReturnAvoidCertificate
    {S : Type u} {E : Type v}
    (step : S → E → S) (edges : List E)
    (start target : S) where
  states : List S
  start_mem : start ∈ states
  target_not_mem : target ∉ states
  closed :
    ∀ x, x ∈ states →
      ∀ e, e ∈ edges →
        step x e ∈ states




theorem reachableWithin_mem_certificate
    {S : Type u} {E : Type v}
    {step : S → E → S} {edges : List E}
    {start target : S}
    (cert : ReturnAvoidCertificate step edges start target) :
    ∀ k y, ReachWithin step edges k start y → y ∈ cert.states := by
  intro k
  induction k with
  | zero =>
      intro y hy
      have hy' : y = start :=
        (reachWithin_zero_iff step edges start y).mp hy
      subst y
      exact cert.start_mem
  | succ k ih =>
      intro y hy
      change y ∈ reachWithinStates step edges (Nat.succ k) start at hy
      simp only [reachWithinStates] at hy
      rcases List.mem_append.mp hy with hold | hnew
      · exact ih y hold
      · unfold oneStepImage at hnew
        rcases List.mem_flatMap.mp hnew with ⟨x, hx, hmap⟩
        rcases List.mem_map.mp hmap with ⟨e, he, hxy⟩
        cases hxy
        exact cert.closed x (ih x hx) e he




theorem certificate_no_return
    {S : Type u} {E : Type v}
    {step : S → E → S} {edges : List E}
    {start target : S}
    (cert : ReturnAvoidCertificate step edges start target) :
    ∀ k, ¬ ReachWithin step edges k start target := by
  intro k hk
  exact cert.target_not_mem
    (reachableWithin_mem_certificate cert k target hk)




theorem certificate_not_reachable
    {S : Type u} {E : Type v}
    {step : S → E → S} {edges : List E}
    {start target : S}
    (cert : ReturnAvoidCertificate step edges start target) :
    ¬ Reachable step edges start target := by
  rintro ⟨k, hk⟩
  exact certificate_no_return cert k hk




theorem exitWithin_of_certificate
    {S : Type u} {E : Type v}
    {step : S → E → S} {edges : List E}
    {C : S} (K : Nat) (e : E)
    (cert : ReturnAvoidCertificate step edges (step C e) C) :
    ExitWithin step edges K C := by
  refine ⟨e, ?_⟩
  intro k hk
  exact certificate_no_return cert k


/-!
## 6. Executable bounded diagnostics


These are useful for discovering candidate certificates.  The theorem above is
the final logical bridge: after BFS reaches a fixed point, package that list as
`ReturnAvoidCertificate` instead of trusting a large opaque Boolean.
-/




def ReachWithinB {S : Type u} {E : Type v}
    [DecidableEq S]
    (step : S → E → S) (edges : List E)
    (k : Nat) (x y : S) : Bool :=
  decide (y ∈ reachWithinStates step edges k x)




def noReturnThroughB {S : Type u} {E : Type v}
    [DecidableEq S]
    (step : S → E → S) (edges : List E)
    (child parent : S) : Nat → Bool
  | 0 => !(ReachWithinB step edges 0 child parent)
  | Nat.succ k =>
      noReturnThroughB step edges child parent k &&
        !(ReachWithinB step edges (Nat.succ k) child parent)




def ExitWithinB {S : Type u} {E : Type v}
    [DecidableEq S]
    (step : S → E → S) (edges : List E)
    (K : Nat) (C : S) : Bool :=
  edges.any (fun e =>
    noReturnThroughB step edges (step C e) C K)




def forwardClosedB {S : Type u} {E : Type v}
    [DecidableEq S]
    (step : S → E → S) (edges : List E)
    (states : List S) : Bool :=
  states.all (fun x =>
    edges.all (fun e => decide (step x e ∈ states)))




def returnAvoidB {S : Type u} {E : Type v}
    [DecidableEq S]
    (step : S → E → S) (edges : List E)
    (start target : S) (states : List S) : Bool :=
  decide (start ∈ states) &&
    !(decide (target ∈ states)) &&
    forwardClosedB step edges states


/-- Concrete K for the current n=6 HOST witness shell. -/
def neutralHostK : Nat := fragmentK neutralHost6


/-- Cheap closure diagnostic: expected to be false until the depth-5 physical cone is added. -/
def neutralHostClosedB : Bool :=
  forwardClosedB hostModelStep edges6 neutralHost6


/-!
## 7. First installed class: exact sealed recovery source


This is an *installed* step, not the HOST mirror.  The repository already proves
both exact one-step successors.  K=0 is therefore a kernel-backed smoke
certificate for the requested ReachWithin interface.  It is intentionally not
presented as a complete SCC-exit certificate: a return after one or more later
services is still open until the recovery successor cone is closed.
-/




def edges2 : List (Fin 2) := [0, 1]


noncomputable def sealedInstalledStep :
    ZZFinalCarrierV3.Config 2 3 3 48 → Fin 2 →
      ZZFinalCarrierV3.Config 2 3 3 48 :=
  ZZFinalCarrierV3.stepConcreteV3
    (κ := 3) (τ := 48) h3 h23 ZZV31SealedInstalled.ring2




theorem sealed_edge0_exact :
    sealedInstalledStep ZZV31SealedInstalled.C 0 =
      ZZV31SealedInstalled.recoveredAt 0 := by
  simpa [sealedInstalledStep] using
    ZZV31SealedInstalled.step0_eq_recovered




theorem sealed_edge1_exact :
    sealedInstalledStep ZZV31SealedInstalled.C 1 =
      ZZV31SealedInstalled.recoveredAt 1 := by
  simpa [sealedInstalledStep] using
    ZZV31SealedInstalled.step1_eq_recovered


/-- First concrete bound: the exact successor is not the source at depth zero. -/
theorem sealed_source_exit_K0 :
    ExitWithin sealedInstalledStep edges2 0 ZZV31SealedInstalled.C := by
  refine ⟨(0 : Fin 2), ?_⟩
  intro k hk
  have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
  subst k
  rw [reachWithin_zero_iff]
  have hmove :
      sealedInstalledStep ZZV31SealedInstalled.C 0 ≠
        ZZV31SealedInstalled.C := by
    simpa [sealedInstalledStep] using
      ZZV31SealedInstalled.step0_moves
  intro hback
  exact hmove hback.symm


end ZZSCCCertificate
