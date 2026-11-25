import Leader.L4.PhysicalCustodyTwoPass
import Leader.L4.PhysicalCustodyQuadratic

namespace L4.PhysicalCustody
open BStarTrace BStarH6WordChart BStarAcquireLiteralChain BStarOwnerRecoveryPass
open PhysicalCustodySampledPass
local notation "hp" => (show 0<2 by decide)

def extendTape {n : Nat} (w : List (Fin n)) (e : Fin n) := w++[e]

private theorem replay_step {s n : Nat} (x : Raw s n) (w : List (Fin n)) (e : Fin n) :
    rawRun x (extendTape w e) = rawNext s (rawRun x w) e :=
  BStarResetSchedule.run_append (rawNext s) x w [e]

private theorem replay_closed {s n : Nat} (Q : Raw s n → Prop)
    (closed : ∀ x e, Q x → Q (rawNext s x e)) {x : Raw s n} (H : Q x)
    (w : List (Fin n)) : Q (rawRun x w) := by
  induction w generalizing x with
  | nil => exact H
  | cons e w ih => exact ih (closed x e H)

private theorem append_observer {n : Nat} (P S : List (Fin n) → Prop)
    (a : List (Fin n)) (forward : ∀ b, P b → S (a++b)) (C : Nat)
    (bound : IIDExpectedHittingTimeAtMost extendTape P [] C) :
    IIDExpectedHittingTimeAtMost extendTape S a C := by
  intro t
  simpa only [List.append_nil] using Nat.le_trans (EntranceCover.iidHitCost_le_of_projection extendTape extendTape S P
    (a++·) (fun _ _ => (List.append_assoc ..).symm) forward t []) (bound t)

def firstCredit {s n : Nat} {O : Type}
    (E : O → Raw s n → List (Fin n) → Prop) (o : O) (x : Raw s n)
    (w : List (Fin n)) : Prop :=
  ∃ v, Commuted w v ∧ 0<v.length ∧ E o x v

def passTarget {s n : Nat} {O : Type}
    (E : O → Raw s n → List (Fin n) → Prop) (os : List O) (x : Raw s n)
    (w : List (Fin n)) : Prop :=
  ∃ v, Pass E x os w v

/-- Run local first-hit clocks on successive suffixes of one physical
tape. Each replay commutes only its own local segment. -/
theorem owner_pass_mean {s n : Nat} {O : Type}
    (E : O → Raw s n → List (Fin n) → Prop) (Q : Raw s n → Prop)
    (closed : ∀ x e, Q x → Q (rawNext s x e)) (A : Nat) (os : List O)
    (localMean : ∀ o∈os, ∀ x, Q x →
      IIDExpectedHittingTimeAtMost extendTape (firstCredit E o x) [] A)
    (x : Raw s n) (hx : Q x) :
    IIDExpectedHittingTimeAtMost extendTape (passTarget E os x) [] (os.length*A) := by
  induction os generalizing x with
  | nil =>
    intro t
    rw [iidHitCost_of_target _ _ _ (show passTarget E [] x [] from ⟨[],Pass.nil x⟩)]
    exact Nat.zero_le _
  | cons o os ih =>
    rw [List.length_cons,Nat.succ_mul,Nat.add_comm]
    refine add_hitting_bounds extendTape (firstCredit E o x) _ [] A _
      (localMean o (by simp) x hx) ?_
    intro w hw
    obtain ⟨v,comm,positive,credit⟩ := hw
    apply append_observer (passTarget E os (rawRun x w)) _ w
    · rintro b ⟨r,P⟩
      exact ⟨v++r, Pass.cons comm positive credit P⟩
    · exact ih (fun p mem => localMean p (List.mem_cons_of_mem _ mem)) _
        (replay_closed Q closed hx w)

/-- Two actual sequential owner passes are enough for bare Custody even
if neither sampled pass contains a contiguous credited segment. -/
theorem two_owner_passes_mean {s n : Nat} {z : Raw s n}
    (g : ReadyAfterCovers z) (A : Nat)
    (localMean : ∀ o : Owners (oldH6 (rows s) z), ∀ x, g.Q x →
      IIDExpectedHittingTimeAtMost extendTape (firstCredit (HoldsCredit (Recovered hp z g.hh)) o x) [] A) :
    IIDExpectedHittingTimeAtMost (rawNext s) Custody z (2*(total (oldH6 (rows s) z)*A)) := by
  let E := HoldsCredit (Recovered hp z g.hh)
  let os := ownerOrder (oldH6 (rows s) z)
  let C := os.length*A
  have times (x : Raw s n) (hx : g.Q x) :
      IIDExpectedHittingTimeAtMost extendTape (passTarget E os x) [] C :=
    owner_pass_mean E g.Q g.closed A os (fun o _ => localMean o) x hx
  have endMean : IIDExpectedHittingTimeAtMost extendTape
      (fun w => Custody (rawRun z w)) [] (C+C) := by
    refine add_hitting_bounds extendTape (passTarget E os z) _ [] C C (times z g.qz) ?_
    rintro u ⟨u',hF⟩
    apply append_observer (passTarget E os (rawRun z u)) _ u
    · rintro v ⟨v',G⟩
      exact custody_of_two_credited_passes g hF G
    · exact times _ (replay_closed g.Q g.closed g.qz u)
  have ee : C+C=2*(total (oldH6 (rows s) z)*A) := by
    simp [C,os,ownerOrder,Nat.two_mul]
  rw [←ee]
  exact fun t => Nat.le_trans
    (EntranceCover.iidHitCost_le_of_projection (rawNext s) extendTape Custody
      (fun w => Custody (rawRun z w)) (rawRun z) (replay_step z) (fun _ h => h) t [])
    (endMean t)

/-- The packed chart pays for both passes: the uniform per-owner rate
may be linear in the radWidth without losing a logarithmic factor. -/
theorem two_owner_passes_quadratic {s n : Nat} {z : Raw s n}
    (g : ReadyAfterCovers z) (K : Nat)
    (localMean : ∀ o : Owners (oldH6 (rows s) z), ∀ x, g.Q x →
      IIDExpectedHittingTimeAtMost extendTape
        (firstCredit (HoldsCredit (Recovered hp z g.hh)) o x) [] (K*n*radWidth s)) :
    IIDExpectedHittingTimeAtMost (rawNext s) Custody z ((2*K)*n^2) := by
  apply TripleRenewal.expected_mono (two_owner_passes_mean g _ localMean)
  have pack := Nat.mul_le_mul_left (2*K*n) g.packed
  simpa only [Nat.pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using pack

#print axioms owner_pass_mean
#print axioms two_owner_passes_mean
#print axioms two_owner_passes_quadratic
end L4.PhysicalCustody
