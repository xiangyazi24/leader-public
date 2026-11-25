import Leader.L4.Height.CycleBudget
import Leader.L4.Height.CandidatePolicy
import Leader.L4.Height.ProductionInvariant

namespace L4.Height.ProductionCycles
open AllSizeProtocol PhysicalCustody ProductionCustody BStarSteeredLikelihood BStarH6WordChart
open BStarAcquireAnchors BStarAcquireLiteralChain
open Classical
noncomputable section

variable {s n : Nat} {x : Raw s n} (g : CustodyWitness x)
local notation "h" => oldH6 (rows s) g.base

/-- Four cyclic rivals in chart order followed by the incumbent target. -/
def releaseClient (o : Owners h) : Nat → Owners h
  | 0 => ProductionClients.client h g.hh o 0
  | 1 => ProductionClients.client h g.hh o 1
  | 2 => ProductionClients.client h g.hh o 3
  | 3 => ProductionClients.client h g.hh o 4
  | _ => o

/-- Every nonzero cut ends exactly at the last accepted release, so the
fresh target starts at its own clean ISSUE3 after the four rival cuts. -/
inductive Releases (o : Owners h) : Nat → Word n → Prop
  | initial : Releases o 0 []
  | receipt {j a} (past : Releases o j a) (gap : Word n) (e : Fin n)
      (paid : accepted g (releaseClient g o j) (a++gap) e) :
      Releases o (j+1) ((a++gap)++[e])

def liveAll (o : Owners h) := CandidateResidence.live (g:=g) o (fun _ _ => True)

def policy (i : Header h) :=
  chooseBy (ProductionClients.redirect g (ProductionClients.serviceOwner g i)
    (liveAll g (ProductionClients.serviceOwner g i)))

def stage (i : Header h) (k : Nat) (y : History s n) : Prop :=
  Consistent x (policy g i) i.val y ∧
    if k=0 then y.published else Releases g (ProductionClients.serviceOwner g i) (6-k) y.emitted

/-- Projection and clock bound for a single stopped physical cycle. -/
def Cycle (i : Header h) (y : History s n) (goal : History s n → Prop) : Prop :=
  ∃ (U : Type) (D : ResidualPotentialData (S:=U) (n:=n)) (proj : U → History s n) (z : U),
    proj z=y ∧ D.Q z ∧ D.Phi z≤2^15*n*width g ∧
    (∀ u,D.Q u → ¬D.P u → ∀ e,proj (D.next u e)=next (policy g i) i.val (proj u) e) ∧
    (D.P z → goal (proj z)) ∧
    ∀ u,D.Q u → ¬D.P u → ∀ e,D.P (D.next u e) → goal (proj (D.next u e))

theorem Cycle.mono {i : Header h} {y : History s n} {A B : History s n → Prop}
    (C : Cycle g i y A) (incl : ∀ t,A t → B t) : Cycle g i y B := by
  obtain ⟨U,D,proj,z,eq,q,small,step,start,hit⟩ := C
  exact ⟨U,D,proj,z,eq,q,small,step,fun p => incl _ (start p),
    fun u qu off e pu => incl _ (hit u qu off e pu)⟩

theorem Cycle.expected {i : Header h} {y : History s n} {A : History s n → Prop}
    (C : Cycle g i y A) : IIDExpectedHittingTimeAtMost (next (policy g i) i.val) A y (2^15*n*width g) := by
  obtain ⟨U,D,proj,z,eq,q,small,step,start,hit⟩ := C
  rw [←eq]
  exact ResidualStages.projected_first_entrance D proj _ A step hit z q start small

/-- Five real RREL stops and one first successful fresh cycle imply the
raw block on the always-enabled fresh-request policy, including four-owner rings. -/
theorem block_of_releases (P : Production g) (i : Header h)
    (release : ∀ j,j<5 → ∀ y,Consistent x (policy g i) i.val y →
      Releases g (ProductionClients.serviceOwner g i) j y.emitted →
      Cycle g i y (fun z => z.published ∨ Consistent x (policy g i) i.val z ∧
        ∃ gap e,z.emitted=(y.emitted++gap)++[e] ∧
          accepted g (releaseClient g (ProductionClients.serviceOwner g i) j) (y.emitted++gap) e))
    (fresh : ∀ y,Consistent x (policy g i) i.val y →
      Releases g (ProductionClients.serviceOwner g i) 5 y.emitted → Cycle g i y History.published) :
    let t := 2*(2^20*n*width g)
    n^t ≤ 2^(5*longBudget+1)*wordSum (fun w =>
      if RawServiceCore.publishes x i.val w then 1 else 0) t := by
  let target := ProductionClients.serviceOwner g i
  apply block_of_stage_means g P i target (liveAll g target) (stage g i)
  · intro y atStage
    exact (show stage g i 0 y from atStage).2
  · exact ⟨consistent_start ..,Releases.initial⟩
  · intro k hk y hy
    obtain ⟨ok,old⟩ := hy
    have past : Releases g target (6-(k+1)) y.emitted := by
      simpa only [Nat.succ_ne_zero,if_false] using old
    apply Cycle.expected g
    by_cases last : k=0
    · subst k
      exact Cycle.mono g (fresh y ok past) (fun _ p => .inr p)
    · apply Cycle.mono g (release (6-(k+1)) (by omega) y ok past)
      intro z ended
      rcases ended with pub|⟨clean,gap,e,marks,paid⟩
      · exact .inr pub
      · apply Or.inl
        refine ⟨clean,?_⟩
        rw [if_neg last,marks,show 6-k=(6-(k+1))+1 by omega]
        exact .receipt past gap e paid

/-- The sixth stage can reuse the same target RREL clock. Its extra obligation
is a finite-word statement: a complete new target cycle after those five cuts
must have published on or before its own next physical RREL. -/
theorem block_of_release_safety (P : Production g) (i : Header h)
    (release : ∀ o : Owners h, ∀ y,Consistent x (policy g i) i.val y →
      Cycle g i y (fun z => z.published ∨ Consistent x (policy g i) i.val z ∧
        ∃ gap e,z.emitted=(y.emitted++gap)++[e] ∧ accepted g o (y.emitted++gap) e))
    (safe : ∀ y,Consistent x (policy g i) i.val y →
      Releases g (ProductionClients.serviceOwner g i) 5 y.emitted →
      ∀ z,Consistent x (policy g i) i.val z → ∀ gap e,
        z.emitted=(y.emitted++gap)++[e] →
        accepted g (ProductionClients.serviceOwner g i) (y.emitted++gap) e →
        z.published) :
    let t := 2*(2^20*n*width g)
    n^t ≤ 2^(5*longBudget+1)*wordSum (fun w =>
      if RawServiceCore.publishes x i.val w then 1 else 0) t := by
  apply block_of_releases g P i
  · intro j _ y ok _
    exact release _ y ok
  · intro y ok cuts
    apply Cycle.mono g (release (ProductionClients.serviceOwner g i) y ok)
    intro z terminal
    rcases terminal with pub|⟨hz,gap,e,atEnd,receipt⟩
    · exact pub
    · exact safe y ok cuts z hz gap e atEnd receipt

#print axioms block_of_release_safety
#print axioms block_of_releases
end
end L4.Height.ProductionCycles

