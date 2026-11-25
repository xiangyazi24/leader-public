import Leader.L4.PhysicalCustodyH1Domination
import Leader.L4.PhysicalCustodyH1TwoCovers

namespace L4.PhysicalCustody.H1
open L4.AllSizeS1Geometry L4.PhysicalCustody L4.AllSizeProtocol
open K2ArbitraryElimination.FiniteAccounting

def rawMaximal {s n : Nat} (x : Raw s n) : Prop := maximal (projection x)

private theorem no_short_wrap {n d : Nat} (D : 0 < d) (N : d < n) (i : Fin n) :
    (i.val+d)%n ≠ i.val := by
  intro E
  have hi := i.isLt
  by_cases L : i.val+d<n
  · rw [Nat.mod_eq_of_lt L] at E
    omega
  · have H : n ≤ i.val+d := by omega
    have B : i.val+d-n<n := by omega
    rw [Nat.mod_eq_sub_mod H, Nat.mod_eq_of_lt B] at E
    omega

private theorem sep_ring {n : Nat} (N : 5≤n) (i : Fin n) :
    i≠rightNeighbor i ∧ i≠rightNeighbor (rightNeighbor i) := by
  constructor
  · intro E
    exact no_short_wrap (d:=1) (by omega) (by omega) i (congrArg Fin.val E.symm)
  · intro E
    have H := congrArg Fin.val E.symm
    change ((i.val+1)%n+1)%n=i.val at H
    have K : ((i.val+1)%n+1)%n=(i.val+1+1)%n := by
      rw [Nat.add_mod (i.val+1) 1 n]
      simp [Nat.mod_eq_of_lt (show 1<n by omega)]
    rw [K,show i.val+1+1=i.val+2 by omega] at H
    exact no_short_wrap (d:=2) (by omega) (by omega) i H

private theorem physical_cost {s n : Nat} (x : Raw s n) (P : State n → Prop) (t : Nat) :
    L4.iidHitCost (rawNext s) (fun y => P (projection y)) t x =
      L4.iidHitCost physicalStep P t (projection x) := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    simp only [L4.iidHitCost]
    split
    · rfl
    · congr 1
      apply FiniteUniformStoppingTree.ofFn_sum_eq
      intro e
      rw [ih]
      have E : projection (rawNext s x e)=physicalStep (projection x) e :=
        funext (exact_physical_projection (rows s) x e)
      rw [E]

private theorem raw_runWord {s n : Nat} (x : Raw s n) (w : List (Fin n)) :
    L4.Height.runWord (rawNext s) x w=rawRun x w := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih => exact ih (rawNext s x e)

private theorem height_cost {X : Type} {n : Nat} (step : X → Fin n → X)
    (P : X → Prop) (t : Nat) (x : X) :
    L4.iidHitCost step P t x=L4.Height.iidHitCost step P t x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    by_cases H : P x
    · simp only [L4.iidHitCost,L4.Height.iidHitCost,if_pos H]
    · simp only [L4.iidHitCost,L4.Height.iidHitCost,if_neg H]
      congr 1
      exact FiniteUniformStoppingTree.ofFn_sum_eq _ _ (fun e=>ih (step x e))

/-- The literal six-bit sheet of the production row reaches a permanent
maximal independent set from all Cartesian starts in a quadratic IID mean. -/
theorem raw_h1_maximal_expected {s n : Nat} (N : 5≤n) (x : Raw s n) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) rawMaximal x ((2+2*6^9)*n^2) := by
  rw [Nat.add_mul]
  apply L4.AllSizeComposition.additive_stage (rawNext s)
    (L4.Height.TwoActualCovers (rawNext s) x) rawMaximal _ _ x
    (fun t => by rw [height_cost]; exact L4.Height.two_full_covers_expected (rawNext s) (by omega) x t)
  intro y H t
  obtain ⟨l,len,full,last⟩ := H
  cases l with
  | nil => cases len
  | cons a l =>
    cases l with
    | nil => cases len
    | cons b l =>
      cases l with
      | nil =>
        have exactY : rawRun x (a++b)=y := by
          rw [raw_runWord] at last
          simpa only [List.flatten_cons,List.flatten_nil,List.append_nil] using last
        have A : Authenticated (projection y) := by
          rw [←exactY]
          intro i
          exact raw_h1_covers (by omega) x a b (full a List.mem_cons_self)
            (full b (List.mem_cons_of_mem _ List.mem_cons_self)) i
        change L4.iidHitCost (rawNext s) (fun z => maximal (projection z)) t y ≤ _
        rw [physical_cost]
        exact maximal_after_auth_expected N (projection y)
          (fun j => (sep_ring N j).1) (fun j => (sep_ring N j).2) A t
      | cons c l =>
        simp only [List.length_cons] at len
        omega

theorem raw_h1_maximal_closed {s n : Nat} (N : 5≤n) (x : Raw s n) (e : Fin n)
    (H : rawMaximal x) : rawMaximal (rawNext s x e) := by
  have E : projection (rawNext s x e)=physicalStep (projection x) e :=
    funext (exact_physical_projection (rows s) x e)
  unfold rawMaximal
  rw [E]
  exact maximal_closed (projection x) e
    (fun j => (sep_ring N j).1) (fun j => (sep_ring N j).2) H

/-- Maximality fixes the particular selected set, not merely the
property of being some maximal independent set. -/
theorem raw_h1_selected_frozen {s n : Nat} (N : 5≤n) (x : Raw s n) (e i : Fin n)
    (H : rawMaximal x) :
    PhysicalMIS.selected (rawNext s x e i).physical=PhysicalMIS.selected (x i).physical := by
  let y := projection x
  let z := physicalStep y e
  have E : projection (rawNext s x e)=z := funext (exact_physical_projection (rows s) x e)
  change PhysicalMIS.selected (projection (rawNext s x e) i)=PhysicalMIS.selected (y i)
  rw [E]
  have M : maximal y := H
  have sep := fun j => (sep_ring N j).1
  have sepTwo := fun j => (sep_ring N j).2
  have K : maximal z := maximal_closed y e sep sepTwo M
  cases old : PhysicalMIS.selected (y i)
  · cases new : PhysicalMIS.selected (z i)
    · rfl
    · exfalso
      rcases M.2 i with L|C|R
      · let j := incoming i
        have J : rightNeighbor j=i := incoming_spec i
        have T : PhysicalMIS.selected (z j)=true := selected_persistent y e j sep M.1 L
        exact K.1.2 j j.isLt ⟨T,J.symm ▸ new⟩
      · exact Bool.noConfusion (old.symm.trans C)
      · have T : PhysicalMIS.selected (z (rightNeighbor i))=true :=
          selected_persistent y e _ sep M.1 R
        exact K.1.2 i i.isLt ⟨new,T⟩
  · exact selected_persistent y e i sep M.1 old

theorem raw_h1_selected_frozen_run {s n : Nat} (N : 5≤n) (x : Raw s n) (w : List (Fin n))
    (H : rawMaximal x) (i : Fin n) :
    PhysicalMIS.selected (rawRun x w i).physical=PhysicalMIS.selected (x i).physical := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih =>
    exact (ih (rawNext s x e) (raw_h1_maximal_closed N x e H)).trans
      (raw_h1_selected_frozen N x e i H)

end L4.PhysicalCustody.H1
