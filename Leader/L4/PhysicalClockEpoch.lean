import Leader.L4.BStarEpochLift
import Leader.L4.BStarCycleGeometry
import Leader.L4.Height.ServiceCustody
import Leader.L4.ClockCycleExtrema

namespace L4.PhysicalClockEpoch
open AllSizeProtocol BStarTrace PhysicalCustody BStarCycleGeometry BStarAcquireAnchors
open BStarH6WordChart BStarCustodyCuts BStarPhysicalLegitimate BStarPhysicalCoset
open BStarPhysicalLiftAlignment BStarEpochLift BStarPhysicalIncrementLedger BStarIncrementLedger
open L4.Compiler.Native BStarNativePortGeometry

local notation "hp" => (show 0<2 by decide)

private theorem count_start_eq {n : Nat} (a b : Fin n → Nat) (mark : Nat→Option (Fin n))
    (i : Fin n) (same : a i=b i) (t : Nat) : count a mark i t=count b mark i t := by
  induction t with
  | zero => exact same
  | succ t ih => rw [count,count,ih]

private theorem count_no_mark {n : Nat} (a : Fin n → Nat) (mark : Nat→Option (Fin n))
    (i : Fin n) (absent : ∀ t,mark t≠some i) (t : Nat) : count a mark i t=a i := by
  induction t with
  | zero => rfl
  | succ t ih => rw [count,ih,if_neg (absent t),Nat.add_zero]

variable {s n : Nat} {x : Raw s n} (g : CustodyWitness x)
local notation "HS" => oldH6 (rows s) g.base
local notation "hist" => ((g.u++g.v)++g.past)
local notation "ticks" => traceCount hp g.base g.initial g.hh

private theorem inc_header {y : Raw s n} {e i : Fin n}
    (hit : incAt hp g.base g.hh y e=some i) : HS i=true := by
  have eq := incAt_value hp g.hh e i hit
  subst i
  unfold incAt at hit
  split at hit
  · assumption
  · contradiction

private theorem off_header_no_tape_inc (w : List (Fin n)) (i : Fin n)
    (off : HS i≠true) (t : Nat) :
    tapeInc hp g.base g.hh g.initial w t≠some i := by
  intro hit
  unfold tapeInc at hit
  split at hit
  · exact off (inc_header g hit)
  · contradiction

/-- Normalize only the off-header starts. The archived coset replay
on the original tape changes at no actual owner or prefix. -/
theorem epoch_with_extrema
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (hr : 3≤radWidth s) (P : Nat) (M : modulus (radWidth s)=2*P)
    (small : total HS<P) (phase : 32∣P)
    (legit : ClockLegit hp g.base g.hh x) :
    ∃ start : Fin n→Nat, ∃ lo G opening cap : Nat,
      opening=frontier G ∧ cap=opening+32*(2^19*total HS) ∧
      G≤lo+total HS/2 ∧ cap+1≤lo+(total HS/2+35+32*(2^19*total HS)) ∧
      (∀ w : List (Fin n),
        RepresentsCoset hp g.base (rawRun g.initial (hist++w)) P (ticks start (hist++w)) ∧
        Coherent g.hh (ticks start (hist++w))) ∧
      (∀ i : Header HS,lo≤ticks start hist i.val) ∧
      (∀ i : Fin n,ticks start hist i≤G) ∧
      (∃ i : Header HS,ticks start hist i.val=lo) ∧
      (∃ i : Header HS,ticks start hist i.val=G) ∧
      (∀ i : Fin n, HS i≠true → ∀ w : List (Fin n), ticks start w i=0) := by
  classical
  have L : ClockLegit hp g.base g.hh (rawRun g.initial hist) := g.here.symm ▸ legit
  obtain ⟨start,H⟩ := epoch_coset_replay hp g.u g.v g.past g.cuts g.hh sep g.Q
    g.init g.fiber g.closed hr g.flags g.notShort P M small phase L
  let new := fun i => if HS i=true then start i else 0
  have keep (w : List (Fin n)) (i : Header HS) : ticks new w i.val=ticks start w i.val := by
    exact count_start_eq _ _ _ _ (if_pos i.property) _
  have rep (w : List (Fin n)) :
      RepresentsCoset hp g.base (rawRun g.initial (hist++w)) P (ticks new (hist++w)) ∧
      Coherent g.hh (ticks new (hist++w)) := by
    obtain ⟨A,B⟩ := (show RepresentsCoset hp g.base (rawRun g.initial (hist++w)) P
      (ticks start (hist++w)) ∧ Coherent g.hh (ticks start (hist++w)) from by
        simpa only [List.append_assoc,rawRun,rawNext,rows] using H w)
    constructor
    · intro i
      rw [keep (hist++w) i]
      exact A i
    · intro i q
      rw [keep (hist++w) i,keep (hist++w) (neighborHeader g.hh i q)]
      exact B i q
  have zero (i : Fin n) (off : HS i≠true) (w : List (Fin n)) : ticks new w i=0 := by
    exact (count_no_mark _ _ _ (off_header_no_tape_inc g w i off) _).trans (if_neg off)
  let f := fun j : Fin (total HS) => ticks new hist (atIndex g.hh j).val
  have near (j : Fin (total HS)) : ClockCycleExtrema.Near (f j)
      (f ⟨(j.val+1)%total HS,Nat.mod_lt _ (Nat.zero_lt_of_lt j.isLt)⟩) := by
    change ClockCycleExtrema.Near (f j) (f (BStarCycleGeometry.next j))
    unfold f
    rw [atIndex_next]
    have A := (rep []).2 (atIndex g.hh j) 2
    simpa only [List.append_nil,ClockCycleExtrema.Near] using A
  obtain ⟨i,j,E⟩ := ClockCycleExtrema.exists_extrema (total_pos HS g.hh) f
  let lo := f i
  let G := f j
  let opening := frontier G
  let cap := opening+32*(2^19*total HS)
  have span : G≤lo+total HS/2 := ClockCycleExtrema.span f near i j
  have depth : cap+1≤lo+(total HS/2+35+32*(2^19*total HS)) := by
    have O := (frontier_spec G).2.1
    dsimp only [cap,opening]
    omega
  refine ⟨new,lo,G,opening,cap,rfl,rfl,span,depth,rep,?_,?_,?_,?_,zero⟩
  · intro a
    have T := (E (index g.hh a)).1
    unfold f at T
    rwa [atIndex_index] at T
  · intro a
    by_cases ha : HS a=true
    · have T := (E (index g.hh ⟨a,ha⟩)).2
      unfold f at T
      rwa [atIndex_index] at T
    · rw [zero a ha]; exact Nat.zero_le _
  · exact ⟨atIndex g.hh i,rfl⟩
  · exact ⟨atIndex g.hh j,rfl⟩

#print axioms epoch_with_extrema
end L4.PhysicalClockEpoch
