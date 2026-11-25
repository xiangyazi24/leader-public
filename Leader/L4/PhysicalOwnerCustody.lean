import Leader.L4.PhysicalOwnerStripGeometry
import Leader.L4.PhysicalOwnerAttempt
import Leader.L4.PhysicalCustodyEntrance

namespace L4.PhysicalOwnerCustody
open AllSizeProtocol BStarTrace PhysicalCustody BStarLongWork BStarLongClaims
open BStarH6WordChart BStarH6Ordinal BStarAcquireLiteralChain BStarAcquireVisitOrder
open BStarResetChartTouch BStarFenceLineGeometry BStarClearanceOffset BStarOwnerRecoveryPass
open PhysicalOwnerAttempt PhysicalOwnerStripGeometry
local notation "hp" => (show 0<2 by decide)

/-- A closed integer coefficient, independent of advice and ring size. -/
def ownerCoefficient : Nat := 729*(104394*1024+834)

theorem attempt_width_bound (n W len : Nat) (H : 2*len+1≤22*W) :
    attemptCost n W len ≤ 104394*(n*W)+834*n := by
  have R := Nat.mul_le_mul_left n H
  simp only [Nat.mul_comm n 22,←Nat.mul_assoc] at R
  rw [Nat.mul_assoc 22 n W] at R
  have E : attemptCost n W len = 104328*(n*W)+834*n+3*(n*(2*len+1)) := by
    unfold attemptCost
    simp only [Nat.mul_add,Nat.mul_assoc]
    omega
  omega

theorem owner_width_bound (n w len : Nat) (hw : 0<w) (H : 2*len+1≤22*(1024*w)) :
    729*attemptCost n (1024*w) len ≤ ownerCoefficient*n*w := by
  have h := attempt_width_bound n (1024*w) len H
  have W : 834*n≤834*(n*w) := by
    exact Nat.mul_le_mul_left 834 (Nat.le_mul_of_pos_right n hw)
  have h' : attemptCost n (1024*w) len ≤ (104394*1024+834)*(n*w) := by
    rw [show n*(1024*w)=1024*(n*w) by ac_rfl] at h
    simp only [Nat.add_mul,Nat.mul_assoc]
    omega
  calc
    _ ≤ 729*((104394*1024+834)*(n*w)) := Nat.mul_le_mul_left _ h'
    _ = _ := by unfold ownerCoefficient; ac_rfl

/-- Producer: all settled production charts and every admissible
raw upper state, with the exact commuted firstCredit tape goal. -/
theorem owner_credit_uniform {s n : Nat} (hs : 2≤s) (prod : 3*1024*radWidth s<n)
    (base : Raw s n) (g : ReadyAfterCovers base)
    (stable : ∀ y, g.Q y→correct (oldH6 (rows s) base) g.hh 5 y ∧ ∀ i,GrantClean y i)
    (o : Owners (oldH6 (rows s) base)) (x : Raw s n) (hx : g.Q x) :
    L4.IIDExpectedHittingTimeAtMost extendTape
      (firstCredit (HoldsCredit (Recovered hp base g.hh)) o x) [] (ownerCoefficient*n*radWidth s) := by
  have w2 : 2≤radWidth s := by
    unfold radWidth
    have H := Nat.pow_le_pow_right (by decide : (0:Nat)<2) hs
    omega
  have W : radWidth s≤1024*radWidth s := by omega
  obtain ⟨S,len,fall,l,d,chart,LF,RF,dp,seam,hl,lc,rc,lenB⟩ := strips_of_production g hs prod o
  apply TripleRenewal.expected_mono ?_ (owner_width_bound n (radWidth s) len (by omega) lenB)
  exact owner_credit_expected chart g.sep g.Q hx g.fiber (fun y h e=>g.closed y e h)
    LF RF dp seam g.flags g.notShort (by omega) hl lc rc g.head g.cont g.offset
    (fun y hy=>(stable y hy).1) (1024*radWidth s) W g.upperWidth (by omega)

private theorem adjacent_separation {n : Nat} (h : 2≤n) (e : Fin n) : e≠rightNeighbor e := by
  intro E
  have V := congrArg Fin.val E
  change e.val=(e.val+1)%n at V
  by_cases L : e.val+1<n
  · rw [Nat.mod_eq_of_lt L] at V
    omega
  · rw [show e.val+1=n by omega,Nat.mod_self] at V
    omega

/-- Only the independent packed entrance remains. No local owner trial or
post-cover grant assumptions are exposed in the resulting interface. -/
theorem custody_reached_of_geometry {s n : Nat} (hs : 2≤s)
    (prod : 3*1024*radWidth s<n)
    (settled : Raw s n→Prop) (Kgeom : Nat)
    (geometryMean : ∀ x, L4.IIDExpectedHittingTimeAtMost (rawNext s) settled x (Kgeom*n^2))
    (packedFiber : ∀ x, settled x→Nonempty (PackedFiber x)) (x : Raw s n) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) Custody x ((Kgeom+5+2*ownerCoefficient)*n^2) := by
  have w2 : 2≤radWidth s := by
    unfold radWidth
    have H := Nat.pow_le_pow_right (by decide : (0:Nat)<2) hs
    omega
  exact custody_reached_of_geometry_and_owner (adjacent_separation (by omega)) settled Kgeom
    ownerCoefficient geometryMean packedFiber (owner_credit_uniform hs prod) x

end L4.PhysicalOwnerCustody
