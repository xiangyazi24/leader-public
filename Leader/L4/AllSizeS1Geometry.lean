import Leader.L4.AllSizeProtocol
import Leader.L4.AllSizeComposition

namespace L4.AllSizeS1Geometry
open AllSizeProtocol

def step {a : LargeParams} {n : Nat} (b : LargeRows a)
    (x : Fin n → LargeSite a) (e : Fin n) : Fin n → LargeSite a :=
  let r := rightNeighbor e
  let p := largePair b (x e,x r)
  fun i => if i=e then p.1 else if i=r then p.2 else x i

def physicalStep {n : Nat} (x : Fin n → BitVec 6) (e : Fin n) : Fin n → BitVec 6 :=
  let r := rightNeighbor e
  let p := PhysicalMIS.next (x e,x r)
  fun i => if i=e then p.1 else if i=r then p.2 else x i

theorem exact_physical_projection {a : LargeParams} {n : Nat} (b : LargeRows a)
    (x : Fin n → LargeSite a) (e i : Fin n) :
    (step b x e i).physical=physicalStep (fun q => (x q).physical) e i := by
  unfold step physicalStep
  split
  · rfl
  · split <;> rfl

def header {a : LargeParams} (x : LargeSite a) := PhysicalMIS.selected x.physical
def off {a : LargeParams} (x : LargeSite a) := (ShortGeo.mis.off.read x.mis1).toNat
def successor {a : LargeParams} (x : LargeSite a) := ShortGeo.mis.successor.read x.mis1

theorem refresh {a : LargeParams} {n : Nat} (b : LargeRows a)
    (x : Fin n→LargeSite a) (e : Fin n) (he : rightNeighbor e≠e) :
    successor (step b x e e)=BitVec.ofNat 1 (header (x (rightNeighbor e))).toNat ∧
    off (step b x e (rightNeighbor e))=
      (if header (x (rightNeighbor e)) then 0 else
        min 3 ((if header (x e) then 0 else min 3 (off (x e)))+1)) ∧
    off (step b x e e)=off (x e) ∧
    successor (step b x e (rightNeighbor e))=successor (x (rightNeighbor e)) := by
  have hg := (largePair_short_geometry b (x e,x (rightNeighbor e))).1
  change ShortGeo.mis.Refresh 3 (header (x e),header (x (rightNeighbor e)))
    ((x e).mis1,(x (rightNeighbor e)).mis1)
    ((largePair b (x e,x (rightNeighbor e))).1.mis1,(largePair b (x e,x (rightNeighbor e))).2.mis1) at hg
  obtain ⟨h0,h1,h2,h3⟩ := hg
  simp only [step,if_true,if_neg he]
  refine ⟨h0,?_,congrArg BitVec.toNat h2,h3⟩
  have H := congrArg BitVec.toNat h1
  rw [ShortGeo.nextOff_nat _ _ _ _ (by decide)] at H
  exact H

/-- If the lower physical header layout is fixed, the stored
saturated offsets and successor cache are closed. No short work
provider, fairness assumption or canonical raw bytes are needed. -/
theorem geo_closed_at_fixed_headers {a : LargeParams} {n : Nat} (b : LargeRows a)
    (x : Fin n→LargeSite a) (e : Fin n) (he : rightNeighbor e≠e)
    (d : Fin n→Nat) (bd : ∀ i, d i≤3)
    (frozen : ∀ i, header (step b x e i)=header (x i))
    (atHeads : ∀ i, header (x i)=true → d i=0)
    (offsetEq : ∀ i, d (rightNeighbor i)=
      if header (x (rightNeighbor i)) then 0 else min 3 (d i+1))
    (old : ∀ i, off (x i)=d i ∧
      successor (x i)=BitVec.ofNat 1 (header (x (rightNeighbor i))).toNat) :
    ∀ i, off (step b x e i)=d i ∧
      successor (step b x e i)=BitVec.ofNat 1 (header (step b x e (rightNeighbor i))).toNat := by
  intro i
  rw [frozen]
  obtain ⟨hC,hOff,hL,hR⟩ := refresh b x e he
  by_cases hi : i=e
  · subst i
    exact ⟨hL.trans (old e).1,hC⟩
  · by_cases hI : i=rightNeighbor e
    · subst i
      refine ⟨?_,hR.trans (old _).2⟩
      rw [hOff,(old e).1,offsetEq e]
      have eq : (if header (x e) then 0 else min 3 (d e))=d e := by
        cases h : header (x e) with
        | false => simp [Nat.min_eq_right (bd e)]
        | true => simpa using (atHeads e h).symm
      rw [eq]
    · simpa only [step,hi,hI,if_false] using old i

end L4.AllSizeS1Geometry
