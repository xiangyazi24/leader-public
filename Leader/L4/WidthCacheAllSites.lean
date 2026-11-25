import Leader.L4.ReportCacheAllSites

namespace L4.WidthCacheAllSites
open AllSizeProtocol BStarH6WordChart BStarH6Ordinal PhysicalCustody
open ReportCacheWindow ReportCacheAllSites

section Literal
variable {n : Nat} {a : LargeParams}

abbrev widthOff (x : Fin n → LargeSite a) (i : Fin n) : Nat :=
  ((ShortGeo.width a.c).off.read (x i).widthClient).toNat

abbrev widthSucc (x : Fin n → LargeSite a) (i : Fin n) : Bool :=
  ((ShortGeo.width a.c).successor.read (x i).widthClient).getLsbD 0

abbrev WidthCorrect (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (Q : (Fin n → LargeSite a) → Prop) (x : Fin n → LargeSite a) : Prop :=
  AllCorrect Q h hh a.c widthOff widthSucc x

/-- Use the literal joined Width cache writer and the old H6 mask.
No assertion about the Width threshold, request, or output bits. -/
theorem width_frame (b : LargeRows a) (h : Fin n → Bool)
    (Q : (Fin n → LargeSite a) → Prop)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (closed : ∀ x e,Q x→Q (AllSizeS1Geometry.step b x e))
    (mask : ∀ x,Q x→∀ i,(oldHeaders b (x i)).h6=h i) :
    Frame (AllSizeS1Geometry.step b) Q h a.c widthOff widthSucc := by
  let G := ShortGeo.width a.c
  let read := LargeSite.widthClient (a:=a)
  have R (x : Fin n → LargeSite a) (e : Fin n) (A : Q x) :
      let r := rightNeighbor e
      let y := AllSizeS1Geometry.step b x e
      G.Refresh a.c (h e,h r) (read (x e),read (x r)) (read (y e),read (y r)) := by
    dsimp only
    have f := (largePair_short_geometry b (x e,x (rightNeighbor e))).2.2.2.2.2
    change G.Refresh a.c ((oldHeaders b (x e)).h6,(oldHeaders b (x (rightNeighbor e))).h6)
      (read (x e),read (x (rightNeighbor e)))
      (read (largePair b (x e,x (rightNeighbor e))).1,
        read (largePair b (x e,x (rightNeighbor e))).2) at f
    rw [mask x A e,mask x A (rightNeighbor e)] at f
    simpa only [AllSizeS1Geometry.step,if_true,if_pos rfl,if_neg (Ne.symm (sep e))] using f
  refine ⟨closed,?_,?_,?_,?_⟩
  · intro x e A
    have E := congrArg BitVec.toNat (R x e A).2.1
    rw [G.nextOff_nat _ _ _ (ShortGeo.ell_cap a.c)] at E
    exact E
  · intro x e i A I
    by_cases E : i=e
    · subst i
      exact congrArg BitVec.toNat (R x e A).2.2.1
    · simp only [widthOff,AllSizeS1Geometry.step,if_neg E,if_neg I]
  · intro x e A
    have E := congrArg (fun b : BitVec 1=>b.getLsbD 0) (R x e A).1
    cases T : h (rightNeighbor e)
    · simpa [ShortGeo.nextSuccessor,T] using E
    · simpa [ShortGeo.nextSuccessor,T] using E
  · intro x e i A I
    by_cases E : i=rightNeighbor e
    · subst i
      exact congrArg (fun b : BitVec 1=>b.getLsbD 0) (R x e A).2.2.2
    · simp only [widthSucc,AllSizeS1Geometry.step,if_neg I,if_neg E]

theorem width_all_sites (b : LargeRows a) (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (Q : (Fin n → LargeSite a) → Prop) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (closed : ∀ x e,Q x→Q (AllSizeS1Geometry.step b x e))
    (mask : ∀ x,Q x→∀ i,(oldHeaders b (x i)).h6=h i) (C : 0<a.c)
    (x : Fin n → LargeSite a) (A : Q x) :
    (∀ y e, WidthCorrect h hh Q y → WidthCorrect h hh Q (AllSizeS1Geometry.step b y e)) ∧
    Height.IIDExpectedHittingTimeAtMost (AllSizeS1Geometry.step b) (WidthCorrect h hh Q) x
      ((a.c+1)*n^2) := by
  have F := width_frame b h Q sep closed mask
  exact ⟨all_closed hh F,all_expected hh F C x A⟩

end Literal

/-- The actual production Width cap is s+11. Frozen H6 is supplied
on a closed raw domain and the sampler stays on all physical marks. -/
theorem width_raw {s n : Nat} (N : 1<n) (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (Q : Raw s n → Prop) (closed : ∀ x e,Q x→Q (rawNext s x e))
    (mask : ∀ x,Q x→∀ i,oldH6 (rows s) x i=h i)
    (x : Raw s n) (A : Q x) :
    (∀ y e, WidthCorrect h hh Q y → WidthCorrect h hh Q (rawNext s y e)) ∧
    Height.IIDExpectedHittingTimeAtMost (rawNext s) (WidthCorrect h hh Q) x ((s+12)*n^2) := by
  exact width_all_sites (rows s) h hh Q (ShortResetCycle.edge_sep N) closed mask
    (by change 0<s+11; omega) x A

theorem width_raw_fields {s n : Nat} (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (Q : Raw s n → Prop) (x : Raw s n) (A : WidthCorrect h hh Q x) (i : Fin n) :
    widthOff x i = min (s+11) (ordinal h hh i) ∧ widthSucc x i=h (rightNeighbor i) :=
  raw_fields_correct hh (by omega : 0<s+11) x A i

#print axioms width_frame
#print axioms width_all_sites
#print axioms width_raw
#print axioms width_raw_fields
end L4.WidthCacheAllSites
